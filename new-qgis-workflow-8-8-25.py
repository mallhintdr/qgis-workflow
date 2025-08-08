import os
import glob
import time
import math
import concurrent.futures
import gc

from PyQt5.QtWidgets import QApplication, QFileDialog
from PyQt5.QtCore import QVariant
from qgis.core import (
    QgsVectorLayer,
    QgsProject,
    QgsProcessingFeedback,
    QgsFeature,
    QgsWkbTypes,
    QgsGeometry,
    QgsField,
    QgsCoordinateReferenceSystem,
    QgsCoordinateTransform,
    edit,
)
import processing
from PIL import Image, ImageChops

# -------------------- CONFIGURATION ----------------------
JOB_LIST_FILENAME = "geojson_jobs.txt"
LOCK_FILENAME = "geojson_jobs.lock"
JOB_STATUS_PENDING = "PENDING"
JOB_STATUS_IN_PROGRESS = "IN_PROGRESS"
JOB_STATUS_DONE = "DONE"

# Tiles / rendering
ZOOM_MIN = 10
ZOOM_MAX = 20
TILE_WIDTH = 256
TILE_HEIGHT = 256
DPI = 96
BACKGROUND_COLOR = "rgba(0, 0, 0, 0)"   # transparent
TILE_FORMAT = 0                         # 0=PNG, 1=JPG
METATILESIZE = 8                        # was 16
ANTIALIAS = False                       # big speed win

# Blank tile cleanup
BLANK_TILE_SIZE_BYTES = 1800            # quick size gate for transparent PNGs
CLEANUP_THREAD_MULTIPLIER = 4
CLEANUP_CHUNK = 5000

# GC cadence
GC_EVERY_JOBS = 5

class MinimalFeedback(QgsProcessingFeedback):
    def pushInfo(self, info): pass
    def setProgressText(self, text): pass
    def setProgress(self, progress): pass

# -------------------- UI / JOB QUEUE ----------------------
def select_main_folder():
    app = QApplication.instance()
    if app is None:
        app = QApplication([])
    folder = QFileDialog.getExistingDirectory(None, "Select Folder with GeoJSON Files", os.path.expanduser("~"))
    return folder

def build_job_list(main_folder):
    job_list_path = os.path.join(main_folder, JOB_LIST_FILENAME)
    if os.path.exists(job_list_path):
        return
    files = glob.glob(os.path.join(main_folder, "*.geojson"))
    with open(job_list_path, "w", encoding="utf-8") as f:
        for file in files:
            f.write(f"{os.path.basename(file)},{JOB_STATUS_PENDING}\n")

def atomic_lock(folder, timeout=30):
    lock_path = os.path.join(folder, LOCK_FILENAME)
    waited = 0
    while True:
        try:
            fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.close(fd)
            return lock_path
        except FileExistsError:
            time.sleep(0.25)
            waited += 0.25
            if waited >= timeout:
                raise Exception("Timeout waiting for job file lock.")

def atomic_unlock(lock_path):
    try:
        os.remove(lock_path)
    except Exception:
        pass

def claim_next_job(main_folder):
    job_list_path = os.path.join(main_folder, JOB_LIST_FILENAME)
    lock_path = atomic_lock(main_folder)
    claimed_file = None
    with open(job_list_path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    new_lines = []
    for line in lines:
        fn, status = line.strip().split(",", 1)
        if status == JOB_STATUS_PENDING and claimed_file is None:
            new_lines.append(f"{fn},{JOB_STATUS_IN_PROGRESS}\n")
            claimed_file = fn
        else:
            new_lines.append(line)
    with open(job_list_path, "w", encoding="utf-8") as f:
        f.writelines(new_lines)
    atomic_unlock(lock_path)
    return os.path.join(main_folder, claimed_file) if claimed_file else None

def mark_job_done(main_folder, filename):
    job_list_path = os.path.join(main_folder, JOB_LIST_FILENAME)
    lock_path = atomic_lock(main_folder)
    with open(job_list_path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    new_lines = []
    for line in lines:
        fn, status = line.strip().split(",", 1)
        if fn == os.path.basename(filename):
            new_lines.append(f"{fn},{JOB_STATUS_DONE}\n")
        else:
            new_lines.append(line)
    with open(job_list_path, "w", encoding="utf-8") as f:
        f.writelines(new_lines)
    atomic_unlock(lock_path)

def check_all_done(main_folder):
    job_list_path = os.path.join(main_folder, JOB_LIST_FILENAME)
    if not os.path.exists(job_list_path):
        return True
    with open(job_list_path, "r", encoding="utf-8") as f:
        for line in f:
            fn, status = line.strip().split(",", 1)
            if status != JOB_STATUS_DONE:
                return False
    return True

# -------------------- MATH / CRS HELPERS ----------------------
def _lat_to_tile_y(lat, zoom):
    rad = math.radians(lat)
    return math.floor((1 - math.log(math.tan(rad) + 1 / math.cos(rad)) / math.pi) / 2 * (2 ** zoom))

def compute_total_tiles_wgs84(xmin, xmax, ymin, ymax, zoom_min, zoom_max):
    total = 0
    for z in range(zoom_min, zoom_max + 1):
        txmin = math.floor((xmin + 180) / 360 * (2 ** z))
        txmax = math.floor((xmax + 180) / 360 * (2 ** z))
        tymin = _lat_to_tile_y(ymax, z)
        tymax = _lat_to_tile_y(ymin, z)
        total += (txmax - txmin + 1) * (tymax - tymin + 1)
    return total

def layer_extent_wgs84(layer):
    src = layer.crs()
    dst = QgsCoordinateReferenceSystem("EPSG:4326")
    tr = QgsCoordinateTransform(src, dst, QgsProject.instance())
    e = layer.extent()
    sw = tr.transform(e.xMinimum(), e.yMinimum())
    ne = tr.transform(e.xMaximum(), e.yMaximum())
    xmin, ymin = min(sw.x(), ne.x()), min(sw.y(), ne.y())
    xmax, ymax = max(sw.x(), ne.x()), max(sw.y(), ne.y())
    return xmin, xmax, ymin, ymax

# -------------------- CLEANERS ----------------------
def clean_outline_layer_batch(layer):
    """Exterior rings only + batch geometry update (no per-feature edit blocks)."""
    prov = layer.dataProvider()
    changes = {}
    for feat in layer.getFeatures():
        g = feat.geometry()
        if not g or g.isEmpty():
            continue
        if not g.isGeosValid():
            g = g.makeValid()

        if g.isMultipart():
            parts = g.asMultiPolygon()
            exteriors = []
            for poly in parts or []:
                if poly and len(poly) > 0:
                    exteriors.append([poly[0]])
            if exteriors:
                changes[feat.id()] = QgsGeometry.fromMultiPolygonXY(exteriors)
        else:
            poly = g.asPolygon()
            if poly and len(poly) > 0:
                changes[feat.id()] = QgsGeometry.fromPolygonXY([poly[0]])

    if changes:
        prov.changeGeometryValues(changes)

    # Remove contained boundaries within same group_key (fast BB-first)
    feats = list(layer.getFeatures())
    by_group = {}
    for f in feats:
        by_group.setdefault(f["group_key"], []).append(f)

    remove_ids = set()
    for gk, arr in by_group.items():
        # Sort small→large so we mark small ones quickly
        arr = sorted(arr, key=lambda f: f.geometry().area())
        for i, f_small in enumerate(arr):
            gs = f_small.geometry()
            if gs is None:
                continue
            bb_s = gs.boundingBox()
            for f_big in arr[i+1:]:
                gb = f_big.geometry()
                if gb is None:
                    continue
                if not gb.boundingBox().contains(bb_s):
                    continue
                if gb.contains(gs):
                    remove_ids.add(f_small.id())
                    break

    if remove_ids:
        with edit(layer):
            for fid in remove_ids:
                layer.deleteFeature(fid)
        return f"Removed {len(remove_ids)} contained boundaries."
    return "No contained boundaries removed."

def is_blank_tile(tile_path):
    try:
        if os.path.getsize(tile_path) > BLANK_TILE_SIZE_BYTES:
            return False
    except Exception:
        return False
    try:
        with Image.open(tile_path) as img:
            rgba_img = img.convert("RGBA")
            blank = Image.new("RGBA", rgba_img.size, (0, 0, 0, 0))
            diff = ImageChops.difference(rgba_img, blank)
            return diff.getbbox() is None
    except Exception:
        return False

def clean_tiles(directory, prefix=""):
    pngs = []
    for root, _, files in os.walk(directory):
        for fn in files:
            if fn.lower().endswith(".png"):
                pngs.append(os.path.join(root, fn))
    if not pngs:
        print(f"{prefix}No PNG tiles found to process.")
        return

    print(f"{prefix}Tile cleanup started: {len(pngs)} PNG files found.")
    max_workers = min(64, (os.cpu_count() or 1) * CLEANUP_THREAD_MULTIPLIER)
    removed = 0

    def process_tile(p):
        try:
            if is_blank_tile(p):
                os.remove(p)
                return 1
        except Exception:
            return 0
        return 0

    for i in range(0, len(pngs), CLEANUP_CHUNK):
        batch = pngs[i:i + CLEANUP_CHUNK]
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as ex:
            for r in ex.map(process_tile, batch):
                removed += (r or 0)

    print(f"{prefix}Tile cleanup done. {removed} blank tiles deleted.")

# -------------------- GROUP KEY ----------------------
def get_group_key(feat):
    def safe_val(field):
        return feat[field] if field in feat.fields().names() else None

    t = str(safe_val("Type")).strip() if safe_val("Type") is not None else ""
    m_val = safe_val("M")
    mn_val = safe_val("MN")
    b_val = safe_val("B")
    k_val = safe_val("K")

    def norm(x):
        if x in [None, "", "None"]:
            return None
        try:
            if isinstance(x, str) and x.isdigit():
                return int(x)
            return x
        except Exception:
            return x

    m_norm = norm(m_val)
    mn_norm = norm(mn_val)
    b_norm = norm(b_val)
    k_norm = norm(k_val)

    if t == "MT":
        if (m_norm in [None, 0]) and (mn_norm in [None, 0]):
            return "0"
        if m_norm not in [None, 0] and mn_norm in [None, 0]:
            return str(m_norm)
        if mn_norm not in [None, 0] and m_norm in [None, 0]:
            return str(mn_norm)
        if (m_norm is not None and mn_norm is not None) and (m_norm == mn_norm):
            return str(m_norm)
        if mn_norm not in [None, 0]:
            if b_norm in [None, "", "None", 0, "0"]:
                return str(mn_norm)
            else:
                return f"{b_norm}/{mn_norm}"
        if m_norm not in [None, 0]:
            return str(m_norm)
        return "0"
    elif t in ("MU", "MU/MT", "MT/MU", "MU/KW", "KW"):
        if m_norm not in [None, 0]:
            return str(m_norm)
    elif t == "K":
        if k_norm not in [None, 0]:
            return str(k_norm)
    if m_norm not in [None, 0]:
        return str(m_norm)
    return "0"

# -------------------- MAIN JOB ----------------------
def process_geojson(geojson_file):
    try:
        base_name = os.path.splitext(os.path.basename(geojson_file))[0]
        print(f"Processing: {base_name}")

        # Load source
        src_layer = QgsVectorLayer(geojson_file, base_name, "ogr")
        if not src_layer.isValid():
            print("Layer failed to load. Skipping.")
            return

        # Build memory layer with group_key in one pass
        geom_type = QgsWkbTypes.displayString(src_layer.wkbType()).lower()
        crs_authid = src_layer.crs().authid()
        mem_layer = QgsVectorLayer(f"{geom_type}?crs={crs_authid}", base_name, "memory")
        prov = mem_layer.dataProvider()

        fields = src_layer.fields()
        if "group_key" not in fields.names():
            fields.append(QgsField("group_key", QVariant.String))
        prov.addAttributes(fields)
        mem_layer.updateFields()

        gk_idx = mem_layer.fields().indexFromName("group_key")
        new_feats = []
        for feat in src_layer.getFeatures():
            geom = feat.geometry()
            if geom and not geom.isGeosValid():
                geom = geom.makeValid()
            nf = QgsFeature(mem_layer.fields())
            nf.setGeometry(geom)
            attrs = list(feat.attributes())
            if len(attrs) < mem_layer.fields().count():
                attrs += [None] * (mem_layer.fields().count() - len(attrs))
            attrs[gk_idx] = get_group_key(feat)
            nf.setAttributes(attrs)
            new_feats.append(nf)
        prov.addFeatures(new_feats)
        mem_layer.updateExtents()
        print("Memory layer created.")

            # Add to project ONLY because some QGIS versions need project layers for native:tilesxyzdirectory
            QgsProject.instance().addMapLayer(mem_layer)
            try:
                tile_style_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tile_style.qml")
                if os.path.exists(tile_style_path):
                    mem_layer.loadNamedStyle(tile_style_path)
            except Exception:
                pass
            mem_layer.setLabelsEnabled(True)  # labels required

            # Dissolve -> multipart to single -> exterior rings -> label
            if mem_layer.fields().indexFromName("group_key") == -1:
                print("group_key field missing; skipping dissolve.")
                return

            dissolved = processing.run(
                "native:dissolve",
                {"INPUT": mem_layer, "FIELD": ["group_key"], "OUTPUT": "memory:"},
                feedback=MinimalFeedback()
            )["OUTPUT"]

            outline_layer = processing.run(
                "native:multiparttosingleparts",
                {"INPUT": dissolved, "OUTPUT": "memory:"},
                feedback=MinimalFeedback()
            )["OUTPUT"]

            clean_msg = clean_outline_layer_batch(outline_layer)
            print(f"Outline cleaned. {clean_msg}")
            QgsProject.instance().addMapLayer(outline_layer)
            try:
                murabb_style_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "murabb_style.qml")
                if os.path.exists(murabb_style_path):
                    outline_layer.loadNamedStyle(murabb_style_path)
            except Exception:
                pass
            outline_layer.setLabelsEnabled(True)  # labels required

            # Extent in WGS84 for math + export
            xmin, xmax, ymin, ymax = layer_extent_wgs84(outline_layer)
            tiles_est = compute_total_tiles_wgs84(xmin, xmax, ymin, ymax, ZOOM_MIN, ZOOM_MAX)
            print(f"Tiles to generate: {tiles_est}")

            output_dir = os.path.join(os.path.dirname(geojson_file), base_name)
            os.makedirs(output_dir, exist_ok=True)

            # Prefer qgis:tilesxyzdirectory (supports LAYERS). If not found, fall back to native (project layers).
            alg_id = "qgis:tilesxyzdirectory"
            have_qgis_alg = False
            try:
                processing.algorithmHelp(alg_id)
                have_qgis_alg = True
            except Exception:
                alg_id = "native:tilesxyzdirectory"

            params = {
                "EXTENT": f"{xmin},{xmax},{ymin},{ymax} [EPSG:4326]",
                "ZOOM_MIN": ZOOM_MIN,
                "ZOOM_MAX": ZOOM_MAX,
                "TILE_WIDTH": TILE_WIDTH,
                "TILE_HEIGHT": TILE_HEIGHT,
                "DPI": DPI,
                "BACKGROUND_COLOR": BACKGROUND_COLOR,
                "ANTIALIAS": ANTIALIAS,
                "TILE_FORMAT": TILE_FORMAT,
                "QUALITY": 90,
                "METATILESIZE": METATILESIZE,
                "TMS_CONVENTION": False,
                "OUTPUT_DIRECTORY": output_dir.replace("\\", "/"),
            }
            if have_qgis_alg:
                params["LAYERS"] = [mem_layer, outline_layer]

            try:
                processing.run(alg_id, params, feedback=MinimalFeedback())
                print(f"Tiles generated for '{base_name}'.")
                clean_tiles(output_dir, prefix=f"{base_name}: ")
            except Exception as e:
                print(f"Error generating tiles for {base_name}: {e}")

        except Exception as e:
            print(f"Error processing {geojson_file}: {e}")
        finally:
            # Clean the project to avoid GUI churn between jobs
            try:
                for l in list(QgsProject.instance().mapLayers().values()):
                    QgsProject.instance().removeMapLayer(l.id())
            except Exception:
                pass
            gc.collect()
            time.sleep(1)


# ========== MAIN LOOP ==========
def run():
    main_folder = select_main_folder()
    if not main_folder:
        print("No folder selected. Exiting.")
        return

    print(f"Selected folder: {main_folder}")
    build_job_list(main_folder)
    while not check_all_done(main_folder):
        geojson_file = claim_next_job(main_folder)
        if geojson_file is None:
            print("Waiting for jobs...")
            time.sleep(3)
            continue
        print(f"\nClaimed: {os.path.basename(geojson_file)}")
        process_geojson(geojson_file)
        mark_job_done(main_folder, geojson_file)

    print("All GeoJSON files processed.")


if __name__ in {"__main__", "__console__"}:
    run()


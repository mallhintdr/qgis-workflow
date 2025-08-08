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
    edit,
    QgsVectorLayerSimpleLabeling
)
import processing
from PIL import Image, ImageChops

# -------------------- CONFIGURATION ----------------------
JOB_LIST_FILENAME = "geojson_jobs.txt"
LOCK_FILENAME = "geojson_jobs.lock"
JOB_STATUS_PENDING = "PENDING"
JOB_STATUS_IN_PROGRESS = "IN_PROGRESS"
JOB_STATUS_DONE = "DONE"

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
                print("Timeout waiting for job file lock.")
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
    if claimed_file:
        return os.path.join(main_folder, claimed_file)
    else:
        return None

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

def compute_total_tiles(xmin, xmax, ymin, ymax, zoom_min, zoom_max):
    total = 0
    def lat_to_tile_y(lat, zoom):
        rad = math.radians(lat)
        return math.floor((1 - math.log(math.tan(rad) + 1/math.cos(rad)) / math.pi) / 2 * (2**zoom))
    for z in range(zoom_min, zoom_max + 1):
        tile_x_min = math.floor((xmin + 180) / 360 * (2**z))
        tile_x_max = math.floor((xmax + 180) / 360 * (2**z))
        tile_y_min = lat_to_tile_y(ymax, z)
        tile_y_max = lat_to_tile_y(ymin, z)
        count = (tile_x_max - tile_x_min + 1) * (tile_y_max - tile_y_min + 1)
        total += count
    return total

class MinimalFeedback(QgsProcessingFeedback):
    def pushInfo(self, info): pass
    def setProgressText(self, text): pass
    def setProgress(self, progress): pass

def clean_outline_layer(layer):
    features = list(layer.getFeatures())
    for feat in features:
        geom = feat.geometry()
        if not geom.isMultipart():
            poly = geom.asPolygon()
            if poly and len(poly) > 0:
                new_geom = QgsGeometry.fromPolygonXY([poly[0]])
                feat.setGeometry(new_geom)
                with edit(layer):
                    layer.changeGeometry(feat.id(), new_geom)
        else:
            multi = geom.asMultiPolygon()
            if multi:
                new_multi = []
                for poly in multi:
                    if poly and len(poly) > 0:
                        new_multi.append([poly[0]])
                new_geom = QgsGeometry.fromMultiPolygonXY(new_multi)
                feat.setGeometry(new_geom)
                with edit(layer):
                    layer.changeGeometry(feat.id(), new_geom)
    remove_ids = set()
    features = list(layer.getFeatures())
    for i, feat in enumerate(features):
        geom_i = feat.geometry()
        area_i = geom_i.area()
        for j, other in enumerate(features):
            if i == j:
                continue
            if feat["group_key"] != other["group_key"]:
                continue
            geom_j = other.geometry()
            area_j = geom_j.area()
            if geom_j.contains(geom_i) and area_j > area_i:
                remove_ids.add(feat.id())
                break
    if remove_ids:
        with edit(layer):
            for fid in remove_ids:
                layer.deleteFeature(fid)
        return "Removed contained boundaries."
    else:
        return "No contained boundaries removed."

def is_blank_tile(tile_path):
    try:
        with Image.open(tile_path) as img:
            rgba_img = img.convert("RGBA")
            blank = Image.new("RGBA", rgba_img.size, (0, 0, 0, 0))
            diff = ImageChops.difference(rgba_img, blank)
            return diff.getbbox() is None
    except Exception:
        return False

def process_tile(tile_path):
    try:
        if is_blank_tile(tile_path):
            os.remove(tile_path)
            return True
    except Exception:
        return False
    return False

def clean_tiles(directory, prefix=""):
    tile_paths = []
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.lower().endswith('.png'):
                tile_paths.append(os.path.join(root, file))
    total_tiles = len(tile_paths)
    if total_tiles == 0:
        print(f"{prefix}No PNG tiles found to process.")
        return
    print(f"{prefix}Tile cleanup started: {total_tiles} PNG files found.")
    removed_files = 0
    max_workers = min(64, os.cpu_count() * 4)
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(process_tile, tile_path) for tile_path in tile_paths]
        for future in concurrent.futures.as_completed(futures):
            try:
                if future.result():
                    removed_files += 1
            except Exception:
                pass
    print(f"{prefix}Tile cleanup done. {removed_files} blank tiles deleted.")

def get_group_key(feat):
    def safe_val(field):
        return feat[field] if field in feat.fields().names() else None

    t = str(safe_val("Type")).strip() if safe_val("Type") is not None else ""
    m_val = safe_val("M")
    mn_val = safe_val("MN")
    b_val = safe_val("B")
    k_val = safe_val("K")

    # Helper to normalize values
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
        # Both M and MN are blank/zero
        if (m_norm is None or m_norm == 0) and (mn_norm is None or mn_norm == 0):
            return "0"
        # Only one of M or MN has value, use that value
        if (m_norm is not None and m_norm != 0) and (mn_norm is None or mn_norm == 0):
            return str(m_norm)
        if (mn_norm is not None and mn_norm != 0) and (m_norm is None or m_norm == 0):
            return str(mn_norm)
        # Both have value and are equal, use M
        if (m_norm is not None and mn_norm is not None) and (m_norm == mn_norm):
            return str(m_norm)
        # Both present and different, use B/MN if possible, else MN
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
    # Fallback to M
    if m_norm not in [None, 0]:
        return str(m_norm)
    return "0"


def process_geojson(geojson_file):
    try:
        base_name = os.path.splitext(os.path.basename(geojson_file))[0]
        print(f"Processing: {base_name}")
        layer = QgsVectorLayer(geojson_file, base_name, "ogr")
        if not layer.isValid():
            print(f"Layer failed to load. Skipping.")
            return

        geom_type = QgsWkbTypes.displayString(layer.wkbType()).lower()
        crs_authid = layer.crs().authid()
        mem_layer = QgsVectorLayer(f"{geom_type}?crs={crs_authid}", base_name, "memory")
        mem_provider = mem_layer.dataProvider()
        fields = layer.fields()
        if "group_key" not in fields.names():
            fields.append(QgsField("group_key", QVariant.String))
        mem_provider.addAttributes(fields)
        mem_layer.updateFields()

        new_features = []
        for feat in layer.getFeatures():
            geom = feat.geometry()
            if not geom.isGeosValid():
                geom = geom.makeValid()
            new_feat = QgsFeature(mem_layer.fields())
            new_feat.setGeometry(geom)
            attrs = list(feat.attributes())
            if len(attrs) < mem_layer.fields().count():
                attrs += [None] * (mem_layer.fields().count() - len(attrs))
            group_key = get_group_key(feat)
            group_key_idx = mem_layer.fields().indexFromName("group_key")
            attrs[group_key_idx] = group_key
            new_feat.setAttributes(attrs)
            new_features.append(new_feat)
        mem_provider.addFeatures(new_features)
        mem_layer.updateExtents()
        layer = mem_layer
        print(f"Memory layer created.")

        QgsProject.instance().addMapLayer(layer)
        try:
            tile_style_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tile_style.qml")
            if os.path.exists(tile_style_path):
                layer.loadNamedStyle(tile_style_path)
        except Exception:
            print("Could not apply tile_style.qml.")
        layer.setLabelsEnabled(True)
        layer.triggerRepaint()
        QApplication.processEvents()

        outline_layer = None
        fields_present = layer.fields().names()
        if "M" not in fields_present or "Type" not in fields_present:
            print(f"Layer missing M or Type field.")
        else:
            if layer.fields().indexFromName("group_key") == -1:
                print("group_key field missing.")
                return
            dissolved = processing.run(
                "native:dissolve",
                {"INPUT": layer, "FIELD": ["group_key"], "OUTPUT": "memory:"},
                feedback=MinimalFeedback())["OUTPUT"]
            outline_layer = processing.run(
                "native:multiparttosingleparts",
                {"INPUT": dissolved, "OUTPUT": "memory:"},
                feedback=MinimalFeedback())["OUTPUT"]
            clean_msg = clean_outline_layer(outline_layer)
            print(f"Outline cleaned. {clean_msg}")
            QgsProject.instance().addMapLayer(outline_layer)
            try:
                murabb_style_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "murabb_style.qml")
                if os.path.exists(murabb_style_path):
                    outline_layer.loadNamedStyle(murabb_style_path)
            except Exception:
                print("Could not apply murabb_style.qml.")
            outline_layer.triggerRepaint()

            # Label
            lab = outline_layer.labeling().settings()
            lab.fieldName = '"group_key"'
            lab.isExpression = True
            outline_layer.setLabeling(QgsVectorLayerSimpleLabeling(lab))
            outline_layer.setLabelsEnabled(True)
            outline_layer.triggerRepaint()

        output_dir = os.path.join(os.path.dirname(geojson_file), base_name)
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)

        total_tiles = compute_total_tiles(layer.extent().xMinimum(), layer.extent().xMaximum(),
                                         layer.extent().yMinimum(), layer.extent().yMaximum(),
                                         10, 20)
        print(f"Tiles to generate: {total_tiles}")
        params = {
            'EXTENT': f"{layer.extent().xMinimum()},{layer.extent().xMaximum()},{layer.extent().yMinimum()},{layer.extent().yMaximum()} [EPSG:4326]",
            'ZOOM_MIN': 10,
            'ZOOM_MAX': 20,
            'DPI': 75,
            'BACKGROUND_COLOR': 'rgba(0, 0, 0, 0.00)',
            'ANTIALIAS': True,
            'TILE_FORMAT': 0,
            'QUALITY': 75,
            'METATILESIZE': 16,
            'TILE_WIDTH': 256,
            'TILE_HEIGHT': 256,
            'TMS_CONVENTION': False,
            'HTML_TITLE': '',
            'HTML_ATTRIBUTION': '',
            'HTML_OSM': False,
            'OUTPUT_DIRECTORY': output_dir.replace("\\", "/")
        }
        processing.run("native:tilesxyzdirectory", params, feedback=MinimalFeedback())
        print(f"Tiles generated for '{base_name}'.")
        clean_tiles(output_dir, prefix=f"{base_name}: ")

    except Exception as e:
        print(f"Error processing {geojson_file}")
    finally:
        try:
            for l in list(QgsProject.instance().mapLayers().values()):
                QgsProject.instance().removeMapLayer(l.id())
        except Exception:
            pass
        QApplication.processEvents()
        gc.collect()
        time.sleep(2)

# ========== MAIN LOOP ==========

main_folder = select_main_folder()
if not main_folder:
    print("No folder selected. Exiting.")
else:
    print(f"Selected folder: {main_folder}")

    build_job_list(main_folder)

    while not check_all_done(main_folder):
        geojson_file = claim_next_job(main_folder)
        if geojson_file is None:
            print("Waiting for jobs...")
            time.sleep(5)
            continue
        print(f"\nClaimed: {os.path.basename(geojson_file)}")
        process_geojson(geojson_file)
        mark_job_done(main_folder, geojson_file)
    print("All GeoJSON files processed.")

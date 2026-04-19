from flask import Flask, render_template, jsonify, request, session, redirect, url_for, Response
from dotenv import load_dotenv
from werkzeug.security import check_password_hash
import os
load_dotenv()

PIHOLE_PASSWORD = os.getenv('PIHOLE_PASSWORD')
JELLYFIN_API_KEY = os.getenv('JELLYFIN_API_KEY')
IMMICH_API_KEY = os.getenv('IMMICH_API_KEY')
NETWORK_HUB_PASSWORD_HASH = os.getenv('NETWORK_HUB_PASSWORD_HASH', '')

OBS_LAT     = -37.7939
OBS_LON     = 145.3214
EPA_KEY     = "ce469fc9d073425b9bbd9c44bda741f9"
EPA_SITE_ID = "9348c1f5-60c5-4c35-b4f1-1f0931ab1415"

weather_cache = {}
epa_cache = {}
import adafruit_dht
import adafruit_ccs811
import board
import busio
import threading
import time
import smbus2
import struct
import serial
import pynmea2
import urllib.request
import requests
import json
import os
import subprocess
import signal
import re
from icalendar import Calendar
from datetime import datetime, date, timedelta
import pytz
import recurring_ical_events
import psutil
import RPi.GPIO as GPIO

app = Flask(__name__)
app.secret_key = os.getenv('FLASK_SECRET_KEY', 'changeme')
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(hours=8)

PIR_PIN = 5

GPIO.setwarnings(False)
GPIO.setmode(GPIO.BCM)
GPIO.setup(PIR_PIN, GPIO.IN)

sensor_data = {
    "temperature": None,
    "humidity": None,
    "pressure": None,
    "co2": None,
    "tvoc": None,
    "ccs_ready": False,
    "gps_lat": None,
    "gps_lon": None,
    "gps_fix": False,
    "gps_satellites": None,
    "gps_elevation": None,
    "weather_temp": None,
    "weather_desc": None,
    "weather_rain": None,
    "dht_error": None,
    "bmp_error": None,
    "ccs_error": None,
    "gps_error": None,
    "weather_error": None,
    "_dht_last_read": None,
    "_bmp_last_read": None,
    "_ccs_last_read": None,
    "_gps_last_read": None,
    "pir": 0,
    "pir_last_triggered": None,
}

# Satellite data storage
satellite_data = {}  # keyed by PRN, stores latest info per satellite
satellite_history = {}  # keyed by PRN, list of timestamps seen

CONSTELLATION_MAP = {
    range(1, 33):    "GPS",
    range(33, 55):   "SBAS",
    range(65, 97):   "GLONASS",
    range(120, 159): "SBAS",
    range(193, 203): "QZSS",
    range(201, 237): "BeiDou",
    range(301, 337): "Galileo",
}

def get_constellation(prn):
    for r, name in CONSTELLATION_MAP.items():
        if prn in r:
            return name
    return "Unknown"

GPS_SAT_NAMES = {
    1: "GPS-IIF-3", 2: "GPS-IIR-13", 3: "GPS-IIF-4", 4: "GPS-IIF-5",
    5: "GPS-IIR-11", 6: "GPS-IIF-6", 7: "GPS-IIR-14", 8: "GPS-IIF-7",
    9: "GPS-IIF-8", 10: "GPS-IIF-9", 11: "GPS-IIR-15", 12: "GPS-IIF-10",
    13: "GPS-IIR-2", 14: "GPS-IIR-16", 15: "GPS-IIR-M-3", 16: "GPS-IIR-M-4",
    17: "GPS-IIR-M-1", 18: "GPS-IIR-M-2", 19: "GPS-IIR-17", 20: "GPS-IIR-18",
    21: "GPS-IIR-M-5", 22: "GPS-IIR-19", 23: "GPS-IIR-M-6", 24: "GPS-IIF-1",
    25: "GPS-IIF-2", 26: "GPS-IIF-11", 27: "GPS-IIF-12", 28: "GPS-IIF-13",
    29: "GPS-IIF-14", 30: "GPS-IIF-15", 31: "GPS-IIF-16", 32: "GPS-IIF-17",
}

def update_satellite(prn, elevation, azimuth, snr, in_use):
    now = time.time()
    constellation = get_constellation(prn)
    name = GPS_SAT_NAMES.get(prn, f"{constellation}-{prn}")
    satellite_data[prn] = {
        "prn": prn,
        "name": name,
        "constellation": constellation,
        "elevation": elevation,
        "azimuth": azimuth,
        "snr": snr,
        "in_use": in_use,
        "last_seen": now,
    }
    if prn not in satellite_history:
        satellite_history[prn] = []
    satellite_history[prn].append(now)
    # Keep last 7 days of sightings
    cutoff = now - 7 * 86400
    satellite_history[prn] = [t for t in satellite_history[prn] if t > cutoff]

# History storage — last 24hrs of readings (max 1440 points at 1/min)
MAX_HISTORY = 1440
sensor_history = {
    "temperature": [],
    "humidity": [],
    "pressure": [],
    "satellites": [],
}

def add_history(key, value):
    if value is None:
        return
    sensor_history[key].append({"t": int(time.time()), "v": value})
    if len(sensor_history[key]) > MAX_HISTORY:
        sensor_history[key].pop(0)

WEATHER_CODES = {
    0: "Clear Sky", 1: "Mainly Clear", 2: "Partly Cloudy", 3: "Overcast",
    45: "Foggy", 48: "Icy Fog", 51: "Light Drizzle", 53: "Drizzle",
    55: "Heavy Drizzle", 61: "Light Rain", 63: "Rain", 65: "Heavy Rain",
    71: "Light Snow", 73: "Snow", 75: "Heavy Snow", 77: "Snow Grains",
    80: "Light Showers", 81: "Showers", 82: "Heavy Showers",
    85: "Snow Showers", 86: "Heavy Snow Showers",
    95: "Thunderstorm", 96: "Thunderstorm + Hail", 99: "Heavy Thunderstorm"
}

WEATHER_ICONS = {
    0: "☀️", 1: "🌤️", 2: "⛅", 3: "☁️",
    45: "🌫️", 48: "🌫️", 51: "🌦️", 53: "🌦️",
    55: "🌧️", 61: "🌧️", 63: "🌧️", 65: "🌧️",
    71: "🌨️", 73: "🌨️", 75: "🌨️", 77: "🌨️",
    80: "🌦️", 81: "🌧️", 82: "⛈️",
    85: "🌨️", 86: "🌨️",
    95: "⛈️", 96: "⛈️", 99: "⛈️"
}

ICAL_DAN = "https://calendar.google.com/calendar/ical/dan.giret%40gmail.com/private-696be1b4ff7d1a6e18c9533f3120ecb4/basic.ics"
ICAL_TIEN = "https://calendar.google.com/calendar/ical/hotien604%40gmail.com/private-d9b4e8f3a71c9f591dd6a6458557118b/basic.ics"
MELBOURNE_TZ = pytz.timezone("Australia/Melbourne")
HEALTH_DIR = "/home/dan-g/pi_hub_web/health_data"
SLEEP_TARGET = 7.5

def load_health_data():
    data = {}
    for fname in ["daily", "sleep", "heart", "correlations", "bests"]:
        path = f"{HEALTH_DIR}/{fname}.json"
        if os.path.exists(path):
            with open(path) as f:
                data[fname] = json.load(f)
        else:
            data[fname] = {}
    return data

health = load_health_data()

def get_sleep_stats():
    daily = health.get("daily", {})
    correlations = health.get("correlations", {})
    all_dates = sorted(daily.keys())
    last_night = None
    for d in reversed(all_dates):
        if daily[d].get("sleep_hours"):
            last_night = {"date": d, **daily[d]}
            break
    recent_7 = [daily[d] for d in all_dates[-7:] if daily[d].get("sleep_hours")]
    avg_7 = round(sum(d["sleep_hours"] for d in recent_7) / len(recent_7), 1) if recent_7 else None
    recent_30 = [daily[d] for d in all_dates[-30:] if daily[d].get("sleep_hours")]
    avg_30 = round(sum(d["sleep_hours"] for d in recent_30) / len(recent_30), 1) if recent_30 else None
    deep_avgs = [d["deep_mins"] for d in recent_30 if d.get("deep_mins")]
    rem_avgs = [d["rem_mins"] for d in recent_30 if d.get("rem_mins")]
    core_avgs = [d["core_mins"] for d in recent_30 if d.get("core_mins")]
    avg_deep = round(sum(deep_avgs) / len(deep_avgs)) if deep_avgs else None
    avg_rem = round(sum(rem_avgs) / len(rem_avgs)) if rem_avgs else None
    avg_core = round(sum(core_avgs) / len(core_avgs)) if core_avgs else None
    sleep_debt = correlations.get("total_sleep_debt_hours", 0)
    streak_under = 0
    for d in reversed(all_dates):
        sh = daily[d].get("sleep_hours")
        if sh is None:
            continue
        if sh < SLEEP_TARGET:
            streak_under += 1
        else:
            break
    sleep_score = None
    if last_night:
        sh = last_night.get("sleep_hours", 0)
        deep = last_night.get("deep_mins", 0)
        rem = last_night.get("rem_mins", 0)
        total_mins = deep + rem + last_night.get("core_mins", 0)
        duration_score = min(sh / SLEEP_TARGET * 50, 50)
        deep_score = min(deep / 90 * 25, 25) if total_mins > 0 else 0
        rem_score = min(rem / 90 * 25, 25) if total_mins > 0 else 0
        sleep_score = round(duration_score + deep_score + rem_score)
    insight = ""
    if last_night:
        sh = last_night.get("sleep_hours", 0)
        deep = last_night.get("deep_mins", 0)
        if sh >= SLEEP_TARGET:
            insight = f"Great night - you hit your {SLEEP_TARGET}hr target."
        elif sh >= 6:
            insight = f"Decent sleep but {round(SLEEP_TARGET - sh, 1)}hrs short of your target."
        else:
            insight = f"Short night. You're {round(SLEEP_TARGET - sh, 1)}hrs under target."
        if avg_deep and deep > avg_deep * 1.2:
            insight += " Deep sleep was above your average - good recovery."
        elif avg_deep and deep < avg_deep * 0.8:
            insight += " Deep sleep was below average - body may need more recovery."
        if streak_under >= 3:
            insight += f" You've been under target {streak_under} nights in a row."
    return {
        "last_night": last_night,
        "avg_7": avg_7,
        "avg_30": avg_30,
        "avg_deep": avg_deep,
        "avg_rem": avg_rem,
        "avg_core": avg_core,
        "sleep_debt": round(sleep_debt, 1),
        "streak_under": streak_under,
        "sleep_score": sleep_score,
        "sleep_target": SLEEP_TARGET,
        "insight": insight,
        "trend_30": correlations.get("recent_30d", {}).get("sleep_trend", ""),
        "total_nights": len([d for d in all_dates if daily[d].get("sleep_hours")]),
    }

def get_gpio_in_use():
    in_use = set()
    # Only include pins with actual software consumers (not phantom SPI/UART)
    try:
        result = subprocess.run(["gpioinfo"], capture_output=True, text=True)
        for line in result.stdout.split("\n"):
            if 'consumer=' in line and 'ACT' not in line:
                match = re.search(r"line\s+(\d+)", line)
                if match:
                    gpio_num = int(match.group(1))
                    # Skip SPI CE pins — auto-claimed by kernel when SPI enabled, not physically wired
                    if gpio_num in [7, 8]:
                        continue
                    in_use.add(gpio_num)
    except:
        pass
    # Hardcode physically wired pins
    if os.path.exists("/dev/i2c-1"):
        in_use.add(2)   # SDA — BMP180 (Pin 3)
        in_use.add(3)   # SCL — BMP180 (Pin 5)
    if os.path.exists("/dev/ttyACM0"):
        in_use.add(14)  # GPS TX (Pin 8)
        in_use.add(15)  # GPS RX (Pin 10)
    in_use.add(4)       # DHT11 (Pin 7)
    in_use.add(5)       # PIR (Pin 29)
    return sorted(list(in_use))

def get_device_stats():
    stats = {}
    stats["cpu_percent"] = psutil.cpu_percent(interval=0.5)
    stats["cpu_freq"] = round(psutil.cpu_freq().current) if psutil.cpu_freq() else None
    stats["load_avg"] = round(psutil.getloadavg()[0], 2)
    stats["cpu_count"] = psutil.cpu_count()
    stats["cpu_temp"] = None
    try:
        temps = psutil.sensors_temperatures()
        if "cpu_thermal" in temps:
            stats["cpu_temp"] = round(temps["cpu_thermal"][0].current, 1)
    except:
        pass
    mem = psutil.virtual_memory()
    stats["ram_used"] = round(mem.used / 1024**3, 1)
    stats["ram_total"] = round(mem.total / 1024**3, 1)
    stats["ram_percent"] = mem.percent
    disk = psutil.disk_usage("/")
    stats["disk_used"] = round(disk.used / 1024**3, 1)
    stats["disk_total"] = round(disk.total / 1024**3, 1)
    stats["disk_percent"] = disk.percent
    uptime_secs = time.time() - psutil.boot_time()
    hours = int(uptime_secs // 3600)
    mins = int((uptime_secs % 3600) // 60)
    days = hours // 24
    hours = hours % 24
    stats["uptime"] = f"{days}d {hours}h {mins}m" if days > 0 else f"{hours}h {mins}m"
    stats["ip_local"] = None
    stats["ip_tailscale"] = None
    stats["hostname"] = "3.14159265359"
    try:
        result = subprocess.run(["ip", "addr"], capture_output=True, text=True)
        for line in result.stdout.split("\n"):
            if "inet " in line and "127.0.0.1" not in line:
                ip = line.strip().split()[1].split("/")[0]
                if ip.startswith("100."):
                    stats["ip_tailscale"] = ip
                else:
                    stats["ip_local"] = ip
    except:
        pass
    stats["bluetooth"] = "Off"
    try:
        result = subprocess.run(["hciconfig"], capture_output=True, text=True)
        if "UP RUNNING" in result.stdout:
            stats["bluetooth"] = "Active"
        elif "hci0" in result.stdout:
            stats["bluetooth"] = "Available"
    except:
        pass
    stats["wifi_ssid"] = None
    stats["wifi_signal"] = None
    try:
        result = subprocess.run(["iwgetid", "-r"], capture_output=True, text=True)
        stats["wifi_ssid"] = result.stdout.strip() or None
        result2 = subprocess.run(["iwconfig", "wlan0"], capture_output=True, text=True)
        for line in result2.stdout.split("\n"):
            if "Signal level" in line:
                match = re.search(r"Signal level=(-?\d+)", line)
                if match:
                    stats["wifi_signal"] = int(match.group(1))
    except:
        pass
    stats["i2c_devices"] = []
    try:
        result = subprocess.run(["i2cdetect", "-y", "1"], capture_output=True, text=True, timeout=5)
        known = {"5a": "CCS811", "77": "BMP180"}
        for line in result.stdout.split("\n"):
            parts = line.split()
            for part in parts:
                if part != "--" and len(part) == 2:
                    try:
                        int(part, 16)
                        label = known.get(part.lower(), f"0x{part.upper()}")
                        stats["i2c_devices"].append({"addr": f"0x{part.upper()}", "label": label})
                    except:
                        pass
    except:
        pass
    stats["spi_enabled"] = os.path.exists("/dev/spidev0.0")
    stats["serial_devices"] = []
    for dev in ["/dev/ttyACM0", "/dev/ttyACM1", "/dev/ttyUSB0", "/dev/ttyUSB1"]:
        if os.path.exists(dev):
            known_serial = {"/dev/ttyACM0": "GPS (NEO-7M)", "/dev/ttyUSB0": "USB Serial"}
            stats["serial_devices"].append({"port": dev, "label": known_serial.get(dev, "Serial Device")})
    stats["usb_devices"] = []
    try:
        result = subprocess.run(["lsusb"], capture_output=True, text=True)
        for line in result.stdout.strip().split("\n"):
            if line:
                parts = line.split(" ", 6)
                name = parts[6] if len(parts) > 6 else "Unknown"
                if "Linux Foundation" not in name and "root hub" not in name.lower():
                    stats["usb_devices"].append(name.strip())
    except:
        pass
    stats["open_ports"] = []
    try:
        result = subprocess.run(["ss", "-tlnp"], capture_output=True, text=True)
        for line in result.stdout.split("\n")[1:]:
            parts = line.split()
            if len(parts) >= 4:
                addr = parts[3]
                port = addr.split(":")[-1]
                try:
                    stats["open_ports"].append({"port": int(port)})
                except:
                    pass
    except:
        pass
    stats["gpio_in_use"] = get_gpio_in_use()

    # SD card health
    stats["sd_health"] = {}
    try:
        result = subprocess.run(["vcgencmd", "get_throttled"], capture_output=True, text=True)
        val = result.stdout.strip().replace("throttled=", "")
        throttle_int = int(val, 16)
        stats["throttled"] = throttle_int != 0
        stats["throttle_code"] = val
        flags = []
        if throttle_int & 0x1: flags.append("Under-voltage")
        if throttle_int & 0x2: flags.append("Freq cap")
        if throttle_int & 0x4: flags.append("Throttled")
        if throttle_int & 0x8: flags.append("Soft temp limit")
        stats["throttle_flags"] = flags
    except:
        stats["throttled"] = False
        stats["throttle_code"] = None
        stats["throttle_flags"] = []

    # SD card info
    try:
        result = subprocess.run(["cat", "/sys/block/mmcblk0/device/name"], capture_output=True, text=True)
        stats["sd_name"] = result.stdout.strip() or "Unknown"
        result2 = subprocess.run(["cat", "/sys/block/mmcblk0/device/csd"], capture_output=True, text=True)
        stats["sd_info"] = result2.stdout.strip()[:30] if result2.stdout else None
    except:
        stats["sd_name"] = None
        stats["sd_info"] = None

    # Camera detection
    stats["camera_detected"] = False
    try:
        result = subprocess.run(["vcgencmd", "get_camera"], capture_output=True, text=True)
        stats["camera_detected"] = "detected=1" in result.stdout
    except:
        pass

    # Bluetooth connected devices
    stats["bt_devices"] = []
    try:
        result = subprocess.run(["bluetoothctl", "devices", "Connected"], capture_output=True, text=True, timeout=3)
        for line in result.stdout.strip().split("\n"):
            if line.strip() and "Device" in line:
                parts = line.strip().split(" ", 2)
                stats["bt_devices"].append(parts[2] if len(parts) > 2 else line.strip())
    except:
        pass

    # USB devices — smart detection, filter internal chips
    stats["usb_ports"] = {"total": 4, "connected": 0, "devices": []}
    # Internal/system USB devices to filter out (not physical external devices)
    internal_filter = [
        "via labs", "via tech", "genesys logic", "texas instruments",
        "syntek", "microchip tech", "standard microsystems",
        "integrated circuits", "prolific", "ftdi", "hub"
    ]
    try:
        result = subprocess.run(["lsusb"], capture_output=True, text=True)
        known_input_vids = ["046d", "045e", "04d9", "1532", "258a", "0c45", "093a", "1bcf", "04f2", "0461", "1a2c"]
        for line in result.stdout.strip().split("\n"):
            if not line: continue
            parts = line.split(" ", 6)
            name = parts[6].strip() if len(parts) > 6 else "Unknown"
            vid = parts[5].split(":")[0].lower() if len(parts) > 5 else ""
            pid = parts[5].split(":")[1].lower() if len(parts) > 5 and ":" in parts[5] else ""
            # Skip system devices
            if "Linux Foundation" in name or "root hub" in name.lower():
                continue
            # Skip internal hub/controller chips
            if any(f in name.lower() for f in internal_filter):
                continue
            # Classify known devices
            if any(k in vid for k in known_input_vids) or any(k in name.lower() for k in ["keyboard", "mouse", "hid", "logitech", "nano", "receiver"]):
                label = "Input Dongle"
            elif "u-blox" in name.lower() or "neo" in name.lower() or "gps" in name.lower():
                label = "GPS (NEO-7M)"
            else:
                label = name[:30] if len(name) > 30 else name
            stats["usb_ports"]["devices"].append(label)
        stats["usb_ports"]["connected"] = len(stats["usb_ports"]["devices"])
    except:
        pass

    # Speedtest cache
    stats["speedtest"] = dict(speedtest_cache)

    return stats

GPIO_PINS = [
    {"pin": 1,  "name": "3.3V",   "type": "power",   "gpio": -1},
    {"pin": 2,  "name": "5V",     "type": "power",   "gpio": -1},
    {"pin": 3,  "name": "GPIO2",  "type": "gpio",    "gpio": 2},
    {"pin": 4,  "name": "5V",     "type": "power",   "gpio": -1},
    {"pin": 5,  "name": "GPIO3",  "type": "gpio",    "gpio": 3},
    {"pin": 6,  "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 7,  "name": "GPIO4",  "type": "gpio",    "gpio": 4},
    {"pin": 8,  "name": "GPIO14", "type": "gpio",    "gpio": 14},
    {"pin": 9,  "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 10, "name": "GPIO15", "type": "gpio",    "gpio": 15},
    {"pin": 11, "name": "GPIO17", "type": "gpio",    "gpio": 17},
    {"pin": 12, "name": "GPIO18", "type": "gpio",    "gpio": 18},
    {"pin": 13, "name": "GPIO27", "type": "gpio",    "gpio": 27},
    {"pin": 14, "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 15, "name": "GPIO22", "type": "gpio",    "gpio": 22},
    {"pin": 16, "name": "GPIO23", "type": "gpio",    "gpio": 23},
    {"pin": 17, "name": "3.3V",   "type": "power",   "gpio": -1},
    {"pin": 18, "name": "GPIO24", "type": "gpio",    "gpio": 24},
    {"pin": 19, "name": "GPIO10", "type": "gpio",    "gpio": 10},
    {"pin": 20, "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 21, "name": "GPIO9",  "type": "gpio",    "gpio": 9},
    {"pin": 22, "name": "GPIO25", "type": "gpio",    "gpio": 25},
    {"pin": 23, "name": "GPIO11", "type": "gpio",    "gpio": 11},
    {"pin": 24, "name": "GPIO8",  "type": "gpio",    "gpio": 8},
    {"pin": 25, "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 26, "name": "GPIO7",  "type": "gpio",    "gpio": 7},
    {"pin": 27, "name": "ID_SD",  "type": "special", "gpio": -1},
    {"pin": 28, "name": "ID_SC",  "type": "special", "gpio": -1},
    {"pin": 29, "name": "GPIO5",  "type": "gpio",    "gpio": 5},
    {"pin": 30, "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 31, "name": "GPIO6",  "type": "gpio",    "gpio": 6},
    {"pin": 32, "name": "GPIO12", "type": "gpio",    "gpio": 12},
    {"pin": 33, "name": "GPIO13", "type": "gpio",    "gpio": 13},
    {"pin": 34, "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 35, "name": "GPIO19", "type": "gpio",    "gpio": 19},
    {"pin": 36, "name": "GPIO16", "type": "gpio",    "gpio": 16},
    {"pin": 37, "name": "GPIO26", "type": "gpio",    "gpio": 26},
    {"pin": 38, "name": "GPIO20", "type": "gpio",    "gpio": 20},
    {"pin": 39, "name": "GND",    "type": "ground",  "gpio": -1},
    {"pin": 40, "name": "GPIO21", "type": "gpio",    "gpio": 21},
]

dht = adafruit_dht.DHT11(board.D4)
i2c = busio.I2C(board.SCL, board.SDA)

ccs = None
for attempt in range(5):
    try:
        ccs = adafruit_ccs811.CCS811(i2c)
        print(f"CCS811 initialised on attempt {attempt + 1}")
        break
    except Exception as e:
        print(f"CCS811 attempt {attempt + 1} failed: {e}")
        time.sleep(2)

if ccs is None:
    print("CCS811 failed to initialise - continuing without it")

BMP180_ADDR = 0x77
bus = smbus2.SMBus(1)

def read_bmp180():
    cal = bus.read_i2c_block_data(BMP180_ADDR, 0xAA, 22)
    AC1 = struct.unpack('>h', bytes(cal[0:2]))[0]
    AC2 = struct.unpack('>h', bytes(cal[2:4]))[0]
    AC3 = struct.unpack('>h', bytes(cal[4:6]))[0]
    AC4 = struct.unpack('>H', bytes(cal[6:8]))[0]
    AC5 = struct.unpack('>H', bytes(cal[8:10]))[0]
    AC6 = struct.unpack('>H', bytes(cal[10:12]))[0]
    B1  = struct.unpack('>h', bytes(cal[12:14]))[0]
    B2  = struct.unpack('>h', bytes(cal[14:16]))[0]
    MB  = struct.unpack('>h', bytes(cal[16:18]))[0]
    MC  = struct.unpack('>h', bytes(cal[18:20]))[0]
    MD  = struct.unpack('>h', bytes(cal[20:22]))[0]
    bus.write_byte_data(BMP180_ADDR, 0xF4, 0x2E)
    time.sleep(0.005)
    raw_temp = bus.read_i2c_block_data(BMP180_ADDR, 0xF6, 2)
    UT = (raw_temp[0] << 8) + raw_temp[1]
    bus.write_byte_data(BMP180_ADDR, 0xF4, 0x34)
    time.sleep(0.005)
    raw_pres = bus.read_i2c_block_data(BMP180_ADDR, 0xF6, 3)
    UP = ((raw_pres[0] << 16) + (raw_pres[1] << 8) + raw_pres[2]) >> 8
    X1 = ((UT - AC6) * AC5) >> 15
    X2 = (MC << 11) // (X1 + MD)
    B5 = X1 + X2
    B6 = B5 - 4000
    X1 = (B2 * (B6 * B6 >> 12)) >> 11
    X2 = AC2 * B6 >> 11
    X3 = X1 + X2
    B3 = (((AC1 * 4 + X3) + 2)) // 4
    X1 = AC3 * B6 >> 13
    X2 = (B1 * (B6 * B6 >> 12)) >> 16
    X3 = ((X1 + X2) + 2) >> 2
    B4 = AC4 * (X3 + 32768) >> 15
    B7 = (UP - B3) * 50000
    p = (B7 * 2) // B4 if B7 < 0x80000000 else (B7 // B4) * 2
    X1 = (p >> 8) ** 2
    X1 = (X1 * 3038) >> 16
    X2 = (-7357 * p) >> 16
    pressure = p + ((X1 + X2 + 3791) >> 4)
    return round(pressure / 100.0, 1)

def get_co2_status(co2):
    if co2 is None: return "unknown"
    if co2 > 10000: return "warmup"
    if co2 < 700: return "good"
    if co2 < 1000: return "caution"
    return "alert"

def get_tvoc_status(tvoc):
    if tvoc is None: return "unknown"
    if tvoc == 32768: return "warmup"
    if tvoc < 220: return "good"
    if tvoc < 660: return "caution"
    return "alert"

def fetch_events(url, color):
    try:
        with urllib.request.urlopen(url, timeout=10) as response:
            cal_data = response.read()
        cal = Calendar.from_ical(cal_data)
        start = datetime.now(MELBOURNE_TZ) - timedelta(days=60)
        end = datetime.now(MELBOURNE_TZ) + timedelta(days=365)
        expanded = recurring_ical_events.of(cal).between(start, end)
        events = []
        for component in expanded:
            try:
                dtstart = component.get("DTSTART").dt
                dtend = component.get("DTEND").dt if component.get("DTEND") else None
                if isinstance(dtstart, datetime):
                    dtstart = dtstart.astimezone(MELBOURNE_TZ)
                    start_str = dtstart.isoformat()
                else:
                    start_str = dtstart.isoformat()
                if dtend:
                    if isinstance(dtend, datetime):
                        dtend = dtend.astimezone(MELBOURNE_TZ)
                        end_str = dtend.isoformat()
                    else:
                        end_str = dtend.isoformat()
                else:
                    end_str = start_str
                events.append({
                    "title": str(component.get("SUMMARY", "")),
                    "start": start_str,
                    "end": end_str,
                    "color": color
                })
            except:
                continue
        return events
    except Exception as e:
        print(f"Calendar fetch error: {e}")
        return []

def get_today_events():
    try:
        today = datetime.now(MELBOURNE_TZ).date()
        all_events = fetch_events(ICAL_DAN, "#4a9eff")
        events = []
        for event in all_events:
            start = event["start"]
            try:
                dt = datetime.fromisoformat(start)
                event_date = dt.date() if hasattr(dt, 'date') else dt
                if event_date == today:
                    time_str = dt.strftime("%I:%M %p").lstrip("0") if "T" in start else "All Day"
                    events.append({"title": event["title"], "time": time_str})
            except:
                pass
        events.sort(key=lambda x: x["time"])
        return events
    except:
        return []

def poll_dht11():
    global dht
    while True:
        try:
            sensor_data["temperature"] = dht.temperature
            sensor_data["humidity"] = dht.humidity
            sensor_data["dht_error"] = None
            sensor_data["_dht_last_read"] = time.time()
            add_history("temperature", dht.temperature)
            add_history("humidity", dht.humidity)
        except Exception as e:
            sensor_data["dht_error"] = str(e)
        time.sleep(30)

def poll_bmp180():
    while True:
        try:
            p = read_bmp180()
            sensor_data["pressure"] = p
            sensor_data["bmp_error"] = None
            sensor_data["_bmp_last_read"] = time.time()
            add_history("pressure", p)
        except Exception as e:
            sensor_data["bmp_error"] = str(e)
        time.sleep(60)

def poll_ccs811():
    global ccs
    while True:
        if ccs is None:
            sensor_data["ccs_error"] = "Not initialised"
            time.sleep(30)
            continue
        try:
            if ccs.data_ready:
                sensor_data["co2"] = ccs.eco2
                sensor_data["tvoc"] = ccs.tvoc
                sensor_data["ccs_ready"] = ccs.baseline is not None
                sensor_data["ccs_error"] = None
                sensor_data["_ccs_last_read"] = time.time()
        except Exception as e:
            sensor_data["ccs_error"] = str(e)
        time.sleep(30)

_last_sat_history_time = 0

def poll_gps():
    global _last_sat_history_time
    active_prns = set()
    gsv_buffer = {}  # buffer incomplete GSV sequences
    while True:
        try:
            with serial.Serial('/dev/ttyACM0', 9600, timeout=1) as ser:
                while True:
                    line = ser.readline().decode('ascii', errors='replace').strip()

                    # Position fix
                    if line.startswith('$GPGGA') or line.startswith('$GNGGA'):
                        try:
                            msg = pynmea2.parse(line)
                            if msg.gps_qual > 0:
                                sensor_data["gps_lat"] = round(msg.latitude, 6)
                                sensor_data["gps_lon"] = round(msg.longitude, 6)
                                sensor_data["gps_fix"] = True
                                sensor_data["gps_satellites"] = msg.num_sats
                                now_ts = time.time()
                                if now_ts - _last_sat_history_time >= 60:
                                    add_history("satellites", msg.num_sats)
                                    _last_sat_history_time = now_ts
                                if msg.altitude:
                                    sensor_data["gps_elevation"] = round(float(msg.altitude), 1)
                            else:
                                sensor_data["gps_fix"] = False
                                sensor_data["gps_satellites"] = msg.num_sats
                            sensor_data["gps_error"] = None
                            sensor_data["_gps_last_read"] = time.time()
                        except:
                            pass

                    # Active satellites (which PRNs are being used for fix)
                    elif line.startswith('$GPGSA') or line.startswith('$GNGSA'):
                        try:
                            parts = line.split(',')
                            active_prns = set()
                            for p in parts[3:15]:
                                if p and p.strip():
                                    try:
                                        active_prns.add(int(p.strip()))
                                    except:
                                        pass
                        except:
                            pass

                    # Satellites in view — full detail
                    elif line.startswith('$GPGSV') or line.startswith('$GLGSV') or line.startswith('$GAGSV') or line.startswith('$GBGSV'):
                        try:
                            parts = line.split(',')
                            if len(parts) < 4:
                                continue
                            total_msgs = int(parts[1])
                            msg_num = int(parts[2])
                            # Parse satellite blocks (4 fields each: PRN, elev, azimuth, SNR)
                            i = 4
                            while i + 3 <= len(parts):
                                try:
                                    prn_str = parts[i].strip()
                                    elev_str = parts[i+1].strip()
                                    az_str = parts[i+2].strip()
                                    snr_str = parts[i+3].split('*')[0].strip()
                                    if prn_str:
                                        prn = int(prn_str)
                                        elev = int(elev_str) if elev_str else 0
                                        az = int(az_str) if az_str else 0
                                        snr = int(snr_str) if snr_str else 0
                                        in_use = prn in active_prns
                                        update_satellite(prn, elev, az, snr, in_use)
                                except:
                                    pass
                                i += 4
                        except:
                            pass

        except Exception as e:
            sensor_data["gps_error"] = str(e)
            time.sleep(5)

def poll_weather():
    time.sleep(10)
    while True:
        try:
            r = requests.get("https://api.open-meteo.com/v1/forecast", params={
                "latitude":      OBS_LAT,
                "longitude":     OBS_LON,
                "current":       "temperature_2m,relative_humidity_2m,apparent_temperature,precipitation,weather_code,wind_speed_10m,wind_direction_10m,wind_gusts_10m,uv_index,surface_pressure,cloud_cover,visibility",
                "hourly":        "temperature_2m,precipitation_probability,cloud_cover,uv_index,wind_speed_10m,visibility,weather_code",
                "daily":         "weather_code,temperature_2m_max,temperature_2m_min,precipitation_sum,uv_index_max,sunrise,sunset",
                "timezone":      "Australia/Melbourne",
                "forecast_days": 5
            }, timeout=15)
            r.raise_for_status()
            weather_cache["data"] = r.json()
            weather_cache["ts"] = time.time()
            weather_cache["error"] = None
        except Exception as e:
            weather_cache["error"] = str(e)
        time.sleep(1800)

def refresh_epa():
    time.sleep(15)
    while True:
        try:
            r = requests.get(
                f"https://gateway.api.epa.vic.gov.au/environmentMonitoring/v1/sites/{EPA_SITE_ID}/parameters",
                headers={"X-API-Key": EPA_KEY, "User-Agent": "curl/7.88.1", "Accept": "application/json"},
                timeout=30
            )
            r.raise_for_status()
            epa_cache["data"] = r.json()
            epa_cache["ts"] = time.time()
            epa_cache["error"] = None
        except Exception as e:
            epa_cache["error"] = str(e)
        time.sleep(3600)

def poll_pir():
    while True:
        try:
            val = GPIO.input(PIR_PIN)
            sensor_data["pir"] = val
            if val == 1:
                sensor_data["pir_last_triggered"] = time.time()
        except Exception:
            pass
        time.sleep(0.5)

# Speedtest results cache
speedtest_cache = {
    "download": None,
    "upload": None,
    "ping": None,
    "timestamp": None,
    "running": False,
}

def poll_speedtest():
    while True:
        speedtest_cache["running"] = True
        try:
            result = subprocess.run(
                ["python3", "-m", "speedtest", "--simple"],
                capture_output=True, text=True, timeout=60
            )
            for line in result.stdout.split("\n"):
                if line.startswith("Ping:"):
                    speedtest_cache["ping"] = line.split()[1]
                elif line.startswith("Download:"):
                    speedtest_cache["download"] = line.split()[1]
                elif line.startswith("Upload:"):
                    speedtest_cache["upload"] = line.split()[1]
            speedtest_cache["timestamp"] = time.time()
        except Exception as e:
            pass
        speedtest_cache["running"] = False
        time.sleep(1800)  # every 30 minutes

threading.Thread(target=poll_dht11, daemon=True).start()
threading.Thread(target=poll_bmp180, daemon=True).start()
threading.Thread(target=poll_ccs811, daemon=True).start()
threading.Thread(target=poll_gps, daemon=True).start()
threading.Thread(target=poll_weather, daemon=True).start()
threading.Thread(target=refresh_epa, daemon=True).start()
threading.Thread(target=poll_pir, daemon=True).start()
threading.Thread(target=poll_speedtest, daemon=True).start()

@app.route("/")
def index():
    today_events = get_today_events()
    return render_template("index.html",
        data=sensor_data,
        co2_status=get_co2_status(sensor_data["co2"]),
        tvoc_status=get_tvoc_status(sensor_data["tvoc"]),
        today_events=today_events
    )

@app.route("/schedule")
def schedule():
    return render_template("schedule.html")

@app.route("/device")
def device():
    stats = get_device_stats()
    return render_template("device.html", stats=stats, gpio_pins=GPIO_PINS)

@app.route("/api/sensor_history/<sensor>")
def api_sensor_history(sensor):
    if sensor not in sensor_history:
        return jsonify({"error": "Unknown sensor"})
    data = sensor_history[sensor]
    if not data:
        return jsonify({"data": [], "min": None, "max": None, "current": None})
    values = [d["v"] for d in data]
    return jsonify({
        "data": data,
        "min": round(min(values), 1),
        "max": round(max(values), 1),
        "current": round(values[-1], 1) if values else None,
        "count": len(data)
    })

@app.route("/api/gps/satellites")
def api_gps_satellites():
    now = time.time()
    sats = []
    for prn, sat in satellite_data.items():
        # Only include satellites seen in last 5 minutes
        if now - sat["last_seen"] < 300:
            history = satellite_history.get(prn, [])
            # Count visits in last 24hrs
            visits_24h = len([t for t in history if t > now - 86400])
            visits_7d = len([t for t in history if t > now - 7*86400])
            sats.append({
                **sat,
                "visits_24h": visits_24h,
                "visits_7d": visits_7d,
            })
    # Sort by signal strength descending
    sats.sort(key=lambda x: x["snr"] or 0, reverse=True)
    # Constellation summary
    constellations = {}
    for s in sats:
        c = s["constellation"]
        if c not in constellations:
            constellations[c] = {"total": 0, "in_use": 0}
        constellations[c]["total"] += 1
        if s["in_use"]:
            constellations[c]["in_use"] += 1
    return jsonify({
        "satellites": sats,
        "total_visible": len(sats),
        "total_in_use": len([s for s in sats if s["in_use"]]),
        "constellations": constellations,
        "timestamp": now,
    })

@app.route("/api/gps/history")
def api_gps_history():
    now = time.time()
    # Return visit frequency per PRN over last 7 days
    result = []
    for prn, times in satellite_history.items():
        sat = satellite_data.get(prn, {})
        result.append({
            "prn": prn,
            "name": sat.get("name", f"PRN-{prn}"),
            "constellation": sat.get("constellation", "Unknown"),
            "visits_24h": len([t for t in times if t > now - 86400]),
            "visits_7d": len([t for t in times if t > now - 7*86400]),
            "last_seen": sat.get("last_seen"),
        })
    result.sort(key=lambda x: x["visits_24h"], reverse=True)
    return jsonify(result)

@app.route("/cosmos")
def cosmos():
    return render_template("cosmos.html")

@app.route("/api/cosmos", methods=["POST"])
def api_cosmos():
    try:
        data = request.get_json()
        message = data.get("message", "")
        history = data.get("history", [])
        
        import urllib.request as ur
        import json as js
        
        messages = history + [{"role": "user", "content": message}]
        
        payload = js.dumps({
            "model": "tinyllama",
            "messages": [
                {"role": "system", "content": "You are a brilliant cosmologist and space scientist. You specialise in cosmology, astrophysics, the Fermi Paradox, consciousness and its relationship to the universe, quantum mechanics, the nature of time, extraterrestrial life, black holes, dark matter, and the deepest questions about existence. You are deeply knowledgeable, intellectually rigorous, but also willing to explore speculative ideas with curiosity and enthusiasm. Keep responses concise but profound. The user is highly intelligent and curious — challenge them, inspire them, go deep."},
                *messages
            ],
            "stream": False
        }).encode()
        
        req = ur.Request(
            "http://localhost:11434/api/chat",
            data=payload,
            headers={"Content-Type": "application/json"}
        )
        
        with ur.urlopen(req, timeout=60) as resp:
            result = js.loads(resp.read())
            reply = result["message"]["content"]
            return jsonify({"reply": reply, "success": True})
    except Exception as e:
        return jsonify({"reply": f"Error: {str(e)}", "success": False})

@app.route("/api/events")
def api_events():
    dan_events = fetch_events(ICAL_DAN, "#4a9eff")
    tien_events = fetch_events(ICAL_TIEN, "#f472b6")
    return jsonify(dan_events + tien_events)

@app.route("/api/sensor_status")
def api_sensor_status():
    return jsonify({
        "dht11":  {"last_read": sensor_data.get("_dht_last_read"), "error": sensor_data.get("dht_error")},
        "bmp180": {"last_read": sensor_data.get("_bmp_last_read"), "error": sensor_data.get("bmp_error")},
        "ccs811": {"last_read": sensor_data.get("_ccs_last_read"), "error": sensor_data.get("ccs_error"), "co2": sensor_data.get("co2")},
        "gps":    {"last_read": sensor_data.get("_gps_last_read"), "error": sensor_data.get("gps_error"), "fix": sensor_data.get("gps_fix", False)},
    })

@app.route("/api/system_stats")
def api_system_stats():
    try:
        cpu = psutil.cpu_percent(interval=0.2)
        mem = psutil.virtual_memory()
        cpu_temp = None
        try:
            temps = psutil.sensors_temperatures()
            if "cpu_thermal" in temps:
                cpu_temp = round(temps["cpu_thermal"][0].current, 1)
        except:
            pass
        uptime_secs = time.time() - psutil.boot_time()
        hours = int(uptime_secs // 3600)
        mins = int((uptime_secs % 3600) // 60)
        days = hours // 24
        hours = hours % 24
        uptime = f"{days}d {hours}h {mins}m" if days > 0 else f"{hours}h {mins}m"
        return jsonify({
            "cpu_percent": round(cpu, 1),
            "cpu_temp": cpu_temp,
            "ram_percent": round(mem.percent, 1),
            "uptime": uptime,
        })
    except Exception as e:
        return jsonify({"error": str(e)})

@app.route("/api/gpio_sensors")
def api_gpio_sensors():
    last = sensor_data.get("pir_last_triggered")
    if last:
        diff = int(time.time() - last)
        if diff < 60:
            last_str = f"{diff}s ago"
        elif diff < 3600:
            last_str = f"{diff//60}m ago"
        else:
            last_str = f"{diff//3600}h ago"
    else:
        last_str = "Never"
    return jsonify({
        "pir": sensor_data.get("pir", 0),
        "pir_last_triggered": last_str,
    })

@app.route("/api/test/<sensor>")
def api_test_sensor(sensor):
    try:
        if sensor == "dht11":
            test_dht = adafruit_dht.DHT11(board.D4)
            for _ in range(5):
                try:
                    temp = test_dht.temperature
                    hum = test_dht.humidity
                    if temp is not None and hum is not None:
                        return jsonify({"success": True, "reading": f"{temp}C / {hum}%"})
                except:
                    pass
                time.sleep(1)
            return jsonify({"success": False, "error": "No response"})
        elif sensor == "bmp180":
            try:
                pressure = read_bmp180()
                return jsonify({"success": True, "reading": f"{pressure} hPa"})
            except Exception as e:
                return jsonify({"success": False, "error": str(e)})
        elif sensor == "ccs811":
            if ccs is None:
                return jsonify({"success": False, "error": "Not initialised"})
            try:
                if ccs.data_ready:
                    co2 = ccs.eco2
                    tvoc = ccs.tvoc
                    if co2 and co2 < 10000:
                        return jsonify({"success": True, "reading": f"{co2}ppm / {tvoc}ppb"})
                    else:
                        return jsonify({"success": False, "error": "Warming up"})
                else:
                    return jsonify({"success": False, "error": "Not ready"})
            except Exception as e:
                return jsonify({"success": False, "error": str(e)})
        elif sensor == "gps":
            if os.path.exists("/dev/ttyACM0"):
                fix = sensor_data.get("gps_fix", False)
                sats = sensor_data.get("gps_satellites", 0)
                lat = sensor_data.get("gps_lat")
                if fix and lat:
                    return jsonify({"success": True, "reading": f"Fix / {sats} sats"})
                elif sats:
                    return jsonify({"success": False, "error": f"No fix / {sats} sats"})
                else:
                    return jsonify({"success": False, "error": "Searching..."})
            else:
                return jsonify({"success": False, "error": "Not found"})
        else:
            return jsonify({"success": False, "error": "Unknown sensor"})
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})

@app.route("/api/reinit/<sensor>")
def api_reinit_sensor(sensor):
    global dht, ccs, i2c
    try:
        if sensor == "dht11":
            try:
                dht.exit()
            except:
                pass
            time.sleep(1)
            dht = adafruit_dht.DHT11(board.D4)
            sensor_data["dht_error"] = None
            return jsonify({"success": True, "message": "DHT11 reinitialised"})
        elif sensor == "bmp180":
            try:
                read_bmp180()
                sensor_data["bmp_error"] = None
                return jsonify({"success": True, "message": "BMP180 recalibrated"})
            except Exception as e:
                return jsonify({"success": False, "error": str(e)})
        elif sensor == "ccs811":
            try:
                ccs = adafruit_ccs811.CCS811(i2c)
                sensor_data["ccs_error"] = None
                sensor_data["co2"] = None
                sensor_data["tvoc"] = None
                return jsonify({"success": True, "message": "CCS811 reinitialised"})
            except Exception as e:
                return jsonify({"success": False, "error": str(e)})
        elif sensor == "ccs811_baseline":
            if ccs is None:
                return jsonify({"success": False, "error": "Not initialised"})
            try:
                ccs.baseline = 0
                sensor_data["co2"] = None
                sensor_data["tvoc"] = None
                return jsonify({"success": True, "message": "Baseline reset"})
            except Exception as e:
                return jsonify({"success": False, "error": str(e)})
        elif sensor == "gps":
            sensor_data["gps_error"] = None
            sensor_data["gps_fix"] = False
            sensor_data["gps_satellites"] = None
            return jsonify({"success": True, "message": "GPS reset"})
        elif sensor == "all":
            results = []
            try:
                try:
                    dht.exit()
                except:
                    pass
                time.sleep(0.5)
                dht = adafruit_dht.DHT11(board.D4)
                sensor_data["dht_error"] = None
                results.append("DHT11 OK")
            except:
                results.append("DHT11 fail")
            try:
                read_bmp180()
                sensor_data["bmp_error"] = None
                results.append("BMP180 OK")
            except:
                results.append("BMP180 fail")
            sensor_data["gps_error"] = None
            results.append("GPS reset")
            return jsonify({"success": True, "message": " · ".join(results)})
        else:
            return jsonify({"success": False, "error": "Unknown sensor"})
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})

@app.route("/api/speedtest/status")
def api_speedtest_status():
    return jsonify(speedtest_cache)

@app.route("/api/device/full_stats")
def api_device_full_stats():
    stats = get_device_stats()
    return jsonify(stats)

@app.route("/api/gpio/pin/<int:gpio_num>")
def api_gpio_pin(gpio_num):
    try:
        data = {
            "gpio": gpio_num,
            "value": None,
            "direction": None,
            "consumer": None,
            "pull": None,
            "raw_line": None,
            "verdict": None,
        }
        result = subprocess.run(["gpioinfo"], capture_output=True, text=True)
        for line in result.stdout.split("\n"):
            match = re.search(rf"line\s+{gpio_num}:", line)
            if match:
                data["raw_line"] = line.strip()
                if "output" in line:
                    data["direction"] = "OUTPUT"
                elif "input" in line:
                    data["direction"] = "INPUT"
                cm = re.search(r'consumer="([^"]+)"', line)
                if cm:
                    data["consumer"] = cm.group(1)
                if "pull-up" in line:
                    data["pull"] = "pull-up"
                elif "pull-down" in line:
                    data["pull"] = "pull-down"
                else:
                    data["pull"] = "none"
                break
        try:
            GPIO.setup(gpio_num, GPIO.IN)
            data["value"] = GPIO.input(gpio_num)
        except Exception as e:
            data["value_error"] = str(e)
        if data["direction"] == "OUTPUT":
            data["verdict"] = f"Pin is configured as OUTPUT — driven {'HIGH' if data['value'] else 'LOW'}"
        elif data["value"] == 1:
            data["verdict"] = "Pin is HIGH — signal present or pull-up active"
        elif data["value"] == 0:
            data["verdict"] = "Pin is LOW — check wiring if expecting a signal here"
        else:
            data["verdict"] = "Could not read pin state"
        if data["consumer"]:
            data["verdict"] += f" · In use by: {data['consumer']}"
        return jsonify({"success": True, "data": data})
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})

@app.route("/api/gpio/all")
def api_gpio_all():
    return jsonify({
        "gpio_in_use": get_gpio_in_use(),
        "timestamp": time.time()
    })

@app.route("/api/device/restart")
def api_device_restart():
    def do_restart():
        time.sleep(2)
        subprocess.run(["sudo", "reboot"])
    threading.Thread(target=do_restart, daemon=True).start()
    return jsonify({"success": True, "message": "Restarting in 2 seconds..."})

@app.route("/api/device/shutdown")
def api_device_shutdown():
    def do_shutdown():
        time.sleep(2)
        subprocess.run(["sudo", "shutdown", "-h", "now"])
    threading.Thread(target=do_shutdown, daemon=True).start()
    return jsonify({"success": True, "message": "Shutting down in 2 seconds..."})

@app.route("/api/weather")
def api_weather():
    if not weather_cache.get("data"):
        return jsonify({"error": weather_cache.get("error", "Not yet loaded")}), 503
    return jsonify(weather_cache["data"])

@app.route("/api/epa")
def api_epa():
    if not epa_cache.get("data"):
        return jsonify({"error": epa_cache.get("error", "Not yet loaded")}), 503
    return jsonify(epa_cache["data"])


@app.route("/api/network/tile")
def api_network_tile():
    result = {}
    # Pi-hole
    try:
        summary = pihole_get_fresh("stats/summary")
        blocking_raw = pihole_get_fresh("dns/blocking")
        if summary:
            result["pihole"] = {
                "online": True,
                "queries_today": summary.get("queries", {}).get("total", 0),
                "blocked_today": summary.get("queries", {}).get("blocked", 0),
                "block_pct": round(summary.get("queries", {}).get("percent_blocked", 0), 1),
                "blocking": blocking_raw.get("blocking") in (True, "enabled") if blocking_raw else False,
            }
        else:
            result["pihole"] = {"online": False}
    except Exception as e:
        result["pihole"] = {"online": False, "error": str(e)}
    # CrowdSec
    try:
        r = subprocess.run(["sudo", "cscli", "decisions", "list", "-o", "json"],
                           capture_output=True, text=True, timeout=10)
        decisions = json.loads(r.stdout) if r.stdout.strip() and r.stdout.strip() != "null" else []
        result["crowdsec"] = {"bans": len(decisions or [])}
    except Exception as e:
        result["crowdsec"] = {"bans": 0, "error": str(e)}
    # Devices
    try:
        r = subprocess.run(
            ["sudo", "arp-scan", "--localnet", "--ignoredups",
             "--ouifile=/usr/share/arp-scan/ieee-oui.txt"],
            capture_output=True, text=True, timeout=15
        )
        count = sum(1 for line in r.stdout.splitlines()
                    if len(line.split("	")) >= 3 and line.split("	")[0].count(".") == 3)
        result["devices"] = {"count": count}
    except Exception as e:
        result["devices"] = {"count": 0, "error": str(e)}
    return jsonify(result)

@app.route("/api/gpio_debug")
def gpio_debug():
    in_use = get_gpio_in_use()
    gpioinfo = subprocess.run(["gpioinfo"], capture_output=True, text=True).stdout
    sysfs = os.listdir("/sys/class/gpio") if os.path.exists("/sys/class/gpio") else []
    return jsonify({"gpio_in_use": in_use, "sysfs": sysfs, "gpioinfo": gpioinfo[:2000]})


# ─── NETWORK HUB AUTH ──────────────────────────────────────────────────────────

from functools import wraps

def require_network_auth(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get('network_auth'):
            return redirect(url_for('network_login'))
        return f(*args, **kwargs)
    return decorated

@app.route("/network/login", methods=["GET", "POST"])
def network_login():
    error = None
    if request.method == "POST":
        pw = request.form.get("password", "")
        if NETWORK_HUB_PASSWORD_HASH and check_password_hash(NETWORK_HUB_PASSWORD_HASH, pw):
            session.permanent = True
            session['network_auth'] = True
            return redirect(url_for('network'))
        error = "Invalid password"
    return render_template("network_login.html", error=error)

@app.route("/network/logout")
def network_logout():
    session.pop('network_auth', None)
    return redirect(url_for('network_login'))


# ─── NETWORK ROUTES ────────────────────────────────────────────────────────────

# Cache Pi-hole SID to avoid hammering the auth endpoint (rate-limited)
_pihole_sid = None
_pihole_sid_ts = 0
_PIHOLE_SID_TTL = 300  # re-auth every 5 minutes max

def pihole_auth():
    global _pihole_sid, _pihole_sid_ts
    now = time.time()
    if _pihole_sid and (now - _pihole_sid_ts) < _PIHOLE_SID_TTL:
        return _pihole_sid
    try:
        import urllib.request as ur, json as js
        payload = js.dumps({"password": PIHOLE_PASSWORD}).encode()
        req = ur.Request("http://localhost/api/auth", data=payload,
                         headers={"Content-Type": "application/json"}, method="POST")
        with ur.urlopen(req, timeout=5) as resp:
            data = js.loads(resp.read())
            sid = data.get("session", {}).get("sid")
            if sid:
                _pihole_sid = sid
                _pihole_sid_ts = now
            return sid
    except Exception:
        return None

def pihole_get(path, sid):
    import urllib.request as ur, json as js
    req = ur.Request(f"http://localhost/api/{path}",
                     headers={"X-FTL-SID": sid})
    with ur.urlopen(req, timeout=5) as resp:
        return js.loads(resp.read())

def pihole_get_fresh(path):
    """Auth + GET in one call, invalidating cache on 401."""
    global _pihole_sid, _pihole_sid_ts
    import urllib.request as ur, json as js
    from urllib.error import HTTPError
    sid = pihole_auth()
    if not sid:
        return None
    try:
        req = ur.Request(f"http://localhost/api/{path}", headers={"X-FTL-SID": sid})
        with ur.urlopen(req, timeout=5) as resp:
            return js.loads(resp.read())
    except HTTPError as e:
        if e.code == 401:
            # SID expired — invalidate and retry once
            _pihole_sid = None
            _pihole_sid_ts = 0
            sid = pihole_auth()
            if sid:
                req = ur.Request(f"http://localhost/api/{path}", headers={"X-FTL-SID": sid})
                with ur.urlopen(req, timeout=5) as resp:
                    return js.loads(resp.read())
        raise

@app.route("/network")
@require_network_auth
def network():
    return render_template("network.html")

@app.route("/api/network/pihole")
@require_network_auth
def api_network_pihole():
    try:
        summary      = pihole_get_fresh("stats/summary")
        top_blocked_raw = pihole_get_fresh("stats/top_domains?blocked=true&count=5")
        history_raw  = pihole_get_fresh("history")
        blocking_raw = pihole_get_fresh("dns/blocking")
        if summary is None:
            return jsonify({"error": "Auth failed", "online": False})

        history_points = history_raw.get("history", [])
        hourly = [0] * 24
        now_ts = time.time()
        for point in history_points:
            ts = point.get("timestamp", 0)
            count = point.get("total", 0)
            hours_ago = int((now_ts - ts) / 3600)
            if 0 <= hours_ago < 24:
                idx = 23 - hours_ago
                hourly[idx] += count

        top_blocked = []
        for domain, count in (top_blocked_raw.get("top_blocked", {}) or {}).items():
            top_blocked.append({"domain": domain, "count": count})
        top_blocked = sorted(top_blocked, key=lambda x: x["count"], reverse=True)[:5]

        return jsonify({
            "online": True,
            "queries_today": summary.get("queries", {}).get("total", 0),
            "blocked_today": summary.get("queries", {}).get("blocked", 0),
            "block_pct": round(summary.get("queries", {}).get("percent_blocked", 0), 1),
            "domains_on_list": summary.get("gravity", {}).get("domains_being_blocked", 0),
            "blocking": blocking_raw.get("blocking") in (True, "enabled"),
            "top_blocked": top_blocked,
            "history": hourly,
        })
    except Exception as e:
        return jsonify({"error": str(e), "online": False})

@app.route("/api/network/pihole/toggle", methods=["POST"])
@require_network_auth
def api_network_pihole_toggle():
    import urllib.request as ur, json as js
    global _pihole_sid, _pihole_sid_ts
    try:
        data = request.get_json()
        blocking = data.get("blocking", True)
        sid = pihole_auth()
        if not sid:
            return jsonify({"error": "Auth failed"}), 500
        payload = js.dumps({"blocking": "enabled" if blocking else "disabled"}).encode()
        req = ur.Request("http://localhost/api/dns/blocking", data=payload,
                         headers={"Content-Type": "application/json", "X-FTL-SID": sid},
                         method="POST")
        with ur.urlopen(req, timeout=5) as resp:
            result = js.loads(resp.read())
            _pihole_sid = None
            _pihole_sid_ts = 0
            new_state = result.get("blocking") in (True, "enabled")
            return jsonify({"ok": True, "blocking": new_state})
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/network/dns/log")
@require_network_auth
def api_network_dns_log():
    try:
        raw = pihole_get_fresh("queries?count=100")
        if raw is None:
            return jsonify({"error": "Auth failed", "queries": []})
        queries = []
        status_map = {
            "GRAVITY": ("blocked", "Blocklist"),
            "FORWARDED": ("allowed", "Forwarded"),
            "CACHE": ("cached", "Cache"),
            "CACHE_STALE": ("cached", "Cache (stale)"),
            "GRAVITY_CNAME": ("blocked", "Blocklist (CNAME)"),
            "REGEX_PI": ("blocked", "Regex"),
            "DENYLIST_PI": ("blocked", "Denylist"),
            "DENYLIST_CNAME": ("blocked", "Denylist (CNAME)"),
            "NODATA": ("allowed", "No data"),
            "NXDOMAIN": ("allowed", "NXDOMAIN"),
            "RETRIED": ("allowed", "Retried"),
            "IN_PROGRESS": ("allowed", "In progress"),
            "DBBUSY": ("allowed", "DB busy"),
            "EXTERNAL_BLOCKED_IP": ("blocked", "External block"),
            "EXTERNAL_BLOCKED_NULL": ("blocked", "External block"),
            "EXTERNAL_BLOCKED_NXRA": ("blocked", "External block"),
        }
        for q in raw.get("queries", []):
            status_raw = q.get("status", "FORWARDED")
            category, label = status_map.get(status_raw, ("allowed", status_raw))
            client = q.get("client") or {}
            client_ip = client.get("ip") or "unknown"
            client_name = client.get("name") or ""
            queries.append({
                "time": q.get("time", 0),
                "client": client_name if client_name else client_ip,
                "client_ip": client_ip,
                "domain": q.get("domain", ""),
                "type": q.get("type", "A"),
                "status": category,
                "status_label": label,
            })
        return jsonify({"queries": queries})
    except Exception as e:
        return jsonify({"error": str(e), "queries": []})

@app.route("/api/network/dns/clients")
@require_network_auth
def api_network_dns_clients():
    try:
        raw = pihole_get_fresh("stats/top_clients?count=20")
        if raw is None:
            return jsonify({"error": "Auth failed", "clients": []})
        clients = []
        for entry in raw.get("top_clients", []):
            clients.append({
                "ip": entry.get("ip", entry.get("name", "unknown")),
                "name": entry.get("name", ""),
                "count": entry.get("count", 0),
            })
        return jsonify({"clients": clients})
    except Exception as e:
        return jsonify({"error": str(e), "clients": []})

@app.route("/api/network/devices/scan")
@require_network_auth
def api_network_devices_scan():
    try:
        r = subprocess.run(
            ["sudo", "arp-scan", "--localnet", "--ignoredups",
             "--ouifile=/usr/share/arp-scan/ieee-oui.txt"],
            capture_output=True, text=True, timeout=15
        )
        devices = []
        for line in r.stdout.splitlines():
            parts = line.split("\t")
            if len(parts) >= 3 and parts[0].count(".") == 3:
                ip = parts[0].strip()
                mac = parts[1].strip()
                vendor = parts[2].strip() if parts[2].strip() else "Unknown"
                if vendor.startswith("(Unknown"):
                    vendor = "Unknown"
                devices.append({"ip": ip, "mac": mac, "vendor": vendor})
        devices.sort(key=lambda x: [int(p) for p in x["ip"].split(".")])
        return jsonify({"devices": devices, "count": len(devices)})
    except Exception as e:
        return jsonify({"error": str(e), "devices": []})

@app.route("/api/network/bandwidth")
@require_network_auth
def api_network_bandwidth():
    try:
        r = subprocess.run(["vnstat", "--json"], capture_output=True, text=True, timeout=5)
        data = json.loads(r.stdout)
        interfaces = data.get("interfaces", [])
        eth = next((i for i in interfaces if i["name"] == "eth0"), None)
        if not eth:
            eth = interfaces[0] if interfaces else None
        if not eth:
            return jsonify({"error": "No interface data"})

        def fmt(b):
            if b >= 1e9: return f"{b/1e9:.2f} GB"
            if b >= 1e6: return f"{b/1e6:.1f} MB"
            if b >= 1e3: return f"{b/1e3:.0f} KB"
            return f"{b} B"

        traffic = eth.get("traffic", {})
        today = traffic.get("day", [{}])[-1] if traffic.get("day") else {}
        month = traffic.get("month", [{}])[-1] if traffic.get("month") else {}
        hours = traffic.get("hour", [])[-24:]

        hourly_rx = [h.get("rx", 0) for h in hours]
        hourly_tx = [h.get("tx", 0) for h in hours]

        return jsonify({
            "interface": eth["name"],
            "today_rx": fmt(today.get("rx", 0)),
            "today_tx": fmt(today.get("tx", 0)),
            "month_rx": fmt(month.get("rx", 0)),
            "month_tx": fmt(month.get("tx", 0)),
            "hourly_rx": hourly_rx,
            "hourly_tx": hourly_tx,
        })
    except Exception as e:
        return jsonify({"error": str(e)})

@app.route("/api/network/crowdsec")
@require_network_auth
def api_network_crowdsec():
    try:
        r = subprocess.run(
            ["sudo", "cscli", "decisions", "list", "-o", "json"],
            capture_output=True, text=True, timeout=10
        )
        decisions = json.loads(r.stdout) if r.stdout.strip() and r.stdout.strip() != "null" else []
        bans = []
        for d in (decisions or []):
            bans.append({
                "id": d.get("id"),
                "ip": d.get("value", ""),
                "reason": d.get("scenario", d.get("reason", "")),
                "origin": d.get("origin", ""),
                "duration": d.get("duration", ""),
                "type": d.get("type", "ban"),
            })
        return jsonify({"bans": bans, "count": len(bans)})
    except Exception as e:
        return jsonify({"error": str(e), "bans": [], "count": 0})

@app.route("/api/network/crowdsec/alerts")
@require_network_auth
def api_network_crowdsec_alerts():
    try:
        r = subprocess.run(
            ["sudo", "cscli", "alerts", "list", "-o", "json"],
            capture_output=True, text=True, timeout=10
        )
        alerts_raw = json.loads(r.stdout) if r.stdout.strip() and r.stdout.strip() != "null" else []
        alerts = []
        for a in (alerts_raw or [])[:50]:
            alerts.append({
                "id": a.get("id"),
                "scenario": a.get("scenario", ""),
                "ip": a.get("source", {}).get("ip", ""),
                "country": a.get("source", {}).get("cn", ""),
                "timestamp": a.get("startAt", ""),
                "decisions": len(a.get("decisions", [])),
            })
        return jsonify({"alerts": alerts})
    except Exception as e:
        return jsonify({"error": str(e), "alerts": []})

@app.route("/api/network/services")
@require_network_auth
def api_network_services():
    import urllib.request as ur, json as js
    result = {
        "jellyfin": {"online": False},
        "immich": {"online": False},
    }

    try:
        req = ur.Request("http://100.82.77.13:8096/System/Info",
                         headers={"X-Emby-Token": JELLYFIN_API_KEY})
        with ur.urlopen(req, timeout=5) as resp:
            info = js.loads(resp.read())
        req2 = ur.Request(f"http://100.82.77.13:8096/Sessions?api_key={JELLYFIN_API_KEY}")
        with ur.urlopen(req2, timeout=5) as resp2:
            sessions = js.loads(resp2.read())
            active_streams = len([s for s in sessions if s.get("NowPlayingItem")])
        req3 = ur.Request(
            f"http://100.82.77.13:8096/Items?IncludeItemTypes=Movie,Series&Recursive=true&api_key={JELLYFIN_API_KEY}"
        )
        with ur.urlopen(req3, timeout=5) as resp3:
            lib = js.loads(resp3.read())
            library_count = lib.get("TotalRecordCount", 0)
        req4 = ur.Request(
            f"http://100.82.77.13:8096/Items?SortBy=DateCreated&SortOrder=Descending&Limit=1&Recursive=true&api_key={JELLYFIN_API_KEY}"
        )
        with ur.urlopen(req4, timeout=5) as resp4:
            recent = js.loads(resp4.read())
            items = recent.get("Items", [])
            last_added = items[0].get("Name", "—") if items else "—"
        result["jellyfin"] = {
            "online": True,
            "name": info.get("ServerName", "Jellyfin"),
            "version": info.get("Version", ""),
            "active_streams": active_streams,
            "library_count": library_count,
            "last_added": last_added,
        }
    except Exception as e:
        result["jellyfin"]["error"] = str(e)

    try:
        req = ur.Request("http://100.102.210.39:2283/api/server/statistics",
                         headers={"x-api-key": IMMICH_API_KEY})
        with ur.urlopen(req, timeout=5) as resp:
            stats = js.loads(resp.read())
        req2 = ur.Request("http://100.102.210.39:2283/api/assets?order=desc&size=1&page=1",
                          headers={"x-api-key": IMMICH_API_KEY})
        with ur.urlopen(req2, timeout=5) as resp2:
            assets = js.loads(resp2.read())
            last_asset = assets[0] if assets else None
            last_backup = last_asset.get("fileCreatedAt", "—")[:10] if last_asset else "—"
        usage_bytes = stats.get("usage", 0)
        usage_str = f"{usage_bytes/1e9:.1f} GB" if usage_bytes > 1e9 else f"{usage_bytes/1e6:.0f} MB"
        result["immich"] = {
            "online": True,
            "photos": stats.get("photos", 0),
            "videos": stats.get("videos", 0),
            "usage": usage_str,
            "last_backup": last_backup,
        }
    except Exception as e:
        result["immich"]["error"] = str(e)

    return jsonify(result)

@app.route("/api/network/nodes")
@require_network_auth
def api_network_nodes():
    nodes = {
        "pi":     {"label": "Pi",     "host": "127.0.0.1"},
        "msi":    {"label": "MSI",    "host": "100.82.77.13"},
        "lenovo": {"label": "Lenovo", "host": "100.102.210.39"},
    }
    result = {}
    for key, node in nodes.items():
        try:
            r = subprocess.run(
                ["ping", "-c", "1", "-W", "1", node["host"]],
                capture_output=True, text=True, timeout=3
            )
            online = r.returncode == 0
            latency = None
            if online:
                m = re.search(r"time=([\d.]+)", r.stdout)
                if m:
                    latency = round(float(m.group(1)), 1)
            result[key] = {"label": node["label"], "online": online, "latency_ms": latency}
        except Exception as e:
            result[key] = {"label": node["label"], "online": False, "latency_ms": None}
    return jsonify(result)



@app.route('/api/live/stream/<machine>')
def live_stream(machine):
    hosts = {'msi': '192.168.1.107', 'lenovo': '100.102.210.39'}
    if machine not in hosts:
        return jsonify({'error': 'unknown machine'}), 400
    try:
        upstream = urllib.request.urlopen(
            urllib.request.Request(f'http://{hosts[machine]}:8080/stream'),
            timeout=5
        )
    except Exception:
        return '', 503
    def generate(resp):
        try:
            with resp:
                while True:
                    chunk = resp.read(4096)
                    if not chunk:
                        break
                    yield chunk
        except Exception:
            return
    return Response(generate(upstream), mimetype='multipart/x-mixed-replace; boundary=frame')

@app.route('/live')
def live():
    return render_template('live.html')

@app.route('/api/live/mic/<machine>/status')
def live_mic_status(machine):
    hosts = {'msi': '192.168.1.107', 'lenovo': '100.102.210.39'}
    if machine not in hosts:
        return jsonify({'error': 'unknown machine'}), 400
    try:
        req = urllib.request.Request(f'http://{hosts[machine]}:8080/mic/status')
        with urllib.request.urlopen(req, timeout=3) as resp:
            return jsonify(json.loads(resp.read()))
    except Exception:
        return jsonify({'muted': None, 'offline': True}), 503

@app.route('/api/live/mic/<machine>/toggle', methods=['POST'])
def live_mic_toggle(machine):
    hosts = {'msi': '192.168.1.107', 'lenovo': '100.102.210.39'}
    if machine not in hosts:
        return jsonify({'error': 'unknown machine'}), 400
    try:
        req = urllib.request.Request(
            f'http://{hosts[machine]}:8080/mic/toggle',
            data=b'', method='POST'
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            return jsonify(json.loads(resp.read()))
    except Exception as e:
        return jsonify({'error': str(e)}), 503


# --- Singularity (runs on Mac at 192.168.1.102:5004) ---

@app.route('/api/launch/singularity', methods=['POST'])
def launch_singularity():
    return {'url': 'http://192.168.1.102:5004'}, 200

@app.route('/api/kill/singularity', methods=['POST'])
def kill_singularity():
    return {}, 200

if __name__ == "__main__":
    app.config["TEMPLATES_AUTO_RELOAD"] = True
    app.run(host="0.0.0.0", port=5000, debug=False)
from flask import Flask, Response, jsonify
import cv2, time
from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
from ctypes import cast, POINTER
import comtypes

app = Flask(__name__)
camera = cv2.VideoCapture(0, cv2.CAP_MSMF)
camera.set(cv2.CAP_PROP_FRAME_WIDTH, 640)
camera.set(cv2.CAP_PROP_FRAME_HEIGHT, 480)
time.sleep(2)

def get_mic_volume():
    comtypes.CoInitialize()
    devices = AudioUtilities.GetMicrophone()
    interface = devices.Activate(IAudioEndpointVolume._iid_, comtypes.CLSCTX_ALL, None)
    return cast(interface, POINTER(IAudioEndpointVolume))

def generate_frames():
    while True:
        ret, frame = camera.read()
        if not ret:
            continue
        _, buffer = cv2.imencode(".jpg", frame, [cv2.IMWRITE_JPEG_QUALITY, 70])
        yield (b"--frame\r\nContent-Type: image/jpeg\r\n\r\n" + buffer.tobytes() + b"\r\n")

@app.route("/stream")
def stream():
    return Response(generate_frames(), mimetype="multipart/x-mixed-replace; boundary=frame")

@app.route("/mic/status")
def mic_status():
    try:
        return jsonify({"muted": bool(get_mic_volume().GetMute())})
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/mic/toggle", methods=["POST"])
def mic_toggle():
    try:
        vol = get_mic_volume()
        current = vol.GetMute()
        vol.SetMute(not current, None)
        return jsonify({"muted": not current})
    except Exception as e:
        return jsonify({"error": str(e)}), 500

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8080)

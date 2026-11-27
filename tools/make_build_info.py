"""build_info.py(버전 · Google 로그인 정보 · 업데이트 저장소)를 만들어요.

내 컴퓨터에서 설치 파일을 만들 때 build_installer.bat이 불러요.
- Google 로그인: build_secrets.json의 값, 없으면 이 폴더에 넣은 client_secret_….json(Google Cloud에서 받은 파일)을 써요.
- 둘 다 없으면 Google 로그인 없이 만들어요. (연결 코드 방식과 iCloud는 그대로 돼요)
"""
import json
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
path = root / "build_secrets.json"
data = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
if not data.get("version"):
    found = re.search(r'VERSION = getattr\(_build, "VERSION", "(\d+\.\d+\.\d+)"\)',
                      (root / "calendar_widget.py").read_text(encoding="utf-8"))
    data["version"] = found.group(1) if found else "2.0.0"
version = str(data["version"]).strip()
if not re.fullmatch(r"\d+\.\d+\.\d+", version):
    sys.exit("version은 2.0.0 처럼 적어 주세요.")

client_id = str(data.get("google_client_id", "")).strip()
client_secret = str(data.get("google_client_secret", "")).strip()
source = "build_secrets.json" if client_id else ""
if not client_id:
    for file in sorted(root.glob("client_secret*.json")):
        try:
            info = json.loads(file.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if "installed" in info and info["installed"].get("client_id"):
            client_id = info["installed"]["client_id"]
            client_secret = info["installed"].get("client_secret", "")
            source = file.name
            break
        if "web" in info:
            print(f"  [!] {file.name}은 '웹 애플리케이션'용이에요. Google Cloud에서 '데스크톱 앱'으로 다시 만들어 주세요.")
update_repo = str(data.get("update_repo", "")).strip()

lines = [
    f"VERSION = {version!r}",
    f"GOOGLE_CLIENT_ID = {client_id!r}",
    f"GOOGLE_CLIENT_SECRET = {client_secret!r}",
    f"UPDATE_REPO = {update_repo!r}",
]
(root / "build_info.py").write_text("\n".join(lines) + "\n", encoding="utf-8")
(root / "build_version.txt").write_text(version, encoding="ascii")
print(f"  버전: {version}")
print(f"  Google 로그인: {'넣어요 (' + source + ')' if client_id else '빼요. Google Cloud에서 받은 client_secret JSON 파일을 이 폴더에 넣으면 들어가요'}")
print(f"  자동 업데이트: {'넣어요 (' + update_repo + ')' if update_repo else '빼요'}")

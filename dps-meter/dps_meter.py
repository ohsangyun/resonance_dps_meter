#!/usr/bin/env python3
"""레조넌스 딜 미터: 실행 중인 게임의 전투 상태를 읽어 피해·비용·손패·버프를 기록하고 보여 준다.

게임 메모리는 읽기만 한다 (PROCESS_QUERY_INFORMATION | PROCESS_VM_READ).
쓰기·코드 주입·게임 파일 변경은 하지 않으며, 읽기가 막히면 오류를 표시하고 멈춘다.

자동 사용 설정은 레지스트리(Unity PlayerPrefs)에서 역시 읽기만 한다.
육성 정보는 이번 전투에 실제로 들어간 메모리 값만 쓴다. 로그인 때 한 번 찍히는 Player.log 는 그 뒤의 변경을 모르므로 쓰지 않는다.

전투는 메모리 스캔 없이 정적 경로로만 찾는다.
  BuffBase 정적 필드 +0x18 = BattleControlManager → TeamData → BattleData → BattleResult
게임이 업데이트되면 RVA 를 다시 뽑아야 한다. 시작할 때 클래스 이름으로 검증한다.

기록의 시간축은 전부 게임 프레임이다 (t = frame/60, 게임 타이머 기준. 시뮬 시각+3초≈게임 시각).
비용과 속성의 SN 은 값 x 10000 이다.

사용법
  딜미터.pyw 더블클릭                           창 띄우기 (항상 위, 이미 켜져 있으면 창만 다시 연다)
  python dps-meter/dps_meter.py --no-window     서버만 실행
  python dps-meter/dps_meter.py --check         지금 전투 상태를 한 번 출력
"""
import argparse
import base64
import collections
import ctypes
import ctypes.wintypes as W
import gzip
import hashlib
import json
import math
import os
import re
import struct
import subprocess
import sys
import threading
import time
import types
import urllib.error
import urllib.request
import webbrowser
import winreg
import zlib
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def main_checkout(root):
    """git 작업 폴더(worktree)에서 켰으면 원래 저장소 폴더를, 아니면 root 를 돌려준다."""
    try:
        marker = (root / ".git").read_text(encoding="utf-8").strip()  # 작업 폴더의 .git 은 "gitdir: ..." 한 줄짜리 파일
        if marker.startswith("gitdir:"):
            gitdir = (root / marker[len("gitdir:"):].strip()).resolve()
            common = (gitdir / (gitdir / "commondir").read_text(encoding="utf-8").strip()).resolve()
            if common.name == ".git":
                return common.parent
    except OSError:
        pass  # 원래 저장소 폴더라 .git 이 폴더이거나, git 밖에 있다.
    return root


def asset_dir(*parts):
    """git 에 없는 그림 폴더(web/img). 작업 폴더에는 없으므로 원래 저장소 폴더에서도 찾는다."""
    for base in (ROOT, main_checkout(ROOT)):
        if base.joinpath(*parts).is_dir():
            return base.joinpath(*parts)
    return ROOT.joinpath(*parts)


GAME_DATA = ROOT / "web" / "data" / "game.js"
ROSTER_DATA = ROOT / "data" / "kr_roster.json"
EXTRA_DATA = HERE / "extra_names.json"
DEFAULT_LOG_DIR = HERE / "logs"
ICON_FILE = HERE / "icon.png"
PORTRAIT_DIR = asset_dir("web", "img", "unit")
PORTRAIT_PATH = re.compile(r"/unit/([0-9]{1,12})\.webp")
EQUIP_ICON_DIR = asset_dir("web", "img", "equip")
EXTRA_IMAGE_DIR = HERE / "img"
EQUIP_ICON_PATH = re.compile(r"/equip/([0-9]{1,12})\.webp")
APPDIR = Path(os.environ.get("LOCALAPPDATA", Path.home())) / "ResonanceDpsMeter"
# 자료 묶음 (2026-11-23): 배포 묶음은 초상화·장비 아이콘과 이름 자료(game.js·kr_roster.json)를 폴더 대신 파일 하나(assets.pak)에 가려서 넣는다
#   (tools/build_meter_dist.py 가 만듦).
#   형식: ASSET_PACK_MAGIC + 소금 16바이트 + 목차 길이 4바이트(리틀 엔디언) + 가린 목차(json: 이름 → [위치, 길이]) + 가린 내용들.
#   이름: 그림 "unit/<id>"·"equip/<id>"(webp), 이름 자료 "data/game.js"·"data/kr_roster.json"(zlib 으로 누른 것).
#   가리기 = SHAKE-256(키 + 소금 + 이름)으로 뽑은 바이트와 XOR. 키가 이 파일에 있으니 암호가 아니라 눈가림이다:
#   폴더를 열어 내용을 바로 보거나 통째로 가져가지 못하게 하는 정도이고, 이 코드를 읽는 사람은 풀 수 있다.
#   이 파일이 있으면 그림은 여기서만 읽고, 없으면(저장소에서 켤 때) web/img·web/data·data 폴더에서 읽는다.
ASSET_PACK = HERE / "assets.pak"
ASSET_PACK_MAGIC = b"RSMP1"
ASSET_PACK_KEY = b"b6cc60911180c260f6c7f738f7e17879462b5aa7acfa1c39"
# 서버 전송 (2026-11-23): 화면의 '서버 전송' 버튼이 끝난 전투의 기록 파일을 gzip 으로 묶어 기록 받는 서버(log_server.py)에 보낸다.
#   주소·키는 --upload-url/--upload-key > 이 폴더의 upload.json(배포 묶음이 적어 둠) > 기본값 순서. 보낸 기록 파일 이름은 SENT_FILE 에 남긴다.
DEFAULT_UPLOAD_URL = "https://resonance.sayuu.is-a.dev/meter/upload"
UPLOAD_CONFIG = HERE / "upload.json"
SENT_FILE = APPDIR / "sent.json"
UPLOAD = {"url": DEFAULT_UPLOAD_URL, "key": ""}
# 서버 정보 표 (2026-11-16): 서버마다 실행 파일 이름·Unity PlayerPrefs 레지스트리 키·클래스 주소표(RVA)가 다르다.
#   켜져 있는 게임의 실행 파일 이름으로 서버를 가리고(find_pid), 그 서버의 값으로 아래 전역(PROCESS_NAME·GAME_PREFS_KEY·RVA)을 맞춘다(use_server).
#   기록에는 서버 번호(server)와 게임 빌드(build)를 적는다 — 여러 사람·여러 서버의 기록을 한데 모아도 가릴 수 있게.
#   주소표는 그 서버 설치본을 Il2CppDumper 로 풀어야 나온다 (script.json 의 Battle.<클래스>_TypeInfo).
#   build 는 주소표를 뽑은 GameAssembly.dll 의 빌드 표시다: 켜진 게임의 것과 다르면 주소표가 낡은 것이라 읽지 않고 "버전 불일치"로 멈춘다.
#   일섭·중섭(2026-11-18)의 주소표·레지스트리 키는 설치본에서 뽑았고, 미터가 읽는 클래스의 칸 배치는 한섭과 같다(Unity 2019.4.40f1, 메타데이터 24 도 같음).
#   켠 게임에서 확인: 한섭(11-16), 일섭(11-23 — 붙기·빌드 확인·기록 저장). 중섭은 설치본 대조뿐이다 [미확인] (창에 따로 표시하지는 않는다 — 11-23 사용자 결정).
SERVERS = {
    "kr": {"name": "한섭", "process": "레조넌스.exe", "prefs": "Software\\临界\\레조넌스",
           "build": {"timeDateStamp": 1776070607, "sizeOfImage": 0x48E7000},
           "rva": {"BattleResult": 0x4411848, "RoleInfo": 0x4411168, "BattleSkillInfo": 0x4411120,
                   "BuffBase": 0x440F918, "TeamData": 0x4411AA8}},
    "jp": {"name": "일섭", "process": "レゾナンス：無限号列車.exe", "prefs": "Software\\临界\\レゾナンス：無限号列車",
           "build": {"timeDateStamp": 1769157010, "sizeOfImage": 0x4818000},
           "rva": {"BattleResult": 0x40B5010, "RoleInfo": 0x40B4928, "BattleSkillInfo": 0x40B48E0,
                   "BuffBase": 0x40B30D8, "TeamData": 0x40B5260}},
    "cn": {"name": "중섭", "process": "雷索纳斯.exe", "prefs": "Software\\游戏公国\\雷索纳斯",
           "build": {"timeDateStamp": 1768366301, "sizeOfImage": 0x47A5000},
           "rva": {"BattleResult": 0x404C170, "RoleInfo": 0x404BA88, "BattleSkillInfo": 0x404BA40,
                   "BuffBase": 0x404A238, "TeamData": 0x404C3B8}},
}
SERVER = "kr"  # 지금 붙은(또는 마지막으로 찾은) 게임의 서버
GAME_PREFS_KEY = SERVERS[SERVER]["prefs"]
# 값 이름 앞부분은 계정 식별자다. 뒤쪽 키만 쓰고 이름 전체는 어디에도 남기지 않는다.
PREFS_NAME = re.compile(r"^.*?(CardAIData|CardAIOn|CardAIBan)(.*?)_h\d+$")
PROCESS_NAME = SERVERS[SERVER]["process"]
WINDOW_TITLE = "레조넌스 딜 미터"

RVA = SERVERS[SERVER]["rva"]


def pack_mask(data, salt, name):
    """자료 묶음의 가리기·풀기 (XOR 이라 같은 함수)."""
    stream = hashlib.shake_256(ASSET_PACK_KEY + salt + name.encode("utf-8")).digest(len(data))
    return (int.from_bytes(data, "little") ^ int.from_bytes(stream, "little")).to_bytes(len(data), "little")


class AssetPack:
    """자료 묶음 읽기. 파일이 없거나 모양이 다르면 load 가 None 을 돌려준다."""

    def __init__(self, blob, salt, index):
        self.blob, self.salt, self.index = blob, salt, index

    @classmethod
    def load(cls, path=ASSET_PACK):
        try:
            blob = path.read_bytes()
            head = len(ASSET_PACK_MAGIC)
            if blob[:head] != ASSET_PACK_MAGIC:
                return None
            salt = blob[head:head + 16]
            size = int.from_bytes(blob[head + 16:head + 20], "little")
            index = json.loads(pack_mask(blob[head + 20:head + 20 + size], salt, "").decode("utf-8"))
            return cls(blob, salt, {str(name): (int(at), int(length)) for name, (at, length) in index.items()})
        except (OSError, ValueError, TypeError):
            return None

    def get(self, name):
        at, length = self.index.get(name, (0, 0))
        return pack_mask(self.blob[at:at + length], self.salt, name) if length else None


ASSETS = AssetPack.load()


def read_data(path, name):
    """이름 자료를 글로 읽는다: 자료 묶음에 있으면 거기서, 없으면 저장소의 파일에서."""
    packed = ASSETS.get(name) if ASSETS else None
    if not packed:
        return path.read_text(encoding="utf-8")
    try:
        return zlib.decompress(packed).decode("utf-8")
    except zlib.error as exc:
        raise ValueError(f"자료 묶음의 {name} 을 풀지 못했습니다: {exc}")


def use_server(server):
    """지금 붙을 게임의 서버를 고른다 (실행 파일 이름·레지스트리 키·주소표를 그 서버 것으로)."""
    global SERVER, PROCESS_NAME, GAME_PREFS_KEY, RVA
    info = SERVERS[server]
    SERVER, PROCESS_NAME, GAME_PREFS_KEY, RVA = server, info["process"], info["prefs"], info["rva"]


STATE_NAMES = {4: "전투 중", 3: "전투 시작 대기", 5: "대열 정비", 6: "팀 카드 선택", 7: "이동 중",
               8: "승리 연출", 1: "전투 종료"}

SCHEMA_VERSION = 5  # 3: cards[].target/pos/ai, ops, snapshots 유닛 pos 추가. 4: 게임 프레임마다 표본, hits/actions/dotTicks 추가. 5: server(서버 번호)·build(게임 빌드) 추가
POLL_HZ = 60  # 게임 프레임(초당 60)이 바뀔 때마다 한 번 읽는다
FRAME_SLEEP = 0.002  # 프레임이 바뀌었는지 보는 간격
RECHECK_SECONDS = 0.05  # 프레임이 멈춰 있을 때(일시정지·종료 직후) 다시 읽는 간격
DOT_MOD = "周期效果"  # 주기 효과(지속 피해 등). 틱 시점을 프레임 단위로 기록한다
OPERATION_SIZE = 0x50  # Replay.OperationLog 구조체 크기
IDLE_SECONDS = 0.25
PID_CHECK_SECONDS = 3
WINDOW_CHECK_SECONDS = 2  # 미터 창이 닫혔는지 보는 간격
STALE_SECONDS = 600
PAUSE_SECONDS = 2
FLOW_FRAMES = 6
BUFF_FRAMES = 3  # 버프 표본은 3프레임(약 0.05초)마다 — 전부 읽으면 무거워서 프레임마다 하지 않는다
SETTLE_FRAMES = 12
MAX_LINK = 1024
MAX_DICT = 4096
MAX_LIST = 1 << 20
MAX_UNITS = 256
MAX_STRING = 1024
MAX_ERRORS = 40
MAX_HISTORY = 200
BODY_CACHE = 4
LOG_TO_VIEW = 200
CARDS_TO_VIEW = 200
EVENTS_TO_VIEW = 200
SERIES_ROWS = 300
META_HEAD_CHARS = 1 << 18
META_FIELDS = ("id", "server", "started", "roles", "conditions", "cardOwners", "game_duration", "frame")
ADDRESS_MIN = 0x10000
ADDRESS_MAX = 0x7FFFFFFF0000

# 세부 스펙 (spec). 메모리 값은 전투 시작 부근에 몇 번만 읽는다.
SPEC_VERSION = 3  # 1 은 일부 필드를 Player.log 로 채우던 옛 기록이다. 3: spec.battle 에 ReplayManager 의 관문 인자(날씨 후보 등) 추가
# ReplayManager 가 InitBattle 로 받은 관문 인자 (이름, 오프셋, 형식). LevelManager.CreateWeather 가 날씨 후보를 읽는다.
# 이름은 게임 필드 이름 그대로 — 엔진 재현 시험(tests_replay.rs level_opts_from_log)이 spec.battle 에서 같은 이름으로 읽는다.
REPLAY_INIT_FIELDS = (("isBattleTest", 0x98, "bool"), ("isArena", 0x99, "bool"), ("playerTeamNO", 0x9C, "i32"),
                      ("enemyLevelMin", 0xA0, "i32"), ("difficulty", 0xA4, "i32"), ("bgId", 0xA8, "i32"), ("enemyRn", 0xAC, "i32"),
                      ("weatherList", 0xB0, "int[]"), ("weatherCount", 0xB8, "i32"), ("weatherRateSN", 0xC0, "i64"),
                      ("enemyLevelOffset", 0xC8, "i32"), ("secondWeatherList", 0xD0, "int[]"),
                      ("weatherSecondRateSN", 0xD8, "i64"), ("secondWeatherCount", 0xE0, "i32"))
REPLAY_INIT_START, REPLAY_INIT_END = 0x98, 0xE4
MAX_INT_ARRAY = 256
EQUIP_SLOTS = 3
SPEC_RETRY_TICKS = 4  # 약 0.2초마다 다시 시도
SPEC_MAX_TICKS = 1200  # 약 60초 뒤에는 포기하고 경고를 남긴다
SPEC_STRING = 8192
MAX_TEAM_UNITS = 8
MID_BATTLE_FRAMES = 600  # 이보다 늦게 기록을 시작했으면 시작 시점 값이 아니다
STATE_FIGHTING = 4
ALLY_TEAM = 1
DISCARD_CARD = 10600474
DISCARD_OWNER = 10000001
FIRST_WEIGHT, STEP_WEIGHT, BAN_WEIGHT = 900000, 10000, -9999999
DISCARD_LABELS = {1: "항상 (순위대로)", 2: "사용 안 함", 3: "쓸 수 있는 카드가 없을 때", 4: "순위가 높은 카드가 없을 때"}
# 게임이 전투에 펫 능력치를 넣는 칸: (장비 칸, 옵션 칸) → 옵션 id. 그 장비의 추가 옵션 대신 들어간다.
PET_SLOTS = {(0, 4): 12300776, (0, 5): 12300777, (1, 5): 12300771}
PET_OPTIONS = {12300776: "공격력", 12300777: "방어력", 12300771: "체력"}
# 장비 돌파로 오른 주 능력치를 전투에 넘기는 패시브 id → (장비 칸, 능력치). 값은 extraSkills 의 'id,A,오른 값' (GetRoleInfoByData).
EQUIP_BREAK_TOKENS = {12304698: (0, "Atk"), 12304699: (1, "Def"), 12304700: (2, "HpMax")}
# 미장착이거나 편성에서 끈 칸에 게임이 대신 넣는 장비 id (View_StartBattle). 3번 칸은 -1 이 들어간다.
EMPTY_EQUIP_ID = 11800220
UNIT_INFO_SIZE = 0x178
UNIT_INFO_INTS = {"id": 0x0, "unitViewId": 0x4, "skill1Lv": 0x8, "skill2Lv": 0xC, "skill3Lv": 0x10, "lv": 0x14,
                  "awakeLv": 0x18, "resonanceLv": 0x1C, "trustLv": 0x20, "card1Num": 0x158, "card2Num": 0x15C,
                  "card3Num": 0x160, "roleIndex": 0x170}
# 칸마다 간격이 달라서 산술식이 아니라 dump.cs 의 표로 읽는다: (장비 id, 레벨, 옵션 id 6개, 옵션 값 6개)
UNIT_INFO_EQUIPS = (
    (0x24, 0x28, (0x2C, 0x38, 0x48, 0x58, 0x68, 0x78), (0x30, 0x40, 0x50, 0x60, 0x70, 0x80)),
    (0x88, 0x8C, (0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0), (0x98, 0xA8, 0xB8, 0xC8, 0xD8, 0xE8)),
    (0xF0, 0xF4, (0xF8, 0x108, 0x118, 0x128, 0x138, 0x148), (0x100, 0x110, 0x120, 0x130, 0x140, 0x150)),
)
UNIT_INFO_LIMITS = {"id": (10000000, 19999999), "lv": (1, 200), "awakeLv": (0, 20), "resonanceLv": (0, 20), "trustLv": (0, 100),
                    "skill1Lv": (0, 100), "skill2Lv": (0, 100), "skill3Lv": (0, 100)}

# 포인터가 잘못되면 read 가 None 을 돌려주고, 해석하다 여기 있는 예외가 난다. 틱을 버리고 계속 돈다.
TRANSIENT = (TypeError, struct.error, KeyError, IndexError, ValueError, AttributeError)

PROCESS_QUERY_INFORMATION = 0x0400
PROCESS_VM_READ = 0x0010
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
TOKEN_QUERY = 0x0008
TOKEN_ELEVATION = 20
ERROR_ACCESS_DENIED = 5
STILL_ACTIVE = 259
TH32CS_SNAPPROCESS = 0x02
LIST_MODULES_ALL = 0x03

kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
psapi = ctypes.WinDLL("psapi", use_last_error=True)
advapi32 = ctypes.WinDLL("advapi32", use_last_error=True)


class PROCESSENTRY32W(ctypes.Structure):
    _fields_ = [("dwSize", W.DWORD), ("cntUsage", W.DWORD), ("th32ProcessID", W.DWORD),
                ("th32DefaultHeapID", ctypes.c_size_t), ("th32ModuleID", W.DWORD), ("cntThreads", W.DWORD),
                ("th32ParentProcessID", W.DWORD), ("pcPriClassBase", W.LONG), ("dwFlags", W.DWORD),
                ("szExeFile", W.WCHAR * 260)]


kernel32.OpenProcess.restype = W.HANDLE
kernel32.OpenProcess.argtypes = [W.DWORD, W.BOOL, W.DWORD]
kernel32.CloseHandle.argtypes = [W.HANDLE]
kernel32.GetExitCodeProcess.argtypes = [W.HANDLE, ctypes.POINTER(W.DWORD)]
kernel32.ReadProcessMemory.argtypes = [W.HANDLE, W.LPCVOID, W.LPVOID, ctypes.c_size_t, ctypes.POINTER(ctypes.c_size_t)]
kernel32.CreateToolhelp32Snapshot.restype = W.HANDLE
kernel32.CreateToolhelp32Snapshot.argtypes = [W.DWORD, W.DWORD]
kernel32.Process32FirstW.argtypes = [W.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
kernel32.Process32NextW.argtypes = [W.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
psapi.EnumProcessModulesEx.argtypes = [W.HANDLE, ctypes.c_void_p, W.DWORD, ctypes.POINTER(W.DWORD), W.DWORD]
psapi.GetModuleBaseNameW.argtypes = [W.HANDLE, W.HMODULE, W.LPWSTR, W.DWORD]
advapi32.OpenProcessToken.argtypes = [W.HANDLE, W.DWORD, ctypes.POINTER(W.HANDLE)]
advapi32.GetTokenInformation.argtypes = [W.HANDLE, ctypes.c_int, ctypes.c_void_p, W.DWORD, ctypes.POINTER(W.DWORD)]


def runs_elevated(pid):
    """그 프로세스가 관리자 권한으로 켜져 있는지. 토큰 정보만 본다(메모리는 읽지 않는다). 알 수 없으면 None."""
    process = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, pid)
    if not process:
        return None
    token, elevated, size = W.HANDLE(), W.DWORD(), W.DWORD()
    try:
        if not advapi32.OpenProcessToken(process, TOKEN_QUERY, ctypes.byref(token)):
            return None
        try:
            if not advapi32.GetTokenInformation(token, TOKEN_ELEVATION, ctypes.byref(elevated), ctypes.sizeof(elevated), ctypes.byref(size)):
                return None
        finally:
            kernel32.CloseHandle(token)
    finally:
        kernel32.CloseHandle(process)
    return bool(elevated.value)


def find_pid(prefer=None):
    """서버 정보 표에 있는 게임 실행 파일을 찾는다. 찾으면 그 서버로 맞추고(use_server) pid 를 돌려준다.
    prefer 는 이미 붙어 있는 게임의 pid 다: 그 게임이 살아 있으면 다른 서버의 게임이 같이 켜져 있어도 그대로 둔다."""
    by_process = {info["process"]: server for server, info in SERVERS.items()}
    snap = kernel32.CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
    entry = PROCESSENTRY32W()
    entry.dwSize = ctypes.sizeof(entry)
    found = None
    ok = kernel32.Process32FirstW(snap, ctypes.byref(entry))
    while ok:
        server = by_process.get(entry.szExeFile)
        if server and (found is None or entry.th32ProcessID == prefer):
            found = (entry.th32ProcessID, server)
            if prefer is None or entry.th32ProcessID == prefer:
                break
        ok = kernel32.Process32NextW(snap, ctypes.byref(entry))
    kernel32.CloseHandle(snap)
    if not found:
        return None
    use_server(found[1])
    return found[0]


def u64_at(data, at):
    return struct.unpack_from("<Q", data, at)[0]


def i64_at(data, at):
    return struct.unpack_from("<q", data, at)[0]


def i32_at(data, at):
    return struct.unpack_from("<i", data, at)[0]


def check_num(data, at):
    """CheckNumSN (24바이트): 값 = (+0x10 의 long) XOR (+0x0 의 long)."""
    return i64_at(data, at + 0x10) ^ i64_at(data, at)


def tdiv(a, b):
    """0 방향으로 자르는 정수 나눗셈 (C# long 나눗셈과 같다)."""
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def property_unit_value(data, at):
    """PropertyUnit.GetValueSN 역공학 결과. at 은 구조체(0x98바이트)의 시작 위치."""
    if not data[at + 0x68]:
        return check_num(data, at + 0x70)
    base = check_num(data, at + 0x08)
    percent = check_num(data, at + 0x20)
    percent_down = check_num(data, at + 0x38)
    multiplier = check_num(data, at + 0x50)
    value = tdiv((10000 + percent) * base, 10000)
    value = tdiv(value * max(10000 - percent_down, 0), 10000)
    value = tdiv(value * multiplier, 10000)
    low, high = struct.unpack_from("<qq", data, at + 0x88)
    if value < low:
        value = low
    if value > high:
        value = high
    return value


class Reader:
    """게임 프로세스의 읽기 전용 핸들."""

    def __init__(self, pid):
        self.pid = pid
        self.handle = kernel32.OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, False, pid)
        if not self.handle:
            code = ctypes.get_last_error()
            # 게임을 관리자 권한으로 켜면(2026-11-23 일섭에서 확인) 일반 권한의 미터는 열지 못한다. 우회하지 않고 이유만 알린다 (미터를 관리자 권한으로 켜면 읽힌다).
            if code == ERROR_ACCESS_DENIED and runs_elevated(pid) and not ctypes.windll.shell32.IsUserAnAdmin():
                raise PermissionError("게임이 관리자 권한으로 켜져 있어 읽을 수 없습니다.")
            raise PermissionError(f"게임 프로세스를 읽을 수 없습니다 (오류 {code})")
        self.base = self._module_base("gameassembly.dll")
        self.klass = {}
        self.clear_caches()

    def close(self):
        kernel32.CloseHandle(self.handle)

    def build(self):
        """게임 빌드 표시: GameAssembly.dll 머리말의 빌드 시각과 이미지 크기 (게임이 업데이트되면 바뀐다). 못 읽으면 None."""
        head = self.read(self.base, 0x40) if self.base else None
        pe = self.read(self.base + struct.unpack_from("<I", head, 0x3C)[0], 0x58) if head and head[:2] == b"MZ" else None
        if not pe or pe[:4] != b"PE\0\0":
            return None
        return {"timeDateStamp": struct.unpack_from("<I", pe, 8)[0], "sizeOfImage": struct.unpack_from("<I", pe, 0x50)[0]}

    def clear_caches(self):
        """전투가 시작될 때마다 비운다 (이전 전투의 포인터가 재사용될 수 있다)."""
        self.strings, self.buff_cas, self.card_cas, self.unit_cas, self.leader_maxes = {}, {}, {}, {}, {}
        self.ca_ids, self.product_ids = {}, {}

    def _module_base(self, wanted):
        mods = (W.HMODULE * 4096)()
        need = W.DWORD()
        psapi.EnumProcessModulesEx(self.handle, mods, ctypes.sizeof(mods), ctypes.byref(need), LIST_MODULES_ALL)
        for i in range(need.value // ctypes.sizeof(W.HMODULE)):
            name = ctypes.create_unicode_buffer(260)
            psapi.GetModuleBaseNameW(self.handle, mods[i], name, 260)
            if name.value.lower() == wanted:
                return mods[i]
        return None

    def read(self, addr, size):
        if not ADDRESS_MIN <= addr < ADDRESS_MAX or size <= 0:
            return None
        buf = ctypes.create_string_buffer(size)
        got = ctypes.c_size_t()
        if not kernel32.ReadProcessMemory(self.handle, addr, buf, size, ctypes.byref(got)) or got.value != size:
            return None
        return buf.raw

    def u64(self, addr):
        data = self.read(addr, 8)
        return u64_at(data, 0) if data else 0

    def resolve_classes(self):
        """TypeInfo 슬롯에서 클래스 포인터를 읽고 이름이 맞는지 확인한다."""
        if not self.base:
            self.base = self._module_base("gameassembly.dll")
        if not self.base:
            return False
        if self.read(self.base, 2) is None:
            self._stop_if_blocked()
            return False
        # 주소표를 뽑은 빌드가 아니면 슬롯을 읽지 않는다 (엉뚱한 슬롯은 "초기화 전"처럼 보여 끝없이 기다리게 된다)
        build, known = self.build(), SERVERS[SERVER]["build"]
        if build and build != known:
            raise RuntimeError(f"게임이 업데이트되었습니다 ({SERVERS[SERVER]['name']} 빌드 {build['timeDateStamp']}, 미터가 아는 빌드 {known['timeDateStamp']}). "
                               "Il2CppDumper 로 주소표를 다시 뽑아야 합니다.")
        out = {}
        for name, rva in RVA.items():
            klass = self.u64(self.base + rva)
            if not klass or klass & 1:
                return False  # 게임이 아직 전투 코드를 초기화하지 않음 (초기화 전 슬롯에는 홀수 토큰이 있다)
            name_ptr = self.u64(klass + 0x10)
            raw = self.read(name_ptr, len(name) + 1) if name_ptr else None
            if raw != name.encode() + b"\0":
                raise RuntimeError("게임이 업데이트되어 RVA 가 맞지 않습니다. Il2CppDumper 로 다시 뽑아야 합니다.")
            out[name] = klass
        self.klass = out
        return True

    def _stop_if_blocked(self):
        """프로세스는 살아 있는데 읽히지 않으면 막힌 것이다. 우회하지 않고 멈춘다."""
        code = W.DWORD()
        if kernel32.GetExitCodeProcess(self.handle, ctypes.byref(code)) and code.value == STILL_ACTIVE:
            raise PermissionError("게임 메모리 읽기가 막혔습니다. 우회하지 않고 멈춥니다.")

    def string(self, ptr, cache=True, limit=MAX_STRING):
        if not ptr:
            return ""
        if cache:
            cached = self.strings.get(ptr)
            if cached is not None:
                return cached
        head = self.read(ptr + 0x10, 4)
        if not head:
            return ""
        size = i32_at(head, 0)
        if not 0 <= size <= limit:
            return ""
        data = self.read(ptr + 0x14, size * 2) if size else b""
        if data is None:
            return ""
        text = data.decode("utf-16le", "replace")
        if cache:
            self.strings[ptr] = text
        return text

    def _dict_table(self, ptr, entry_size):
        """Dictionary 의 엔트리 표와 칸 수. 읽을 수 없으면 (None, 0)."""
        head = self.read(ptr, 0x28)
        if head is None:
            return None, 0
        entries, count = struct.unpack_from("<Qi", head, 0x18)
        if not 0 <= count <= MAX_DICT:
            return None, 0
        if count == 0:
            return b"", 0
        return self.read(entries + 0x20, count * entry_size), count

    def dict_values(self, ptr, klass_name, size):
        """Dictionary<int, T> 의 (키, 객체 바이트) 목록. 값의 클래스가 맞는 것만 돌려준다."""
        table, count = self._dict_table(ptr, 24)
        if table is None:
            return None
        klass = self.klass[klass_name]
        out = []
        for i in range(count):
            hash_code, _next, key, _pad, value = struct.unpack_from("<iiiiQ", table, i * 24)
            if hash_code < 0 or not value:  # 빈 칸, 또는 게임이 막 추가하는 중인 칸
                continue
            data = self.read(value, size)
            if data is None or u64_at(data, 0) != klass:
                return None
            out.append((key, data))
        return out

    def dict_int_refs(self, ptr):
        """Dictionary<int, 참조> 의 (키, 포인터) 목록."""
        table, count = self._dict_table(ptr, 24)
        if table is None:
            return []
        out = []
        for i in range(count):
            hash_code, _next, key, _pad, value = struct.unpack_from("<iiiiQ", table, i * 24)
            if hash_code >= 0 and value:
                out.append((key, value))
        return out

    def dict_int_long(self, ptr):
        """Dictionary<int, long>."""
        table, count = self._dict_table(ptr, 24)
        if table is None:
            return {}
        out = {}
        for i in range(count):
            hash_code, _next, key, _pad, value = struct.unpack_from("<iiiiq", table, i * 24)
            if hash_code >= 0:
                out[key] = value
        return out

    def dict_int_int(self, ptr):
        """Dictionary<int, int> (엔트리 16바이트: hash, next, key, value)."""
        table, count = self._dict_table(ptr, 16)
        if table is None:
            return {}
        out = {}
        for i in range(count):
            hash_code, _next, key, value = struct.unpack_from("<iiii", table, i * 16)
            if hash_code >= 0:
                out[key] = value
        return out

    def dict_str_int(self, ptr):
        """Dictionary<string, int> (엔트리 24바이트: hash, next, 키 문자열 포인터, value)."""
        table, count = self._dict_table(ptr, 24)
        if table is None:
            return {}
        out = {}
        for i in range(count):
            hash_code, _next, key, value = struct.unpack_from("<iiQi", table, i * 24)
            if hash_code >= 0 and key:
                out[self.string(key)] = value
        return out

    def list_items(self, ptr, start=0):
        """List<참조> 의 start 번째부터의 포인터."""
        head = self.read(ptr, 0x20)
        if head is None:
            return []
        items, size = struct.unpack_from("<Qi", head, 0x10)
        if not 0 <= size <= MAX_LIST or size <= start:
            return []
        data = self.read(items + 0x20 + start * 8, (size - start) * 8)
        return list(struct.unpack(f"<{size - start}Q", data)) if data else []

    def link_items(self, head):
        """LinkHead<T> 를 앞에서부터 따라가 항목 포인터를 모은다 (최대 1024 노드)."""
        raw = self.read(head, 0x28)
        if raw is None:
            return []
        node, last = struct.unpack_from("<QQ", raw, 0x10)
        out = []
        for _ in range(MAX_LINK):
            data = self.read(node, 0x30) if node else None
            if data is None:
                break
            item = u64_at(data, 0x28)
            if item:
                out.append(item)
            if node == last:
                break
            node = u64_at(data, 0x18)
        return out

    def link_count(self, head):
        raw = self.read(head, 0x28)
        return i32_at(raw, 0x20) if raw else 0

    def property_values(self, prop):
        """Property 전체를 {키: SN 값} 으로 읽는다."""
        raw = self.read(prop, 0x48)
        if raw is None:
            return {}
        table, count = self._dict_table(u64_at(raw, 0x40), 0xA8)
        if table is None:
            return {}
        out = {}
        for i in range(count):
            at = i * 0xA8
            if i32_at(table, at) < 0:
                continue
            key = self.string(u64_at(table, at + 8))
            if key:
                out[key] = property_unit_value(table, at + 16)
        return out

    def context(self):
        """정적 경로로 현재 전투를 찾는다. 전투가 아니면 None."""
        statics_raw = self.read(self.klass["BuffBase"] + 0xB8, 8)
        if statics_raw is None:
            self._stop_if_blocked()
            return None
        statics = u64_at(statics_raw, 0)
        manager = self.u64(statics + 0x18) if statics else 0
        raw = self.read(manager, 0x168) if manager else None
        if raw is None:
            return None
        team = u64_at(raw, 0xA8)
        team_raw = self.read(team, 0x110) if team else None
        if team_raw is None or u64_at(team_raw, 0) != self.klass["TeamData"]:
            return None
        battle_data = u64_at(team_raw, 0x88)
        battle_raw = self.read(battle_data, 0x28) if battle_data else None
        if battle_raw is None or u64_at(battle_raw, 0x10) != team:
            return None
        result = u64_at(battle_raw, 0x20)
        if not result:
            return None
        return types.SimpleNamespace(
            manager=manager, unit_manager=u64_at(raw, 0x48), frame=i32_at(raw, 0xB4), bullet=bool(raw[0x150]),
            state=i32_at(raw, 0x160), team=team, buff_system=u64_at(team_raw, 0x78),
            team_property=u64_at(team_raw, 0x80), card_system=u64_at(team_raw, 0x90),
            role_list=u64_at(team_raw, 0x98), cost=i64_at(team_raw, 0xA8), max_cost=i64_at(team_raw, 0xB0),
            adjust_cost=u64_at(team_raw, 0xB8), start_cost=i64_at(team_raw, 0xE0),
            start_index=i64_at(team_raw, 0xE8), result=result, replay_manager=u64_at(team_raw, 0x28),
            ai_core=u64_at(team_raw, 0x100), use_card_ai=bool(team_raw[0x108]))

    def snapshot(self, obj):
        """BattleResult 하나를 읽는다. 전투 객체가 아니면 None."""
        data = self.read(obj, 0xA0)
        if not data or u64_at(data, 0) != self.klass["BattleResult"]:
            return None
        duration = i32_at(data, 0x14)
        skills_ptr, roles_ptr = struct.unpack_from("<QQ", data, 0x88)
        roles_raw = self.dict_values(roles_ptr, "RoleInfo", 0x40)
        skills_raw = self.dict_values(skills_ptr, "BattleSkillInfo", 0x40)
        if not roles_raw or len(roles_raw) > 12 or skills_raw is None:
            return None
        roles, skills = {}, {}
        for key, raw in roles_raw:
            name = self.string(u64_at(raw, 0x10))
            damage, get_hit, heal, get_heal = struct.unpack_from("<qqqq", raw, 0x18)
            roles[key] = {"name": name, "damage": damage, "getHit": get_hit, "heal": heal, "getHeal": get_heal}
        for key, raw in skills_raw:
            name = self.string(u64_at(raw, 0x10))
            fields = struct.unpack_from("<iiiiiiiii", raw, 0x18)
            skills[key] = dict(zip(("dmg", "heal", "findtimes", "findtargets", "take", "use", "level", "passive", "abandon"), fields), name=name)
        return {"duration": duration, "roles": roles, "skills": skills, "gameTotalSN": check_num(data, 0x30),
                "cardOrder": u64_at(data, 0x80)}

    def result_conditions(self, obj):
        """전투 조건. cores 와 enemy_ids 는 전투 중에 바뀌므로 캐시하지 않는다."""
        data = self.read(obj, 0xA0)
        if not data or u64_at(data, 0) != self.klass["BattleResult"]:
            return None
        progress = struct.unpack_from("<f", data, 0x7C)[0]
        return {
            "isWin": bool(data[0x10]), "survivor": i32_at(data, 0x18), "mvpId": i32_at(data, 0x28),
            "getHitTotal": i64_at(data, 0x48), "healTotal": i64_at(data, 0x50),
            "cores": self.string(u64_at(data, 0x58), cache=False),
            "enemyIds": self.string(u64_at(data, 0x60), cache=False),
            "enemyLevelMin": i32_at(data, 0x68), "enemyLevel": i32_at(data, 0x6C),
            "weatherId": i32_at(data, 0x70), "secondWeatherId": i32_at(data, 0x74), "bgId": i32_at(data, 0x78),
            "levelProgress": round(progress, 4) if math.isfinite(progress) else 0,
        }

    def replay_info(self, manager):
        """ReplayManager.replay 의 전투 스펙을 읽는다. 반환: (값, 실패 이유). playerUid(+0x18) 는 읽지 않는다."""
        head = self.read(manager, 0x38) if manager else None
        replay = self.read(u64_at(head, 0x30), 0x78) if head else None
        if replay is None:
            return None, "Replay 객체가 없습니다"
        listing = self.read(u64_at(replay, 0x48), 0x20)
        if listing is None:
            return None, "unitInfoListTeam1 이 없습니다"
        items, size = struct.unpack_from("<Qi", listing, 0x10)
        if not 1 <= size <= MAX_TEAM_UNITS:
            return None, f"unitInfoListTeam1 크기가 범위를 벗어났습니다 ({size})"
        data = self.read(items + 0x20, size * UNIT_INFO_SIZE)
        if data is None:
            return None, "unitInfoListTeam1 배열을 읽지 못했습니다"
        read_text = lambda ptr: self.string(ptr, cache=False, limit=SPEC_STRING)
        units = [decode_unit_info(data, i * UNIT_INFO_SIZE, read_text) for i in range(size)]
        for unit in units:
            for field, (low, high) in UNIT_INFO_LIMITS.items():
                if not low <= unit[field] <= high:
                    return None, f"UnitInfo.{field} 값이 범위를 벗어났습니다. 오프셋이 바뀌었을 수 있습니다"
        # randomSeed(+0x34): BattleMain.GameStart 가 이 값으로 SafeMath.SetRandomSeed 를 부른다 — 시뮬이 같은 판을 재현할 때 쓴다. playerLv(+0x40) 도 관문 생성 인자다
        init, init_error = self.replay_init_args(manager)
        return {"levelId": i32_at(replay, 0x38), "randomSeed": i32_at(replay, 0x34), "playerLv": i32_at(replay, 0x40), "isReplay": bool(head[0x28]), "units": units,
                "extraCards": read_text(u64_at(replay, 0x58)), "enemyIds": read_text(u64_at(replay, 0x60)),
                "enemyLv": i32_at(replay, 0x68), "trainWeaponSkills": read_text(u64_at(replay, 0x70)),
                "init": init, "initError": init_error}, None

    def replay_init_args(self, manager):
        """ReplayManager 가 InitBattle 로 받은 관문 인자(날씨 후보·확률, 난이도 등). 반환: (값, 실패 이유).
        날씨 후보 배열이 null 이면 None 으로 둔다 — 엔진은 null 과 빈 배열을 다르게 다룬다."""
        raw = self.read(manager + REPLAY_INIT_START, REPLAY_INIT_END - REPLAY_INIT_START)
        if raw is None:
            return None, "ReplayManager 관문 인자를 읽지 못했습니다"
        out = {}
        for name, at, kind in REPLAY_INIT_FIELDS:
            at -= REPLAY_INIT_START
            if kind == "bool":
                if raw[at] > 1:
                    return None, f"ReplayManager.{name} 이 bool 이 아닙니다. 오프셋이 바뀌었을 수 있습니다"
                out[name] = bool(raw[at])
            elif kind == "i32":
                out[name] = i32_at(raw, at)
            elif kind == "i64":
                out[name] = i64_at(raw, at)
            else:
                values = self.int_array(u64_at(raw, at))
                if values is False:
                    return None, f"ReplayManager.{name} 배열을 읽지 못했습니다"
                out[name] = values
        return out, None

    def int_array(self, ptr):
        """int[] 의 원소. null 이면 None, 못 읽거나 길이가 이상하면 False."""
        if not ptr:
            return None
        head = self.read(ptr, 0x20)
        if head is None:
            return False
        size = u64_at(head, 0x18)
        if size > MAX_INT_ARRAY:
            return False
        data = self.read(ptr + 0x20, size * 4) if size else b""
        if data is None:
            return False
        return list(struct.unpack(f"<{size}i", data))

    def operation_logs(self, manager, start):
        """ReplayManager.replay.operationLogList (List<Replay.OperationLog>, 0x50바이트 구조체) 의 start 번째부터.
        게임이 리플레이용으로 남기는 조작 기록이라 카드 사용 좌표(xSN·zSN)와 대상 uniqueId 가 그대로 들어 있다.
        cardIndex 는 사용 당시 손패 번호, -1 이면 손패 교체(refresh)나 팀 카드 선택(teamCard) 기록이다."""
        head = self.read(manager, 0x38) if manager else None
        replay_raw = self.read(u64_at(head, 0x30), 0x88) if head else None
        listing = self.read(u64_at(replay_raw, 0x80), 0x20) if replay_raw else None
        if listing is None:
            return []
        items, size = struct.unpack_from("<Qi", listing, 0x10)
        if not 0 <= size <= MAX_LIST or size <= start:
            return []
        data = self.read(items + 0x20 + start * OPERATION_SIZE, (size - start) * OPERATION_SIZE)
        if data is None:
            return []
        out = []
        for i in range(size - start):
            at = i * OPERATION_SIZE
            frame = i32_at(data, at)
            for team, index_at, pos_at in ((1, 0x4, 0x10), (2, 0x28, 0x38)):
                card_index, refresh, team_card = struct.unpack_from("<i?xxxi", data, at + index_at)
                x_sn, z_sn, uid_ptr = struct.unpack_from("<qqQ", data, at + pos_at)
                if card_index < 0 and not refresh and team_card < 0:
                    continue
                out.append({"frame": frame, "team": team, "cardIndex": card_index, "x": x_sn, "z": z_sn,
                            "uid": self.string(uid_ptr, cache=False) if uid_ptr else "",
                            "refresh": refresh, "teamCard": team_card})
        return out

    def ai_state(self, ai_core):
        """CardAICore 의 현재 행동 값·카드·칠판(Dictionary<string,int>). 카드 AI 가 대상 좌표를 고른 근거를 남기기 위한 것."""
        raw = self.read(ai_core, 0xC0) if ai_core else None
        if raw is None:
            return None
        card = u64_at(raw, 0xB0)
        ca = self.card_ca(self.u64(card + 0x108)) if card else None
        return {"actionValue": i32_at(raw, 0xB8), "cardId": ca[0] if ca else None,
                "blackboard": self.dict_str_int(u64_at(raw, 0x60))}

    def card_order(self, ptr, start):
        """cardOrder (List<RecordCardInfo>) 의 start 번째부터의 새 항목.
        게임이 막 추가해 아직 비어 있는 칸이 나오면 거기서 멈추고 다음 틱에 다시 읽는다."""
        out = []
        for item in self.list_items(ptr, start):
            raw = self.read(item, 0x68) if item else None
            if raw is None:
                break
            card_id, owner_id, cost = struct.unpack_from("<iii", raw, 0x58)
            out.append({"noCost": bool(raw[0x54]), "leader": bool(raw[0x55]), "id": card_id,
                        "owner": owner_id, "shown": cost})
        return out

    def card_ca(self, ptr):
        """CardCA 의 (id, 이름, 기본 비용 SN)."""
        cached = self.card_cas.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0xD8)
            if raw is None:
                return None
            cached = self.card_cas[ptr] = (i32_at(raw, 0x18), self.string(u64_at(raw, 0x58)), i64_at(raw, 0xD0))
        return cached

    def property_card_ca(self, raw):
        """CardProperty 바이트에서 실제로 쓰이는 카드(_fakeCard 우선)의 CardCA."""
        card = u64_at(raw, 0x70) or u64_at(raw, 0x68)
        return self.card_ca(self.u64(card + 0x108)) if card else None

    def hand_cards(self, head, adjust):
        """손패를 [{id, name, cost}] 로 읽는다.

        cost 는 근사값이다: 카드 기본 비용에 _adjustCostDic 을 반영하고 카드 자신의
        CostOffset·TempCostOffset 을 더한 값이며, _lockCost_SN 이 있으면 그 값으로 대체한다.
        유닛 오프셋과 손패 할인 버프는 게임 로직이 복잡해 제외했다."""
        out = []
        for item in self.link_items(head):
            raw = self.read(item, 0xD8)
            ca = self.property_card_ca(raw) if raw else None
            if ca is None:
                continue
            card_id, name, cost = ca
            if card_id in adjust:
                cost = max(cost + adjust[card_id], 0)
            offsets = self.property_values(u64_at(raw, 0x90))
            cost += offsets.get("CostOffset", 0) + offsets.get("TempCostOffset", 0)
            locked = i64_at(raw, 0xD0)
            if locked >= 0:
                cost = locked
            out.append({"id": card_id, "name": name, "cost": min(max(cost, 0), 990000)})
        return out

    def leader_card(self, property_ptr):
        """리더 카드(CardProperty)의 (id, 이름). 없으면 None."""
        raw = self.read(property_ptr, 0xD8) if property_ptr else None
        ca = self.property_card_ca(raw) if raw else None
        return ca[:2] if ca else None

    def leader_conditions(self, list_ptr):
        """리더 카드 조건들의 [{progress, max, finished}]."""
        out = []
        for item in self.list_items(list_ptr):
            raw = self.read(item, 0x74)
            if raw is None:
                continue
            ca = u64_at(raw, 0x40)
            maximum = self.leader_maxes.get(ca)
            if maximum is None:
                ca_raw = self.read(ca, 0x5C)
                maximum = self.leader_maxes[ca] = i32_at(ca_raw, 0x58) if ca_raw else 0
            out.append({"progress": i32_at(raw, 0x50), "max": maximum, "finished": bool(raw[0x60])})
        return out

    def unit_ca(self, ptr):
        """UnitCA 의 (id, 이름)."""
        cached = self.unit_cas.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x60)
            if raw is None:
                return None
            cached = self.unit_cas[ptr] = (i32_at(raw, 0x18), self.string(u64_at(raw, 0x58)))
        return cached

    def units(self, manager):
        """UnitManager._unitDic 의 전체 유닛을 [(팀 키, 포인터, 바이트)] 로 돌려준다."""
        raw = self.read(manager, 0x58)
        if raw is None:
            return []
        out = []
        for team, list_ptr in self.dict_int_refs(u64_at(raw, 0x50)):
            for unit in self.list_items(list_ptr):
                data = self.read(unit, 0x4A0) if unit else None
                if data is not None:
                    out.append((team, unit, data))
                if len(out) >= MAX_UNITS:
                    return out
        return out

    def role_order(self, list_ptr):
        """TeamData._roleList 의 캐릭터 id 순서."""
        out = []
        for unit in self.list_items(list_ptr):
            ca = self.unit_ca(self.u64(unit + 0x490)) if unit else None
            if ca:
                out.append(ca[0])
        return out

    def buff_ca(self, ptr):
        """BuffSustainCA 의 필요한 값 (포인터별로 캐시)."""
        cached = self.buff_cas.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x140)
            if raw is None:
                return None
            cached = self.buff_cas[ptr] = {
                "id": i32_at(raw, 0x18), "mod": self.string(u64_at(raw, 0x10)), "idCN": self.string(u64_at(raw, 0x20)),
                "baseEffect": self.string(u64_at(raw, 0x58)), "forever": bool(raw[0x132])}
        return cached

    def ca_id(self, ptr):
        """CABase.id (포인터별로 캐시)."""
        if not ptr:
            return 0
        cached = self.ca_ids.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x20)
            cached = self.ca_ids[ptr] = i32_at(raw, 0x18) if raw else 0
        return cached

    def product_id(self, ptr):
        """Product(카드 등)의 ca.id (포인터별로 캐시)."""
        if not ptr:
            return 0
        cached = self.product_ids.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x40)
            cached = self.product_ids[ptr] = self.ca_id(u64_at(raw, 0x38)) if raw else 0
        return cached

    def action_of(self, action):
        """UnitAction 하나: (동작 id, 진행 프레임, 전체 프레임, 카드 id, 일반 공격 여부, 리더 스킬 여부). 없으면 None."""
        raw = self.read(action, 0x178) if action else None
        if raw is None:
            return None
        return (self.ca_id(u64_at(raw, 0x170)), i32_at(raw, 0xBC), i32_at(raw, 0xC0), self.product_id(u64_at(raw, 0xE8)),
                bool(raw[0x10D]), bool(raw[0xE0]))

    def dots_of(self, system):
        """BuffSystem 의 주기 효과(BuffDot) 인스턴스: [(포인터, buff id, 건 유닛의 sid, 프레임 카운터, 틱 간격)]."""
        head = self.read(system, 0x38)
        if head is None:
            return []
        out = []
        for link in (u64_at(head, 0x18), u64_at(head, 0x30)):
            for item in self.link_items(link):
                raw = self.read(item, 0x128)
                if raw is None or raw[0x30] or raw[0x58]:  # isRecycled, _isEnd
                    continue
                ca = self.buff_ca(u64_at(raw, 0x100))
                if ca is None or ca["mod"] != DOT_MOD:
                    continue
                out.append((item, ca["id"], i32_at(raw, 0x40), i32_at(raw, 0x120), i32_at(raw, 0x124)))
        return out

    def buffs_of(self, system):
        """BuffSystem 의 활성 버프를 buff id 로 합친다.

        _buffLink 와 _cannotBeDispelled 가 전체 집합이다 (게임의 GetBuffLevel 도 이 둘만 합산).
        반환: {buff id: {ca, stacks(Level 합), instances, left(영구면 None, 아니면 최대 남은 프레임)}}"""
        head = self.read(system, 0x38)
        if head is None:
            return {}
        out = {}
        for link in (u64_at(head, 0x18), u64_at(head, 0x30)):
            for item in self.link_items(link):
                raw = self.read(item, 0x108)
                if raw is None or raw[0x30] or raw[0x58]:  # isRecycled, _isEnd
                    continue
                level = i32_at(raw, 0xC0)
                if level <= 0:
                    continue
                ca = self.buff_ca(u64_at(raw, 0x100))
                if ca is None:
                    continue
                row = out.get(ca["id"])
                if row is None:
                    row = out[ca["id"]] = {"ca": ca, "stacks": 0, "instances": 0, "left": None if ca["forever"] else 0}
                row["stacks"] += level
                row["instances"] += 1
                if not ca["forever"]:
                    row["left"] = max(row["left"], i32_at(raw, 0xB8))
        return out


# 버프 내부 이름(idCN) 번역용 용어집
GLOSSARY = {
    "卡牌": "카드", "手牌": "손패", "费用": "비용", "回费": "비용 회복", "层数": "중첩", "标记": "표식", "计数": "카운트",
    "监测": "감시", "触发": "발동", "参数": "파라미터", "特效": "이펙트", "增伤": "피해 증가", "减伤": "피해 감소", "音符": "노트",
    "抽牌": "드로우", "弃牌区": "버림 더미", "弃牌": "버리기", "附加": "추가", "获得": "획득", "共振": "공명", "觉醒": "각성",
    "突破": "돌파", "养成": "육성", "周期": "주기", "持续": "지속", "攻击力": "공격력", "防御力": "방어력", "攻击": "공격",
    "防御": "방어", "伤害": "피해", "提升": "증가", "提高": "증가", "降低": "감소", "治疗": "치유", "护盾": "보호막",
    "暴击": "치명타", "普攻": "일반 공격", "攻速": "공격 속도", "狂暴": "광폭", "点燃": "점화", "灼心": "화상", "斩裂": "참열",
    "落雷": "낙뢰", "引雷": "인뢰", "凭依": "빙의", "雷系": "전기 계열", "练攻": "공격 육성", "练防": "방어 육성", "练功": "육성",
    "额外": "추가", "驱散": "해제", "减攻防": "공방 감소", "加攻": "공격 증가", "铁盟": "철도연맹", "焦灼": "초조", "炽地": "작열",
    "烬灭": "소멸", "秒": "초",
}
BUFF_PIECE_SKIP = re.compile(r"^[0-9]{2}(我方|敌方|[二三四五]星|通用机制|技能养成)$")
BUFF_PIECE_NUMBER = re.compile(r"^[0-9]{2}")


class Names:
    """게임 데이터(web/data/game.js)로 ID 와 중국어 이름을 한국어로 바꾼다."""

    def __init__(self):
        self.roster, self.kr, self.records, self.zh_names = {}, {}, {}, []
        self.equip_items, self.equip_breaks, self.affixes, self.reso = {}, {}, {}, {}
        self.edges, self.reach = None, {}
        self.edge_lock = threading.Lock()
        self.labels, self.kinds = {}, {}
        self.glossary = sorted(GLOSSARY.items(), key=lambda kv: -len(kv[0]))
        try:
            text = read_data(GAME_DATA, "data/game.js")
            game = json.loads(text[text.index("{"):text.rindex("}") + 1])
            self.roster = {r["id"]: r["name"] for r in game.get("roster", [])}
            self.kr = game.get("kr", {})
            self.records = game.get("records", {})
            equip = game.get("equip") or {}
            self.equip_items = {int(item["id"]): item for item in equip.get("items") or []}
            self.equip_breaks = equip.get("breaks") or {}
            self.affixes = equip.get("affix") or {}
            self.reso = game.get("reso") or {}
        except (OSError, ValueError, KeyError, TypeError) as exc:
            print("게임 데이터를 읽지 못했습니다:", exc, file=sys.stderr)
        try:
            roster = json.loads(read_data(ROSTER_DATA, "data/kr_roster.json"))
            pairs = {r["zh"]: r["name"] for r in roster if r.get("zh") and r.get("name")}
            self.zh_names = sorted(pairs.items(), key=lambda kv: -len(kv[0]))
        except (OSError, ValueError, KeyError, TypeError) as exc:
            print("캐릭터 목록을 읽지 못했습니다:", exc, file=sys.stderr)
        try:
            extra = json.loads(read_data(EXTRA_DATA, "data/extra_names.json"))
            for r in extra.get("roster", []):
                self.roster.setdefault(r["id"], r["name"])
            for key, record in (extra.get("records") or {}).items():
                self.records.setdefault(key, record)
            for key, nodes in (extra.get("reso") or {}).items():
                self.reso.setdefault(key, nodes)
            extra_equip = extra.get("equip") or {}
            for item in extra_equip.get("items") or []:
                self.equip_items.setdefault(int(item["id"]), item)
            for key, info in (extra_equip.get("affix") or {}).items():
                self.affixes.setdefault(key, info)
            for zh, name in (extra.get("kr") or {}).items():
                self.kr.setdefault(zh, name)
            pairs = dict(self.zh_names)
            for r in extra.get("roster", []):
                pairs.setdefault(r["zh"], r["name"])
            self.zh_names = sorted(pairs.items(), key=lambda kv: -len(kv[0]))
        except (OSError, ValueError, KeyError, TypeError) as exc:
            print("보충 이름 자료를 읽지 못했습니다:", exc, file=sys.stderr)

    def role(self, key, name):
        return self.roster.get(key) or self.kr.get(name) or name or str(key)

    def skill(self, key, name):
        if name:
            return self.kr.get(name, name)
        record = self.records.get(str(key)) or {}
        return self.kr.get(record.get("name"), record.get("name")) or str(key)

    def _translate_piece(self, piece):
        """idCN 조각 하나를 번역한다: 캐릭터 이름 → 조각 전체 번역 → 용어집 (긴 것 먼저)."""
        for zh, name in self.zh_names:
            # 한 글자 이름(空, 遥 등)은 일반 단어를 망가뜨리므로 조각 전체가 그 이름일 때만 바꾼다.
            if len(zh) > 1 or piece == zh:
                piece = piece.replace(zh, name)
        piece = self.kr.get(piece, piece)
        for zh, ko in self.glossary:
            piece = piece.replace(zh, ko)
        return piece

    def buff_label(self, id_cn, buff_id=0):
        """'BUFF/00我方/05五星/卡塔斯·业火/共振2/音符抽牌标记' → '카타스·이그니스 / 공명2 / 노트드로우표식'."""
        cached = self.labels.get(id_cn) if id_cn else None
        if cached is not None:
            return cached
        pieces = (id_cn or "").split("/")
        if pieces[0] == "BUFF":
            pieces = pieces[1:]
        out = []
        for piece in pieces:
            if piece and not BUFF_PIECE_SKIP.match(piece):
                piece = self._translate_piece(BUFF_PIECE_NUMBER.sub("", piece))
                if piece:
                    out.append(piece)
        label = " / ".join(out) or str(buff_id)
        if id_cn:
            self.labels[id_cn] = label
        return label

    def buff_kind(self, buff_id, base_effect):
        """버프 분류와 속성 목록: ('buff'|'debuff'|'other', ['attributeType·numberType', ...])."""
        cache_key = (buff_id, base_effect)
        cached = self.kinds.get(cache_key)
        if cached is not None:
            return cached
        changes = (self.records.get(str(buff_id)) or {}).get("attributeChangeList") or []
        attrs = list(dict.fromkeys(f"{c.get('attributeType', '')}·{c.get('numberType', '')}" for c in changes))[:4]
        if base_effect == "PositiveEffect":
            kind = "buff"
        elif base_effect == "NegativeEffect":
            kind = "debuff"
        elif changes:
            signs = []
            for change in changes:
                name = change.get("attributeType") or ""
                if "GetDamage" in name:
                    sign = 1 if "Down" in name else -1
                else:
                    sign = -1 if "Down" in name else 1
                if change.get("numberType") == "PercentDown" or (change.get("value_SN") or 0) < 0:
                    sign = -sign
                signs.append(sign)
            kind = "debuff" if all(s < 0 for s in signs) else "buff"
        else:
            kind = "other"
        self.kinds[cache_key] = (kind, attrs)
        return kind, attrs

    def _build_edges(self):
        def ints(node, out):
            if isinstance(node, dict):
                for value in node.values():
                    ints(value, out)
            elif isinstance(node, list):
                for value in node:
                    ints(value, out)
            elif isinstance(node, int) and not isinstance(node, bool):
                out.add(str(node))

        with self.edge_lock:
            if self.edges is not None:
                return
            edges = {}
            for rid, record in self.records.items():
                found = set()
                ints(record, found)
                found.discard(rid)
                edges[rid] = [x for x in found if x in self.records]
            self.edges = edges

    def _distances(self, role):
        """캐릭터 레코드에서 게임 데이터 참조를 따라간 거리. 카드 주인을 정할 때 쓴다."""
        key = str(role)
        if key not in self.reach:
            if self.edges is None:
                self._build_edges()
            seen, frontier, depth = {key: 0}, [key], 0
            while frontier and depth < 6:
                depth += 1
                following = []
                for node in frontier:
                    for neighbor in self.edges.get(node, ()):
                        if neighbor not in seen:
                            seen[neighbor] = depth
                            following.append(neighbor)
                frontier = following
            self.reach[key] = seen
        return self.reach[key]

    def owner(self, skill, roles):
        """이 카드에 가장 가까운 캐릭터. 거리가 같으면 주인을 정하지 않는다."""
        ranked = sorted((self._distances(r).get(str(skill), 99), str(r)) for r in roles)
        if not ranked or ranked[0][0] == 99 or (len(ranked) > 1 and ranked[0][0] == ranked[1][0]):
            return None
        return ranked[0][1]


def read_card_prefs():
    """레지스트리의 자동 사용 슬롯과 플래그를 뒤쪽 키 이름으로 돌려준다. 값 이름 전체는 남기지 않는다."""
    slots, flags = {}, {}
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, GAME_PREFS_KEY, 0, winreg.KEY_READ) as key:
        for index in range(winreg.QueryInfoKey(key)[1]):
            name, value, kind = winreg.EnumValue(key, index)
            match = PREFS_NAME.match(name)
            if not match:
                continue
            if match.group(1) != "CardAIData":
                if not match.group(2):
                    flags[match.group(1)] = value if isinstance(value, int) else None
            elif kind == winreg.REG_BINARY:
                text = value.rstrip(b"\0").decode("utf-8", "replace")
                if text.startswith("{"):
                    slots[match.group(2)] = text
    return slots, flags


def parse_card_slots(slots):
    """레지스트리의 슬롯 문자열을 해석한다. 내용이 없는 슬롯은 뺀다."""
    out = {}
    for key, text in slots.items():
        try:
            data = json.loads(text)
        except ValueError:
            continue
        if isinstance(data, dict) and data.get("cardList"):
            out[key] = {"data": data, "text": text}
    return out


def encode_code(data):
    """게임 CompressData 와 같은 형식: base64(raw deflate(UTF-8 JSON)), level 6, memLevel 8."""
    packer = zlib.compressobj(6, zlib.DEFLATED, -15, 8, 0)
    text = json.dumps(data, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return base64.b64encode(packer.compress(text) + packer.flush()).decode("ascii")


def expected_weights(card_list):
    """ApplyAICoreSet 이 extraCardWeightDic 에 넣는 값 (카드 id → 가중치. linkCardId 는 제외)."""
    out = {}
    for index, card in enumerate(card_list):
        card_id = int(card["id"])
        banned = card_id != DISCARD_CARD and card.get("useType", 1) == 2
        out[card_id] = BAN_WEIGHT if banned else FIRST_WEIGHT - STEP_WEIGHT * index
    return out


def pick_card_slot(slots, party, level_id=None, weights=None):
    """이번 전투의 슬롯을 근거가 강한 순서로 고른다. 반환: (키, 슬롯, 근거). 못 고르면 키가 None."""
    party_set = set(party)
    rows = []
    for key, slot in slots.items():
        data = slot["data"]
        owners = {c.get("ownerId") for c in data["cardList"]} - {DISCARD_OWNER}
        roles = {r for r in data.get("roleList") or [] if isinstance(r, int) and r > 0}
        rows.append((key, slot, owners, roles))
    level_key = f"LevelRoleList_{level_id}"
    if weights:  # 전투 중 실제 AI 가중치와 전부 일치하면 그것이 답이다
        exact = [row for row in rows if row[2] <= party_set
                 and all(weights.get(k) == v for k, v in expected_weights(row[1]["data"]["cardList"]).items())]
        if exact:
            # 카드가 적은 슬롯은 앞부분만 우연히 같을 수 있다
            exact.sort(key=lambda row: (-len(row[1]["data"]["cardList"]), row[0] != level_key, row[3] != party_set))
            return exact[0][0], exact[0][1], "weights" if len(exact) == 1 else "weights-tie"
    for key, slot, owners, _roles in rows:
        if key == level_key and owners and owners <= party_set:
            return key, slot, "level"
    exact = [row for row in rows if row[3] == party_set and row[2] <= party_set]
    if len(exact) == 1:
        return exact[0][0], exact[0][1], "roleList"
    same = [row for row in rows if row[2] == party_set]
    numbered = [row for row in same if row[0].isdigit()]
    if len(numbered) == 1:
        return numbered[0][0], numbered[0][1], "owners-squad"
    if len(same) == 1:
        return same[0][0], same[0][1], "owners"
    if same or exact:
        return None, None, f"ambiguous:{len(same or exact)}"
    return None, None, "none"


def use_type_label(names, card_id, use_type):
    """사용 방식 숫자의 뜻. web/app.js useOptions 와 같은 규칙이다."""
    if card_id == DISCARD_CARD:
        return DISCARD_LABELS.get(use_type)
    if use_type == 1:
        return "항상"
    if use_type == 2:
        return "사용 안 함"
    record = names.records.get(str(card_id)) or {}
    conditions, actions = record.get("ExCondList") or [], record.get("ExActList") or []
    index = (use_type or 0) - 3
    if 0 <= index < len(conditions):
        return conditions[index].get("desc") or f"조건 {index + 1}"
    index -= len(conditions)
    if 0 <= index < len(actions):
        return (actions[index].get("desc") or f"대상 {index + 1}") + " (시전 대상 지정)"
    return None


def auto_use_spec(names, state, party, leader, level_id, warnings):
    """spec.autoUse. code 는 게임의 클립보드 내보내기와 같은 형식의 문자열이다."""
    flags = state.flags or {}
    on = state.ai_last
    registry_on = flags["CardAIOn"] != 0 if isinstance(flags.get("CardAIOn"), int) else None
    out = {"on": on if on is not None else registry_on,
           "onSource": "memory:TeamData.isUseCardAI" if on is not None else "registry:CardAIOn" if registry_on is not None else None,
           "everOnDuringBattle": state.ai_ever if on is not None else None, "registryOn": registry_on,
           "registryBanFlag": flags.get("CardAIBan"), "code": None, "decoded": None, "cards": [],
           "source": {"from": None, "slot": None, "matchedBy": None, "readAt": "전투 시작 (게임이 자동 사용 설정을 저장한 뒤의 값)",
                      "changedDuringBattle": state.slot_changed, "weightCheck": None}}
    if state.slots is None:
        out["source"]["matchedBy"] = "registry-unreadable"
        warnings.append("레지스트리에서 자동 사용 설정을 읽지 못했습니다" + (f": {state.prefs_error}" if state.prefs_error else ""))
        return out
    key, slot, why = pick_card_slot(state.slots, party, level_id, state.weights)
    out["source"]["matchedBy"] = why
    if slot is None:
        warnings.append(f"이번 파티에 맞는 자동 사용 슬롯을 확정하지 못했습니다 ({why}). 코드는 비워 둡니다.")
        return out
    state.slot_key = key
    data = slot["data"]
    export = json.loads(slot["text"])
    if set(export.get("roleList") or []) != set(party):
        export["roleList"] = list(party)
    if leader:  # 게임의 내보내기는 편성의 현재 리더를 header 로 쓴다
        if export.get("header") not in (None, leader):
            warnings.append(f"레지스트리의 header({export['header']})가 이번 전투의 리더({leader})와 달라 리더로 고쳐 코드를 만들었습니다.")
        export["header"] = leader
    elif not export.get("header"):
        export["header"] = party[0] if party else None
    cards = data["cardList"]
    weights = expected_weights(cards)
    out["code"] = encode_code(export)
    out["decoded"] = export
    out["source"].update({"from": "registry", "slot": key})
    for rank, card in enumerate(cards, 1):
        card_id, owner = int(card["id"]), card.get("ownerId")
        out["cards"].append({
            "rank": rank, "id": card_id, "name": names.skill(card_id, ""), "ownerId": owner,
            "ownerName": names.roster.get(owner) if owner != DISCARD_OWNER else None, "skillId": card.get("skillId"),
            "skillIndex": card.get("skillIndex"), "useType": card.get("useType"),
            "useTypeLabel": use_type_label(names, card_id, card.get("useType")), "useParam": card.get("useParam"),
            "useParamMap": card.get("useParamMap"), "targetType": card.get("targetType"), "equipIdList": card.get("equipIdList"),
            "isDiscardEntry": card_id == DISCARD_CARD, "expectedWeight": weights[card_id]})
    if state.weights:
        wrong = [k for k, v in weights.items() if state.weights.get(k) != v]
        out["source"]["weightCheck"] = {"cards": len(weights), "mismatch": len(wrong), "mismatchIds": wrong[:20]}
        if wrong:
            warnings.append(f"자동 사용 슬롯 {key} 와 전투 중 AI 가중치가 {len(wrong)}장 다릅니다. 코드가 이번 전투 설정과 다를 수 있습니다.")
    else:
        warnings.append("전투 중 AI 가중치(CardAICore)를 읽지 못해 슬롯을 파티 구성으로만 골랐습니다.")
    if state.slot_changed:
        warnings.append("전투 중에 자동 사용 설정이 바뀌었습니다. 코드는 전투 시작 때 값입니다.")
    return out


def decode_unit_info(data, at, read_text):
    """Replay.UnitInfo 구조체 하나. 미장착 칸은 None. 펫 능력치 칸은 장비가 없어도 채워지므로 따로 모은다."""
    out = {key: i32_at(data, at + offset) for key, offset in UNIT_INFO_INTS.items()}
    equips, pets = [], []
    for equip_slot, (id_at, lv_at, slot_ids, slot_values) in enumerate(UNIT_INFO_EQUIPS):
        equip_id = i32_at(data, at + id_at)
        options = []
        for slot, (slot_id, slot_value) in enumerate(zip(slot_ids, slot_values)):  # slot 은 random_affix 번호와 같다
            option_id = i32_at(data, at + slot_id)
            if option_id > 0:
                row = {"slot": slot, "id": option_id, "valueSN": i64_at(data, at + slot_value)}
                (pets if PET_SLOTS.get((equip_slot, slot)) == option_id else options).append(row)
        equips.append({"id": equip_id, "lv": i32_at(data, at + lv_at), "options": options} if equip_id > 0 and equip_id != EMPTY_EQUIP_ID else None)
    out["equips"] = equips
    out["pets"] = pets
    out["extraSkills"] = read_text(u64_at(data, at + 0x168))
    return out


def affix_display(info, value):
    """옵션 수치를 화면 표기로 바꾼다: (표시값, 설명문). 수치가 없는 옵션은 표시값 None."""
    desc = (info or {}).get("desc")
    if not desc:
        return None, None
    if info.get("min") is None or value is None or value < 0:
        return None, desc.replace("%s%%", "").replace("%s", "").strip()
    shown = round(value * info.get("show", 1), max(int(info.get("digits", 0)), 0))
    shown = int(shown) if float(shown).is_integer() else shown
    return shown, desc.replace("%s%%", f"{shown}%").replace("%s", str(shown))


def option_row(names, item, kind, slot, option_id, value, source):
    info = names.affixes.get(str(option_id))
    shown, text = affix_display(info, value)
    if kind == "fixedSkill" and item and item.get("skillDesc"):
        text = item["skillDesc"][0]
    return {"slot": slot, "id": option_id, "kind": kind, "name": (info or {}).get("desc") or text, "value": value,
            "displayValue": shown, "text": text, "source": source}


def option_kind(slot):
    return "fixedSkill" if slot == 0 else "random" if slot <= 3 else "extra"


def memory_options(names, item, mem):
    """UnitInfo 의 옵션 칸. slot 은 random_affix 번호다. 수치가 없는 옵션은 메모리에 0 으로 들어간다."""
    out = []
    for row in mem["options"]:
        value = round(row["valueSN"] / 10000, 4) if row["valueSN"] else None
        option = option_row(names, item, option_kind(row["slot"]), row["slot"], row["id"], value, "memory:Replay.UnitInfo")
        option["valueSN"] = row["valueSN"]
        out.append(option)
    return out


def break_level_candidates(names, item, level, bonus):
    """돌파로 오른 주 능력치가 bonus 인 돌파 단계들 (GetBreakMainAttr). 주 능력치를 올리지 않는 단계가 있어 여럿일 수 있다."""
    steps = names.equip_breaks.get(str(item.get("q"))) or []
    base = max(math.floor(item.get(flat, 0) + item.get(growth, 0) * (level - 1) + 1e-9)
               for flat, growth in (("atk", "gAtk"), ("def", "gDef"), ("hp", "gHp")))
    up, out = 0, []
    for stage in range(len(steps) + 1):
        if stage:
            if level < (steps[stage - 1].get("needLv") or 0):
                break  # 이 단계는 장비 레벨이 모자라 돌파할 수 없다
            if steps[stage - 1].get("effect") == "MainAttrUp":
                up += steps[stage - 1].get("add") or 0
        if math.floor(base * (1 + up) + 1e-9) - base == round(bonus):
            out.append(stage)
    return out


def equip_spec(names, slot, mem, bonus):
    """장비 한 칸. bonus 는 돌파로 오른 주 능력치 (능력치 이름, 값) 또는 None."""
    if mem is None:
        return None
    item = names.equip_items.get(mem["id"])
    stat, value = bonus or (None, 0)
    candidates = break_level_candidates(names, item, mem["lv"], value) if item else []
    return {"slot": slot, "id": mem["id"], "name": (item or {}).get("name"), "quality": (item or {}).get("q"), "level": mem["lv"],
            "breakBonus": value, "breakBonusStat": stat, "breakLevel": candidates[0] if len(candidates) == 1 else None,
            "breakLevelCandidates": candidates, "options": memory_options(names, item, mem),
            "template": {k: (item or {}).get(k) for k in ("atk", "def", "hp", "gAtk", "gDef", "gHp", "skills", "skillDesc")} if item else None}


def parse_battle_tokens(raw):
    """UnitInfo.extraSkills 를 순서대로 [(id, 값)] 으로. 값이 없는 조각(속성 강화 등급, 최종 스킬, 수치 없는 옵션)의 값은 None."""
    tokens = []
    for token in (raw or "").split("|"):
        parts = token.split(",")
        if parts[0].isdigit():
            try:
                tokens.append((int(parts[0]), float(parts[2]) if len(parts) >= 3 else None))
            except ValueError:
                tokens.append((int(parts[0]), None))
    return tokens


def resonance_spec(names, role_id, unit, tokens):
    """공명 강화. 게임이 전투에 넘긴 값에서 되짚는다 (GetRoleResonanceExSkillStr, GetRoleSkillLevel). 반환: (목록, 쓴 조각 id).

    속성 강화와 skillActiveUpgrade 가 없는 스킬 강화는 extraSkills 에, 있는 스킬 강화는 skill1~3Lv (강화 레벨 + 1) 에 들어간다.
    """
    values = dict(tokens)
    used = set()
    skill_levels = [unit["skill1Lv"], unit["skill2Lv"], unit["skill3Lv"]]
    role_skills = [row.get("skillId") for row in (names.records.get(str(role_id)) or {}).get("skillList") or []]
    out = []
    for number, node in enumerate(names.reso.get(str(role_id)) or [], 1):
        attrs = []
        for slot, attr in enumerate(node.get("attr") or []):
            grades, amounts = attr.get("grades") or [], attr.get("vals") or []
            used.update(grades)
            level = next((i + 1 for i, grade in enumerate(grades) if grade in values), 0)
            attrs.append({"slot": slot, "stat": attr.get("stat"), "level": level, "maxLevel": len(amounts),
                          "value": amounts[level - 1] if 0 < level <= len(amounts) else 0})
        skill = node.get("skill") or {}
        skill_row = None
        if skill:
            upgrades = {row.get("id") for row in (names.records.get(str(node.get("id"))) or {}).get("skillActiveUpgrade") or []}
            step = skill.get("step") or 0
            level, passed_by = None, None
            if upgrades:
                index = next((i for i, skill_id in enumerate(role_skills[:len(skill_levels)]) if skill_id in upgrades), None)
                if index is not None:
                    level, passed_by = max(skill_levels[index] - 1, 0), f"skill{index + 1}Lv"
            else:
                used.add(skill.get("id"))
                value = values.get(skill.get("id"))
                level, passed_by = round(value / step) if value and step else 0, "extraSkills"
            amount = round(level * step, 6) if level is not None else None
            shown = None
            if amount is not None:
                shown = f"{amount * 100:.1f}%" if skill.get("pct") else f"{amount * (skill.get('show') or 1):.{skill.get('digits') or 0}f}"
            skill_row = {"id": skill.get("id"), "name": skill.get("name"), "desc": skill.get("desc"), "level": level, "maxLevel": skill.get("max"),
                         "levelPassedBy": passed_by, "value": amount, "isPercent": bool(skill.get("pct")), "display": shown}
        out.append({"index": number, "talentId": node.get("id"), "name": node.get("name"), "desc": node.get("desc"),
                    "open": number <= unit["resonanceLv"], "skillEnhance": skill_row, "attrs": attrs})
    return out, used


def pet_bonus(unit):
    """펫이 주는 능력치 (0 이 아닌 것만). 메모리를 못 읽었으면 None."""
    if unit is None:
        return None
    return [{"id": row["id"], "stat": PET_OPTIONS[row["id"]], "value": round(row["valueSN"] / 10000, 4), "valueSN": row["valueSN"]}
            for row in unit["pets"] if row["valueSN"]]


def member_spec(names, role_id, order, unit, leader, attrs, warnings):
    """spec.team 의 한 칸. 이번 전투에 실제로 들어간 메모리 값만 쓴다. 못 읽었으면 육성 항목은 비워 둔다."""
    out = {"order": order, "id": role_id, "name": names.role(role_id, ""), "leader": role_id == leader, "level": None, "breakthrough": None,
           "resonanceStage": None, "resonanceEnhance": None, "finalSkill": None, "teamwork": None, "skillLevels": None, "cardCounts": None,
           "unitViewId": None, "roleIndex": None, "equips": [None] * EQUIP_SLOTS, "equipExtraOptions": None, "petBonus": None,
           "extraSkillsRaw": None, "attrsAtStartSN": attrs}
    if unit is None:
        warnings.append(f"{names.role(role_id, '')}: 전투 메모리에서 육성 정보를 찾지 못했습니다.")
        return out
    tokens = parse_battle_tokens(unit["extraSkills"])
    ids = {token for token, _value in tokens}
    enhance, used = resonance_spec(names, role_id, unit, tokens)
    final_id = (names.records.get(str(role_id)) or {}).get("finalSkill")
    if final_id:
        used.add(final_id)
    # 장비 추가 옵션 중 4·5번은 UnitInfo 옵션 칸에도 있다. 펫이 그 칸을 차지하면 extraSkills 에만 남는다.
    in_slots = collections.Counter(row["id"] for equip in unit["equips"] if equip for row in equip["options"] if row["slot"] >= 4)
    bonuses, extras = {}, []
    for token, value in tokens:
        if token in EQUIP_BREAK_TOKENS:
            slot, stat = EQUIP_BREAK_TOKENS[token]
            bonuses[slot] = (stat, value)
        elif token in used:
            continue
        elif in_slots[token]:
            in_slots[token] -= 1
        else:
            extras.append(option_row(names, None, "extra", None, token, value, "memory:UnitInfo.extraSkills"))
    out.update({
        "level": unit["lv"], "breakthrough": unit["awakeLv"], "resonanceStage": unit["resonanceLv"], "resonanceEnhance": enhance,
        "finalSkill": {"id": final_id, "unlocked": final_id in ids} if final_id else None, "teamwork": unit["trustLv"],
        "skillLevels": [unit["skill1Lv"], unit["skill2Lv"], unit["skill3Lv"]], "cardCounts": [unit["card1Num"], unit["card2Num"], unit["card3Num"]],
        "unitViewId": unit["unitViewId"], "roleIndex": unit["roleIndex"],
        "equips": [equip_spec(names, slot, unit["equips"][slot], bonuses.get(slot)) for slot in range(EQUIP_SLOTS)],
        "equipExtraOptions": extras, "petBonus": pet_bonus(unit), "extraSkillsRaw": unit["extraSkills"],
    })
    return out


SPEC_NOTES = {
    "purpose": "전투에 들어간 편성의 세부 스펙이다. 게임 데이터가 없어도 이 파일만으로 해석할 수 있게 적었다.",
    "source": "육성 값은 전부 이번 전투의 메모리(Replay.UnitInfo)에서 읽었다. 로그인 때 찍히는 Player.log 는 쓰지 않는다. 경험치처럼 전투에 넘어가지 않는 값은 기록되지 않는다.",
    "SN":"이름이 SN 으로 끝나는 값과 *SN 사전은 정수 고정소수: 실제 값 = SN / 10000. 예: Atk 8078400 = 807.84, CriDamage 5000 = 50%(0.5).",
    "attrsAtStartSN": "전투 상태가 '전투 중'이 된 첫 틱에 읽은 유닛의 최종 Property (0 아닌 값만, SN). attrsCapturedFrame 이 그 프레임(60프레임=1초). 시작 패시브가 이미 들어갔을 수 있다.",
    "breakthrough": "UI 의 돌파(별). 게임 내부 필드 이름은 awake_lv 이다.",
    "resonanceStage": "UI 의 공명 단계 (resonance_lv, 0~5).",
    "teamwork": "UI 의 팀워크/默契 (trust_lv). 2레벨마다 성장치 +1.",
    "resonanceEnhance": "공명 단계 순서(index)별 강화. attrs[] = 속성 강화(stat 에 더하는 고정값 value, 레벨 0~5). skillEnhance = 스킬 강화(레벨 0~10, value=레벨×단계, isPercent 면 1=100%). levelPassedBy 는 전투로 넘어간 경로: extraSkills(버프형 강화), skill1Lv~skill3Lv(스킬 계수표 레벨. 게임 값은 강화 레벨+1), null(전투로 넘어가는 경로가 없어 레벨을 알 수 없음, level 도 null).",
    "finalSkill": "캐릭터 최종 스킬. unlocked 는 이번 전투에 들어갔는지다. 최종 스킬이 없는 캐릭터는 null.",
    "skillLevels": "[스킬1, 스킬2, 스킬3] 레벨. 기본 1, 공명 스킬 강화가 있으면 강화 레벨+1. cardCounts 는 덱에 넣은 카드 장수 [스킬1, 스킬2, 스킬3]이고 -1 은 편성에서 따로 정하지 않았다는 뜻(기본 장수).",
    "equips": "칸 0~2. null 이면 미장착이거나 그 편성에서 끈 칸. level=장비 레벨. breakBonus=장비 돌파로 오른 주 능력치(breakBonusStat 에 더하는 고정값, 전투에 넘어간 값 그대로). breakLevel=돌파 단계. 주 능력치를 올리지 않는 돌파 단계가 있어 breakLevelCandidates 가 여럿이면 null 이다.",
    "equips.options": "slot 은 게임 random_affix 번호(0 고정 스킬, 1~3 랜덤, 4·5 추가). kind: fixedSkill(장비 고유 스킬, 수치 없음) / random(랜덤 옵션) / extra(추가 옵션). value 는 게임 원값(수치 없는 옵션은 null), valueSN 은 메모리 값(=value×10000), name 은 게임 설명 원문(%s 는 자리표시자), displayValue·text 는 화면 표기.",
    "equips.template": "게임 데이터의 장비 기본값. atk/def/hp 는 기본 수치, gAtk/gDef/gHp 는 레벨 성장 수치, skills·skillDesc 는 고유 스킬.",
    "equipExtraOptions": "장비 옵션 칸에 없고 extraSkills 로만 전달된 추가 옵션(펫 능력치가 칸을 차지했거나 6번 이후 옵션). 어느 장비 것인지는 문자열로 구분되지 않지만 전투 효과는 캐릭터 단위로 같다.",
    "petBonus": "펫이 주는 고정 능력치(stat 에 value 를 더함). 0 인 항목은 뺐다. 빈 목록은 펫 보너스 없음, null 은 메모리를 못 읽음.",
    "battle.init": "spec.battle 의 isBattleTest·isArena·playerTeamNO·enemyLevelMin·difficulty·bgId·enemyRn·weatherList·weatherCount·weatherRateSN·enemyLevelOffset·secondWeatherList·weatherSecondRateSN·secondWeatherCount 는 ReplayManager 가 InitBattle 로 받은 관문 인자 그대로다(필드 이름도 게임 그대로). weatherList/secondWeatherList 는 날씨 후보 id 배열(null 은 게임 값이 null), weatherRateSN 은 날씨가 걸릴 확률(SN, -1 이면 관문 기본값). 실제로 정해진 날씨는 conditions.weatherId/secondWeatherId.",
    "extraSkillsRaw": "게임이 전투에 넘긴 원문. '|' 로 나뉜 순서: 공명별 속성등급id, 버프형 스킬강화 'id,태그,값', 최종 스킬 id, 이어서 장비별 추가옵션 'id[,A,값]', 돌파 패시브 'id,A,오른 능력치'.",
    "autoUse":"code 는 게임 '커스텀 세팅 > 클립보드 내보내기'와 같은 형식 base64(raw deflate(UTF-8 JSON)). decoded 는 그 JSON. cards 는 순위 순서. useType: 1 항상, 2 사용 안 함, 3 이상은 카드별 조건/대상(useTypeLabel). 버리기 항목(isDiscardEntry)의 useType 은 별도 의미. expectedWeight 는 전투 AI 가중치 기대값.",
    "autoUse.on": "true 면 이 전투에서 자동 사용이 켜져 있었다 (TeamData.isUseCardAI 의 마지막 값, 못 읽으면 레지스트리).",
    "code bytes": "레지스트리 JSON 을 다시 인코딩한 문자열이라, 해석 결과는 같아도 게임 문자열과 바이트까지 같다는 보장은 없다.",
    "time": "frame 은 60프레임=1초.",
}


def compose_spec(names, state, battle):
    """지금까지 모은 값으로 기록 파일의 spec 을 만든다. 계정 식별자는 넣지 않는다."""
    warnings = []
    replay = state.replay
    conditions = battle.get("conditions") or {}
    units = sorted(replay["units"], key=lambda u: u["roleIndex"]) if replay else []
    if units and len({u["roleIndex"] for u in units}) != len(units):
        units = list(replay["units"])
    by_id = {u["id"]: u for u in units}
    party = list(by_id) or [r for r in conditions.get("roleOrder") or [] if str(r) in (battle.get("roles") or {})]
    if not party:
        party = [int(key) for key in (battle.get("roles") or {}) if str(key).isdigit()]
    leader_card = conditions.get("leaderCardId")
    leader = (battle.get("cardOwners") or {}).get(str(leader_card)) if leader_card else None
    if leader not in party:
        leader = None
        if leader_card and party:
            guess = names.owner(leader_card, party)
            leader = int(guess) if guess else None

    if replay is None:
        reason = f": {state.replay_error}" if state.replay_error else ""
        warnings.append(f"전투 메모리(Replay.UnitInfo)를 읽지 못했습니다{reason}. 이 전투의 육성 정보는 비어 있습니다.")
    elif replay.get("isReplay"):
        warnings.append("리플레이 재생 전투입니다. 스펙은 리플레이에 저장된 값입니다.")
    init = (replay or {}).get("init") or {}
    if replay and not init:
        warnings.append(f"{replay.get('initError') or 'ReplayManager 관문 인자를 읽지 못했습니다'}. spec.battle 에 날씨 후보가 없습니다.")

    try:
        auto = auto_use_spec(names, state, party, leader, replay["levelId"] if replay else None, warnings)
    except (TRANSIENT + (zlib.error,)) as exc:
        auto = None
        warnings.append(f"자동 사용 정보를 해석하지 못했습니다: {type(exc).__name__}")
    team = [member_spec(names, role_id, order, by_id.get(role_id), leader, (state.attrs or {}).get(role_id), warnings)
            for order, role_id in enumerate(party, 1)]
    if party and not state.attrs_complete:
        warnings.append("전투 시작 시 최종 속성을 일부 또는 전부 읽지 못했습니다 (attrsAtStartSN 이 null 인 캐릭터).")
    if battle.get("startFrame", 0) > MID_BATTLE_FRAMES:
        warnings.append("미터를 전투 도중에 켠 기록입니다. attrsAtStartSN 은 시작 시점 값이 아닐 수 있습니다.")
    sources = {
        "team": "memory:Replay.UnitInfo (이번 전투)" if replay else "없음",
        "resonanceEnhance": "memory:UnitInfo.extraSkills, skill1~3Lv" if replay else "없음",
        "attrsAtStartSN": "memory:Unit.Property" if state.attrs else "없음",
        "autoUse": "registry:PlayerPrefs + memory:CardAICore 대조",
        "names": "web/data/game.js",
    }
    return {
        "specVersion": SPEC_VERSION,
        "notes": SPEC_NOTES,
        "autoUse": auto,
        "team": team,
        "battle": {"levelId": replay["levelId"] if replay else None, "randomSeed": replay["randomSeed"] if replay else None,
                   "playerLv": replay["playerLv"] if replay else None, "enemyIds": replay["enemyIds"] if replay else None,
                   "enemyLevel": replay["enemyLv"] if replay else None, "extraCards": replay["extraCards"] if replay else None,
                   "trainWeaponSkills": replay["trainWeaponSkills"] if replay else None, "teamAttrsAtStartSN": state.team_attrs,
                   "attrsCapturedFrame": state.attrs_frame, **init,
                   "weatherEtc": "날씨 후보는 weatherList 등(ReplayManager), 실제로 정해진 날씨는 conditions.weatherId 참조"},
        "sources": sources,
        "warnings": list(dict.fromkeys(warnings)),
    }


def new_spec_state():
    """전투 하나의 세부 스펙 수집 상태."""
    return types.SimpleNamespace(
        slots=None, flags=None, prefs_error=None, slot_key=None, slot_changed=False,
        replay=None, replay_error=None, weights=None, attrs=None, attrs_complete=False, attrs_frame=None, team_attrs=None,
        ai_last=None, ai_ever=False, ticks=0, memory_done=False)


def lineup_view(spec):
    """화면용: 자동 사용 코드와 캐릭터별 레벨·장비만. 공명·팀워크·옵션·속성은 넣지 않는다."""
    if not isinstance(spec, dict):
        return None
    auto = spec.get("autoUse") or {}
    source = auto.get("source") or {}
    team = []
    for member in spec.get("team") or []:
        # enabledInTeamPreset 은 specVersion 1 기록에만 있다
        equips = [{"id": e.get("id"), "name": e.get("name"), "lv": e.get("level")} if e and e.get("enabledInTeamPreset") is not False else None
                  for e in (member.get("equips") or [])[:EQUIP_SLOTS]]
        equips += [None] * (EQUIP_SLOTS - len(equips))
        team.append({"id": member.get("id"), "name": member.get("name"), "leader": bool(member.get("leader")),
                     "lv": member.get("level"), "equips": equips})
    return {"code": auto.get("code"), "on": auto.get("on"), "codeMissing": source.get("matchedBy") if not auto.get("code") else None, "team": team}


def cost_units(sn):
    return round(sn / 10000, 2)


def leader_percent(conditions):
    """리더 조건들의 progress/max 평균 (%). 조건이 없으면 None."""
    if not conditions:
        return None
    ratios = [min(max(c["progress"] / c["max"], 0), 1) if c["max"] > 0 else 0 for c in conditions]
    return round(sum(ratios) / len(ratios) * 100)


def max_window(flow, seconds):
    """flow 의 누적 피해에서 seconds 초 창의 최대 피해. 전투 도중에 켠 경우 그 전 누적분은 세지 않는다."""
    best, base, left = 0, (flow[0][6] if flow else 0), 0
    for row in flow:
        while flow[left][0] <= row[0] - seconds:
            base = flow[left][6]
            left += 1
        best = max(best, row[6] - base)
    return best


def last_window(flow, seconds):
    """전투 마지막 seconds 초의 피해. 결과 화면 '10초 동안 총 피해'는 마지막 600프레임의 합이다."""
    if not flow:
        return 0
    start = flow[-1][0] - seconds
    return flow[-1][6] - next(row[6] for row in flow if row[0] >= start)


def estimate_used_cost(flow, cards):
    """결과 화면 '사용한 비용' 추정: 카드를 쓰기 직전 손패 표본에서 읽은 비용의 합.

    게임은 카드마다 지불 비용을 더한다. 같은 순간 돌려받은 비용이 막대에는 안 보이므로 막대 순감소보다 크다.
    손패 표본의 비용은 근사값이고, 표본에 없던 카드(리더 제외)는 빼고 그 장수를 함께 돌려준다."""
    total, unknown, at = 0, 0, 0
    if not flow:
        return 0, 0
    for card in cards:
        if card.get("auto"):
            continue
        while at + 1 < len(flow) and flow[at + 1][0] <= card["t"]:
            at += 1
        cost = next((item[1] for item in flow[at][3] if item[2] == card["id"]), None)
        if cost is not None:
            total += cost
        elif not card.get("leader"):
            unknown += 1
    return round(total, 2), unknown


def summarize(battle):
    """저장 파일과 화면에 쓰는 요약. 구버전 전투는 없는 값이 0 이 된다."""
    skills = list((battle.get("skills") or {}).values())
    cards = battle.get("cards") or []
    ledger = battle.get("ledger") or {}
    flow = battle.get("flow") or []
    hands = [len(row[3]) for row in flow]
    max_cast, max_cast_card = 0, None
    for row in skills:
        for cast in row.get("casts") or ():
            if cast[1] > max_cast:
                max_cast, max_cast_card = cast[1], row.get("name")
    used_cost, unknown_cards = estimate_used_cost(flow, cards)
    return {
        "usedCards": sum(s.get("use", 0) for s in skills),
        "autoCards": sum(s.get("passive", 0) for s in skills),
        "cardEvents": len(cards),
        "shownCost": round(sum(c.get("shown") or 0 for c in cards), 2),
        "paidCost": cost_units(ledger.get("spentSN", 0)),
        "usedCostEstimate": used_cost,
        "usedCostUnknownCards": unknown_cards,
        "natural": cost_units(ledger.get("naturalSN", 0)),
        "start": cost_units(ledger.get("startSN", 0)),
        "gained": cost_units(ledger.get("gainedSN", 0)),
        "overflow": cost_units(ledger.get("overflowSN", 0)),
        "otherSpent": cost_units(ledger.get("otherSpentSN", 0)),
        "avgHand": round(sum(hands) / len(hands), 2) if hands else 0,
        "maxHand": max(hands, default=0),
        "damageAt10s": next((row[6] for row in flow if row[0] >= 10), 0),
        "max10s": max_window(flow, 10),
        "last10s": last_window(flow, 10),
        "maxCast": max_cast,
        "maxCastCard": max_cast_card,
    }


def top_level_fields(text, wanted):
    """JSON 객체의 최상위 키를 앞에서부터 읽어 wanted 만 모은다. 문자열이 잘렸으면 모은 데까지만 돌려준다."""
    decoder = json.JSONDecoder()
    separator, colon = re.compile(r"[\s,]*"), re.compile(r"\s*:\s*")
    out = {}
    try:
        at = text.index("{") + 1
        while len(out) < len(wanted):
            at = separator.match(text, at).end()
            if text[at] != '"':
                break
            key, at = decoder.raw_decode(text, at)
            at = colon.match(text, at).end()
            value, at = decoder.raw_decode(text, at)
            if key in wanted:
                out[key] = value
    except (ValueError, IndexError, AttributeError):
        pass
    return out


def party_of(battle):
    """목록에 보여 줄 조합: 출전 순서대로 [{id, name, leader}]. 출전 순서가 없는 구버전 기록은 피해 순서."""
    roles = battle.get("roles") or {}
    conditions = battle.get("conditions") or {}
    order = [str(r) for r in conditions.get("roleOrder") or [] if str(r) in roles]
    rest = sorted((key for key in roles if key not in order), key=lambda key: -roles[key].get("damage", 0))
    leader = str((battle.get("cardOwners") or {}).get(str(conditions.get("leaderCardId"))))
    return [{"id": roles[key].get("id", key), "name": roles[key].get("name") or key, "leader": key == leader}
            for key in order + rest]


def battle_meta(battle, path):
    """전투 목록의 한 줄. 파일 앞부분에서 읽은 필드만으로도 만들 수 있어야 한다."""
    return {"id": battle["id"], "server": battle.get("server"), "started": battle["started"], "live": bool(battle.get("live")),
            "total": sum(r.get("damage", 0) for r in battle["roles"].values()), "party": party_of(battle),
            "seconds": battle.get("game_duration") or (battle.get("frame") or 0) / 60, "path": path}


def read_meta(path):
    """이력 목록에 쓸 메타. 파일 앞부분만 읽고, 모자라면 전체를 읽는다."""
    try:
        with open(path, encoding="utf-8") as f:
            head = f.read(META_HEAD_CHARS)
        fields = top_level_fields(head, META_FIELDS)
        if not {"id", "started", "roles"} <= fields.keys():
            fields = json.loads(Path(path).read_text(encoding="utf-8"))
        return battle_meta(fields, str(path))
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return None


class Meter:
    def __init__(self, log_dir):
        self.log_dir = Path(log_dir)
        self.names = Names()
        self.lock = threading.RLock()
        self.reader = None
        self.status = "게임을 찾는 중"
        self.error = ""
        self.armed = True  # 측정 대기: 켜져 있는 동안 시작되는 전투만 기록한다. 켜면 바로 대기 (2026-11-16 — 그 전엔 꺼진 채 시작)
        self.halted = False
        self.blocked_pid = None  # 읽기가 막힌 게임의 pid (그 게임에는 다시 시도하지 않는다)
        self.errors = 0
        self.pid_checked = 0.0
        self.current = None
        self.result = 0
        self.closed = None  # (직전에 닫은 result 포인터, 닫을 때 프레임)
        self.prev = None
        self.history = []  # 메타만 둔다. 본문은 self.bodies 와 파일에 있다.
        self.bodies = collections.OrderedDict()
        self.sent = self._load_sent()  # 서버에 보낸 기록 파일 이름
        self._reset_battle()
        self._load_history()
        threading.Thread(target=self.names._build_edges, daemon=True).start()

    def _reset_battle(self):
        """전투 하나를 기록하는 동안만 쓰는 상태."""
        self.cost_prev = None
        self.cost_before = 0
        self.pending_cost = 0
        self.unpaid = collections.deque()
        self.spends = collections.deque()  # (프레임, 감소량 SN, 감소 후 비용 SN)
        self.card_count = 0
        self.op_count = 0
        self.pending_ops = collections.deque()  # 아직 카드와 짝짓지 못한 조작 기록
        self.tick_use, self.tick_passive = {}, {}
        self.flow_bucket = self.buff_bucket = self.condition_bucket = None
        self.buff_frame = None
        self.last_frame = None
        self.last_frame_at = 0.0
        self.last_leader = None
        self.last_team = {}
        self.unit_keys, self.unit_counts = {}, {}
        self.tick_units = self.tick_unit_states = None
        self.poll_count = self.poll_errors = self.buff_samples = 0
        self.poll_sum = self.poll_max = self.poll_gap = 0.0
        self.poll_last = None
        self.wall_start = time.monotonic()
        self.seen_frame = None  # 마지막으로 전부 읽은 게임 프레임
        self.full_at = 0.0
        self.frame_samples = self.frames_skipped = 0
        self.action_state = {}  # 유닛 키 → 지금 기록 중인 동작 행
        self.dot_state = {}  # 주기 효과 인스턴스 포인터 → (프레임 카운터, 간격, 본 프레임)
        self.spec_state = None

    def _load_history(self):
        files = sorted(self.log_dir.glob("*.json"), reverse=True)[:MAX_HISTORY] if self.log_dir.exists() else []
        for path in files:
            meta = read_meta(path)
            if meta:
                self.history.append(meta)

    def attach(self):
        if self.reader:
            return True
        pid = find_pid()
        if not pid:
            self.status, self.error = "게임이 실행 중이 아닙니다", ""
            return False
        self.reader = Reader(pid)
        self.pid_checked = time.monotonic()
        self.error = ""
        return True

    def detach(self, reason="detached"):
        if self.current:
            self.finish(reason=reason)
        if self.reader:
            self.reader.close()
        self.reader, self.closed = None, None

    def _process_alive(self):
        """3초마다 게임 프로세스가 그대로인지 확인한다."""
        now = time.monotonic()
        if now - self.pid_checked < PID_CHECK_SECONDS:
            return True
        self.pid_checked = now
        if find_pid(self.reader.pid) == self.reader.pid:
            return True
        self.detach("game_exit")
        self.status = "게임이 실행 중이 아닙니다"
        return False

    def idle(self):
        reader = self.reader
        if not reader.klass:
            if not reader.resolve_classes():
                self.status = "전투 코드 초기화 대기 중"
                return
            self.error = ""
        if self.armed:
            ctx = reader.context()
            if ctx and not (self.closed and self.closed[0] == ctx.result and ctx.frame >= self.closed[1]):
                snap = reader.snapshot(ctx.result)
                if snap and snap["duration"] == 0 and snap["roles"]:
                    return self.begin(ctx, snap)
        self.status = self.waiting_status()

    def waiting_status(self):
        return "측정 대기 중" if self.armed else "측정 안 함"

    def set_armed(self, on):
        """측정 대기 켜기·끄기. 끄더라도 이미 기록 중인 전투는 끝까지 기록한다."""
        with self.lock:
            self.armed = bool(on)
            if not self.current and self.reader and self.reader.klass:
                self.status = self.waiting_status()
            return self.armed

    def begin(self, ctx, snap):
        reader = self.reader
        reader.clear_caches()
        snap = reader.snapshot(ctx.result) or snap  # 이전 전투의 문자열 캐시로 읽은 이름을 버린다.
        self._reset_battle()
        now = time.time()
        battle = {
            "schemaVersion": SCHEMA_VERSION, "id": int(now * 1000), "server": SERVER, "build": reader.build(),
            "started": now, "ended": None, "live": True,
            "endReason": None, "game_duration": None, "pollHz": POLL_HZ,
            "timeBase": "frame/60",  # 게임 타이머 기준. 시뮬 시각+3초≈게임 시각
            "attrsUnit": "SN=값x10000", "startFrame": ctx.frame, "frame": ctx.frame, "state": ctx.state,
            "firstHitFrame": None, "first_hit": None, "last_hit": None, "gameTotalSN": 0,
            "conditions": {"leaderCardId": None, "leaderCard": None, "roleOrder": []},
            "roles": {}, "skills": {}, "cardOwners": {}, "timeline": {}, "byRole": {}, "log": [], "cards": [], "costGains": [],
            "ledger": {"openingSN": 0, "naturalSN": 0, "startSN": 0, "gainedSN": 0, "spentSN": 0, "otherSpentSN": 0,
                       "overflowSN": 0, "capFrames": 0, "frames": 0, "pendingSN": 0, "currentSN": 0},
            "flow": [], "leaderProgress": [], "units": {}, "buffEvents": [], "snapshots": [], "ops": [], "now": None,
            # hits: [프레임, 캐릭터 id, 그 프레임의 피해 증가, 그중 카드에 귀속된 양]
            # actions: [시작 프레임, 유닛 키, 동작 id, 카드 id, 플래그(1 일반 공격, 2 리더 스킬), 전체 프레임,
            #           처음 본 진행 프레임, 마지막으로 진행한 프레임, 마지막 진행 프레임 값]
            # dotTicks: [프레임, buff id, 건 캐릭터 id, 인스턴스, 틱 수] — 적에게 걸린 아군의 주기 효과가 틱을 낸 프레임
            "hits": [], "actions": [], "dotTicks": [],
            "summary": None, "metrics": {},
            "spec": None,  # 목록은 파일 앞부분만 읽으므로 긴 필드는 뒤에 둔다
        }
        # 미터를 전투 도중에 켠 경우: 이미 쌓인 cardOrder 는 시각을 모르므로 주인 정보만 쓴다.
        for item in reader.card_order(snap["cardOrder"], 0):
            self._note_owner(battle, item)
            self.card_count += 1
        try:
            self.op_count = len(reader.operation_logs(ctx.replay_manager, 0))
        except TRANSIENT:
            self.op_count = 0
        self.spec_state = new_spec_state()
        self._read_prefs(self.spec_state)
        with self.lock:
            self.current, self.result, self.prev = battle, ctx.result, snap
            self.last_frame, self.last_frame_at = ctx.frame, time.monotonic()
            self.closed, self.error = None, ""
            self.status = STATE_NAMES.get(ctx.state, "전투 중")
            self.update(ctx, snap)
        self._refresh_spec(battle, self.spec_state)

    @staticmethod
    def _read_prefs(state):
        """자동 사용 설정을 레지스트리에서 읽는다. 실패해도 기록은 계속한다."""
        try:
            texts, state.flags = read_card_prefs()
            state.slots = parse_card_slots(texts)
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
            state.prefs_error = type(exc).__name__  # 메시지에는 사용자 폴더 경로가 들어갈 수 있다

    def _refresh_spec(self, battle, state):
        """지금까지 모은 값으로 spec 을 다시 만든다. 어떤 실패도 전투 기록을 막지 않는다."""
        with self.lock:
            try:
                battle["spec"] = compose_spec(self.names, state, battle)
            except Exception as exc:  # noqa: BLE001 - 폴링 스레드까지 번지면 전투 기록이 끊긴다.
                print("세부 스펙을 만들지 못했습니다:", type(exc).__name__, file=sys.stderr)
                battle["spec"] = {"specVersion": SPEC_VERSION, "autoUse": None, "team": [],
                                  "warnings": [f"세부 스펙을 만들지 못했습니다: {type(exc).__name__}"]}

    def _capture_spec(self, ctx):
        """전투 시작 부근에 메모리의 세부 스펙을 읽는다. 다 읽었거나 60초가 지나면 멈춘다."""
        state = self.spec_state
        if state is None:
            return
        state.ai_last = ctx.use_card_ai
        state.ai_ever = state.ai_ever or ctx.use_card_ai
        if state.memory_done:
            return
        state.ticks += 1
        if (state.ticks - 1) % SPEC_RETRY_TICKS == 0:
            try:
                self._read_spec_memory(ctx, state)
            except TRANSIENT as exc:
                state.replay_error = state.replay_error or type(exc).__name__
                self.poll_errors += 1
        have_all = state.replay and state.attrs_complete and (state.weights or not ctx.use_card_ai)
        if have_all or state.ticks >= SPEC_MAX_TICKS:
            state.memory_done = True
            self._refresh_spec(self.current, state)

    def _read_spec_memory(self, ctx, state):
        reader = self.reader
        if state.replay is None:
            state.replay, state.replay_error = reader.replay_info(ctx.replay_manager)
        if not state.weights and ctx.ai_core:
            state.weights = reader.dict_int_int(reader.u64(ctx.ai_core + 0xD8)) or None
        if state.attrs_complete or ctx.state != STATE_FIGHTING:
            return
        party = {u["id"] for u in state.replay["units"]} if state.replay else {int(k) for k in self.current["roles"] if str(k).isdigit()}
        found = {}
        for unit in self._live_units(ctx):
            if unit["team"] == ALLY_TEAM and unit["id"] in party and unit["id"] not in found:
                values = {k: v for k, v in reader.property_values(unit["property"]).items() if v}
                if values:
                    found[unit["id"]] = values
        if len(found) > len(state.attrs or {}):
            state.attrs, state.attrs_frame = found, ctx.frame
            state.team_attrs = {k: v for k, v in reader.property_values(ctx.team_property).items() if v}
        state.attrs_complete = bool(party) and party <= set(found)

    def _close_spec(self):
        """전투가 끝날 때: 레지스트리가 바뀌었는지 보고, 마지막으로 spec 을 맞춘다."""
        state, battle = self.spec_state, self.current
        if state is None or battle is None:
            return
        self.spec_state = None
        slot = (state.slots or {}).get(state.slot_key)
        if slot:
            try:
                texts, _flags = read_card_prefs()
                state.slot_changed = texts.get(state.slot_key) != slot["text"]
            except OSError:
                pass
        self._refresh_spec(battle, state)

    @staticmethod
    def _note_owner(battle, item):
        if item["owner"] > 0:
            battle["cardOwners"][str(item["id"])] = item["owner"]

    def _owner_of(self, card_id, snap):
        """카드 주인: cardOrder 의 ownerId 우선, 없으면 게임 데이터 참조 거리."""
        owner = self.current["cardOwners"].get(str(card_id))
        if owner is not None and owner in snap["roles"]:
            return str(owner)
        return self.names.owner(card_id, snap["roles"])

    def tick(self):
        began = time.perf_counter()
        reader = self.reader
        ctx = reader.context()
        if ctx is None:
            return self.finish(reason="context_lost")
        if ctx.result != self.result:
            return self.finish(reason="result_changed")
        now = time.monotonic()
        if ctx.frame == self.seen_frame and now - self.full_at < RECHECK_SECONDS:
            return  # 같은 게임 프레임: 다시 읽지 않는다 (멈춰 있으면 RECHECK_SECONDS 마다 읽어 종료·일시정지를 본다)
        snap = reader.snapshot(ctx.result)
        if snap is None:
            return self.finish(reason="snapshot_lost")
        ended = snap["duration"] > 0
        if self.seen_frame is not None and ctx.frame != self.seen_frame:
            self.frame_samples += 1
            self.frames_skipped += max(ctx.frame - self.seen_frame - 1, 0)
        self.seen_frame, self.full_at = ctx.frame, now
        try:
            with self.lock:
                self.update(ctx, snap)
                self._note_poll(began)
        except TRANSIENT:
            if not ended:  # 끝난 전투는 마지막 반영이 실패해도 닫아야 한다.
                raise
            self.poll_errors += 1
        if ended:
            return self.finish(game_duration=snap["duration"], reason="result")
        now = time.monotonic()
        if ctx.frame != self.last_frame:
            self.last_frame, self.last_frame_at = ctx.frame, now
        frozen = now - self.last_frame_at
        if frozen > STALE_SECONDS:
            return self.finish(reason="stale")
        self.status = "일시정지" if frozen >= PAUSE_SECONDS else STATE_NAMES.get(ctx.state, "전투 중")

    def _note_poll(self, began):
        finished = time.perf_counter()
        elapsed = finished - began
        self.poll_count += 1
        self.poll_sum += elapsed
        self.poll_max = max(self.poll_max, elapsed)
        if self.poll_last is not None:
            self.poll_gap = max(self.poll_gap, began - self.poll_last)
        self.poll_last = began
        self.current["metrics"] = self._metrics()

    def _metrics(self):
        cur = self.current
        elapsed = time.monotonic() - self.wall_start
        frames = cur["frame"] - cur["startFrame"]
        return {
            "polls": self.poll_count,
            "avgMs": round(self.poll_sum / self.poll_count * 1000, 2) if self.poll_count else 0,
            "maxMs": round(self.poll_max * 1000, 2),
            "maxGapMs": round(self.poll_gap * 1000, 1),
            "framesPerSecond": round(frames / elapsed, 2) if elapsed > 0 else 0,
            "frameSamples": self.frame_samples, "framesSkipped": self.frames_skipped,
            "cardEvents": len(cur["cards"]),
            "flowRows": len(cur["flow"]),
            "buffSamples": self.buff_samples,
            "transientErrors": self.poll_errors,
        }

    def update(self, ctx, snap):
        """한 틱의 기록. 각 단계는 자기 상태를 스스로 갱신하므로 중간에 실패해도 이중 집계되지 않는다."""
        cur, reader, frame = self.current, self.reader, ctx.frame
        cur["frame"], cur["state"] = frame, ctx.state
        self.tick_units = self.tick_unit_states = None
        new_cards = reader.card_order(snap["cardOrder"], self.card_count)
        for item in new_cards:
            self._note_owner(cur, item)
        self.apply_damage(snap, frame)
        self.apply_actions(ctx, frame)
        self.apply_dots(ctx, frame)
        team = reader.property_values(ctx.team_property) or self.last_team
        self.last_team = team
        self.apply_cost(ctx, team, frame)
        system = reader.read(ctx.card_system, 0x110)
        self.apply_cards(ctx, snap, frame, system, new_cards)
        self.settle(frame)
        self.apply_leader(system, frame)
        bucket = frame // FLOW_FRAMES
        if bucket != self.flow_bucket:
            self.sample_flow(ctx, snap, frame, team, system)
            self.flow_bucket = bucket
        bucket = frame // BUFF_FRAMES
        if bucket != self.buff_bucket:
            self.sample_buffs(ctx, frame)
            self.buff_bucket = bucket
        bucket = frame // 60
        if bucket != self.condition_bucket:
            self._read_conditions(ctx.result)  # 게임이 먼저 꺼져도 조건이 남도록 1초마다 읽어 둔다.
            self.condition_bucket = bucket
        self._capture_spec(ctx)

    def apply_damage(self, snap, frame):
        cur, names, prev = self.current, self.names, self.prev
        t = round(frame / 60, 2)
        second = str(frame // 60)
        role_delta = {}
        for key, role in snap["roles"].items():
            old = prev["roles"].get(key, {"damage": 0})
            role_delta[key] = max(role["damage"] - old["damage"], 0)
            row = cur["roles"].setdefault(str(key), {"id": key, "name": names.role(key, role["name"])})
            row.update(damage=role["damage"], getHit=role["getHit"], heal=role["heal"], getHeal=role["getHeal"])
        cur["gameTotalSN"] = snap["gameTotalSN"]
        frame_total = sum(role_delta.values())
        if frame_total:
            if cur["firstHitFrame"] is None:
                cur["firstHitFrame"] = frame
                cur["first_hit"] = t
            cur["last_hit"] = t
            cur["timeline"][second] = cur["timeline"].get(second, 0) + frame_total
        owned, tick_use, tick_passive = {}, {}, {}
        for key, skill in snap["skills"].items():
            old = prev["skills"].get(key, {"dmg": 0, "use": 0, "passive": 0})
            row = cur["skills"].setdefault(str(key), {"id": key, "name": names.skill(key, skill["name"]), "updates": 0, "maxUpdate": 0, "casts": []})
            row.update({k: skill[k] for k in ("dmg", "heal", "findtimes", "findtargets", "take", "use", "level", "passive", "abandon")})
            used, auto = max(skill["use"] - old["use"], 0), max(skill["passive"] - old["passive"], 0)
            if used:
                tick_use[key] = used
            if auto:
                tick_passive[key] = auto
            row["casts"].extend([frame, 0] for _ in range(used + auto))
            delta = skill["dmg"] - old["dmg"]
            if delta > 0:
                row["updates"] += 1
                row["maxUpdate"] = max(row["maxUpdate"], delta)
                if not row["casts"]:  # 사용·자동 횟수 없이 들어온 피해도 시전별 합계에서 빠지지 않게 한다.
                    row["casts"].append([frame, 0])
                row["casts"][-1][1] += delta
                cur["log"].append([t, row["name"], delta])
                owner = self._owner_of(key, snap)
                if owner:
                    owned[owner] = owned.get(owner, 0) + delta
        for key, delta in role_delta.items():
            role_key = str(key)
            attributed = owned.get(role_key, 0)
            if delta or attributed:
                bucket = cur["byRole"].setdefault(role_key, {}).setdefault(second, [0, 0])
                bucket[0] += delta
                bucket[1] += attributed
            rest = delta - attributed
            if rest > 0:
                cur["log"].append([t, cur["roles"][role_key]["name"] + " · 카드 외", rest])
            if delta:
                cur["hits"].append([frame, key, delta, attributed])
        self.tick_use, self.tick_passive = tick_use, tick_passive
        self.prev = snap  # 적용 직후 바로 갱신한다 (뒤 단계에서 실패해도 이중 집계 없음).

    def apply_actions(self, ctx, frame):
        """유닛마다 지금 하는 동작을 본다. 동작이 바뀌면 actions 에 한 줄을 열고, 진행하는 동안 끝 프레임을 갱신한다."""
        cur, reader, states = self.current, self.reader, self.action_state
        for unit in self._live_units(ctx):
            if unit["key"] == "team":
                continue
            act = reader.action_of(unit["action"])
            if act is None:
                states.pop(unit["key"], None)
                continue
            action_id, progress, total, card_id, normal, leader = act
            state = states.get(unit["key"])
            if state is None or state["ptr"] != unit["action"] or state["id"] != action_id or progress < state["progress"]:
                row = [frame, unit["key"], action_id, card_id, int(normal) | int(leader) << 1, total, progress, frame, progress]
                cur["actions"].append(row)
                state = states[unit["key"]] = {"ptr": unit["action"], "id": action_id, "progress": progress, "row": row}
            elif progress != state["progress"]:
                state["progress"] = progress
                state["row"][7], state["row"][8] = frame, progress

    def apply_dots(self, ctx, frame):
        """적에게 걸린 아군의 주기 효과가 낸 틱을 기록한다.

        BuffDot 의 프레임 카운터는 0 → 간격-1 까지 오르고 틱을 내는 프레임에 0 으로 돌아간다 (2026-11-09 실측: 59 → 0).
        같은 효과를 다시 걸어 카운터가 중간에 처음부터 다시 시작한 경우(예: 47 → 1)는 틱이 아니다."""
        cur, reader, states = self.current, self.reader, self.dot_state
        units = self._live_units(ctx)
        allies = {unit["sid"]: unit["id"] for unit in units if unit["key"] != "team" and unit["team"] == ALLY_TEAM}
        seen = set()
        for unit in units:
            if unit["key"] == "team" or unit["team"] == ALLY_TEAM:
                continue
            for pointer, buff_id, from_sid, count, interval in reader.dots_of(unit["buff"]):
                seen.add(pointer)
                last = states.get(pointer)
                states[pointer] = (count, interval, frame)
                owner = allies.get(from_sid)
                # 처음 본 인스턴스와 간격이 막 바뀐 프레임(생성 직후)은 건너뛴다.
                if owner is None or interval <= 0 or last is None or last[1] != interval:
                    continue
                # 카운터가 줄었고, 지난 프레임 수만큼 더하면 간격에 닿았을 때만 틱이다.
                if count < last[0] and last[0] + (frame - last[2]) >= interval:
                    cur["dotTicks"].append([frame, buff_id, owner, pointer & 0xFFFFFF, 1])
        for pointer in [p for p in states if p not in seen]:
            del states[pointer]

    def apply_cost(self, ctx, team, frame):
        """비용 장부. 항상 opening + natural + start + gained - spent + pending == 현재 비용 이다."""
        ledger = self.current["ledger"]
        state = {"costSN": ctx.cost, "maxSN": ctx.max_cost, "startIndexSN": ctx.start_index,
                 "restoreSN": team.get("CostRestore", 0), "frame": frame}
        prev, self.cost_prev = self.cost_prev, state
        ledger["currentSN"] = ctx.cost
        if prev is None:
            self.cost_before = ctx.cost
            ledger["openingSN"] = ctx.cost
            return
        self.cost_before = prev["costSN"]
        restore = state["restoreSN"]
        frames = max(frame - prev["frame"], 0)
        natural = restore * frames if ctx.state == 4 else 0
        start_gain = max(state["startIndexSN"] - prev["startIndexSN"], 0)
        room = max(prev["maxSN"], state["maxSN"])
        expected = prev["costSN"] + natural + start_gain
        overflow = max(expected - room, 0)
        expected -= overflow
        # 넘침이 자연 회복보다 크면 그 초과분을 시작 비용에서 먼저 빼고, 그래도 남으면(상한이 줄어든 경우)
        # 미확정분으로 돌린다. 이렇게 해야 장부의 합이 실제 비용과 항상 맞는다.
        excess = max(overflow - natural, 0)
        ledger["naturalSN"] += max(natural - overflow, 0)
        ledger["startSN"] += max(start_gain - excess, 0)
        ledger["overflowSN"] += overflow
        ledger["frames"] += frames
        if ctx.cost >= state["maxSN"]:
            ledger["capFrames"] += frames
        self.pending_cost += ctx.cost - expected - max(excess - start_gain, 0)
        if abs(self.pending_cost) > max(restore * 3, 100):
            amount, self.pending_cost = self.pending_cost, 0
            if amount > 0:
                ledger["gainedSN"] += amount
                self.current["costGains"].append([frame, amount])
            else:
                ledger["spentSN"] -= amount
                self.spends.append((frame, -amount, ctx.cost))
        ledger["pendingSN"] = self.pending_cost

    def apply_cards(self, ctx, snap, frame, system, new_cards):
        if not new_cards:
            return
        cur, reader, names = self.current, self.reader, self.names
        hand = reader.link_count(u64_at(system, 0x80))
        before, after = cost_units(self.cost_before), cost_units(ctx.cost)
        pos, ai = self._unit_positions(ctx), None
        if ctx.use_card_ai and ctx.ai_core:
            try:
                ai = reader.ai_state(ctx.ai_core)
            except TRANSIENT:
                self.poll_errors += 1
        self._take_operations(ctx, frame)
        for item in new_cards:
            card_id = item["id"]
            skill = snap["skills"].get(card_id)
            name = names.skill(card_id, skill["name"] if skill else "")
            owner = item["owner"] if item["owner"] > 0 else None
            owner_row = cur["roles"].get(str(owner)) if owner else None
            owner_name = owner_row["name"] if owner_row else (names.role(owner, "") if owner else None)
            used_left, auto_left = self.tick_use.get(card_id, 0), self.tick_passive.get(card_id, 0)
            auto = auto_left > 0 and used_left == 0
            if auto:
                self.tick_passive[card_id] = auto_left - 1
            elif used_left > 0:
                self.tick_use[card_id] = used_left - 1
            card = {"frame": frame, "t": round(frame / 60, 2), "id": card_id, "name": name, "ownerId": item["owner"],
                    "ownerName": owner_name, "shown": item["shown"], "paid": 0 if auto else None, "before": before,
                    "after": after, "leader": item["leader"], "auto": auto, "noCost": item["noCost"], "hand": hand,
                    "target": None, "pos": pos, "ai": ai}
            # 게임 조작 기록은 손으로·AI 로 쓴 카드만 남는다고 보고, 자동 발동이 아닌 카드부터 순서대로 짝짓는다.
            if not auto and self.pending_ops:
                card["target"] = self.pending_ops.popleft()
            cur["cards"].append(card)
            self.card_count += 1
            if not auto:
                self.unpaid.append(card)
            if item["leader"] or item["shown"] >= 4:
                try:
                    cur["snapshots"].append({"frame": frame, "cardId": card_id, "card": name, "leader": item["leader"],
                                             "units": self._unit_states(ctx)})
                except TRANSIENT:
                    self.poll_errors += 1
        # 짝이 남은 조작 기록은 이번 틱의 자동 발동 카드에 순서대로 붙인다 (그래도 남으면 ops 에만 남는다).
        if self.pending_ops:
            for card in reversed(cur["cards"][-len(new_cards):]):
                if card["target"] is None and self.pending_ops:
                    card["target"] = self.pending_ops.popleft()

    def _take_operations(self, ctx, frame):
        """새 조작 기록을 ops 에 적고, 카드 사용 기록(cardIndex>=0)은 카드와 짝지을 대기열에 넣는다."""
        try:
            new_ops = self.reader.operation_logs(ctx.replay_manager, self.op_count)
        except TRANSIENT:
            self.poll_errors += 1
            return
        for op in new_ops:
            self.op_count += 1
            row = {"i": self.op_count - 1, "frame": op["frame"], "team": op["team"], "cardIndex": op["cardIndex"],
                   "x": op["x"], "z": op["z"], "uid": op["uid"], "refresh": op["refresh"], "teamCard": op["teamCard"]}
            self.current["ops"].append(row)
            if op["cardIndex"] >= 0 and op["team"] == ALLY_TEAM:
                self.pending_ops.append({"op": row["i"], "frame": op["frame"], "x": op["x"], "z": op["z"], "uid": op["uid"]})
        # 너무 오래 짝을 못 찾은 기록은 버린다 (카드 기록이 누락된 경우)
        while self.pending_ops and frame - self.pending_ops[0]["frame"] > SETTLE_FRAMES * 4:
            self.pending_ops.popleft()

    def _unit_positions(self, ctx):
        """이번 틱 유닛별 [팀, x_SN, z_SN, roleIndex, 생존]. 카드 대상 좌표를 유닛과 맞춰 보기 위한 것."""
        try:
            return {u["key"]: [u["team"], u["x"], u["z"], u["roleIndex"], int(u["alive"])]
                    for u in self._live_units(ctx) if u["key"] != "team"}
        except TRANSIENT:
            self.poll_errors += 1
            return None

    def settle(self, frame):
        """카드와 비용 감소를 앞에서부터 1:1 로 짝짓는다. frame 이 None 이면 남은 것을 전부 마감한다."""
        ledger = self.current["ledger"]
        while self.unpaid and self.spends:
            card = self.unpaid.popleft()
            _spent_at, amount, after = self.spends.popleft()
            card["paid"] = cost_units(amount)
            card["after"] = cost_units(after)
        while self.unpaid and (frame is None or frame - self.unpaid[0]["frame"] > SETTLE_FRAMES):
            self.unpaid.popleft()["paid"] = 0
        while self.spends and (frame is None or frame - self.spends[0][0] > SETTLE_FRAMES):
            ledger["otherSpentSN"] += self.spends.popleft()[1]

    def apply_leader(self, system, frame):
        conditions = self.reader.leader_conditions(u64_at(system, 0x70))
        if conditions:
            first = conditions[0]
            state = (first["progress"], first["max"], first["finished"])
            if state != self.last_leader:
                self.last_leader = state
                self.current["leaderProgress"].append([frame, *state])

    def sample_flow(self, ctx, snap, frame, team, system):
        """0.1초 표본. 앞 8칸은 시뮬 타임라인과 같은 순서다."""
        cur, reader, names = self.current, self.reader, self.names
        hand = [[names.skill(c["id"], c["name"]), cost_units(c["cost"]), c["id"]]
                for c in reader.hand_cards(u64_at(system, 0x80), reader.dict_int_long(ctx.adjust_cost))]
        deck, grave = reader.link_count(u64_at(system, 0x88)), reader.link_count(u64_at(system, 0xD8))
        conditions = reader.leader_conditions(u64_at(system, 0x70))
        percent = leader_percent(conditions)
        regen = round(team.get("CostRestore", 0) * 60 / 10000, 3)
        total = sum(r["damage"] for r in snap["roles"].values())
        cost = cost_units(ctx.cost)
        paid = cost_units(cur["ledger"]["spentSN"])
        cur["flow"].append([round(frame / 60, 1), cost, regen, hand, deck, grave, total, percent,
                            sum(s["use"] for s in snap["skills"].values()), paid])
        first = conditions[0] if conditions else None
        cur["now"] = {
            "cost": cost, "max": cost_units(ctx.max_cost), "regen": regen, "hand": hand,
            "handMax": team.get("HandCardMax", 0) // 10000, "deck": deck, "grave": grave, "leaderPct": percent,
            "leaderProgress": first["progress"] if first else None, "leaderMax": first["max"] if first else None,
            "autoDraw": i32_at(system, 0xA4), "autoDrawInterval": team.get("AutoDrawInterval", 0) // 10000,
        }
        conditions_row = cur["conditions"]
        if conditions_row.get("leaderCardId") is None:
            leader = reader.leader_card(u64_at(system, 0x60))
            if leader:
                conditions_row["leaderCardId"] = leader[0]
                conditions_row["leaderCard"] = names.skill(leader[0], leader[1])
        if not conditions_row.get("roleOrder"):
            conditions_row["roleOrder"] = reader.role_order(ctx.role_list)

    def _read_conditions(self, result):
        values = self.reader.result_conditions(result) if result and self.reader else None
        if values:
            self.current["conditions"].update(values)

    def _unit_key(self, pointer, unit_id):
        """유닛 키는 id 문자열이고, 같은 id 가 또 나오면 'id#2'. 포인터별로 고정한다."""
        known = self.unit_keys.get(pointer)
        if known and known[0] == unit_id:
            return known[1]
        count = self.unit_counts.get(unit_id, 0) + 1
        self.unit_counts[unit_id] = count
        key = str(unit_id) if count == 1 else f"{unit_id}#{count}"
        self.unit_keys[pointer] = (unit_id, key)
        return key

    def _live_units(self, ctx):
        """이번 틱의 유닛 목록. 팀 전체 효과는 'team' 가상 유닛으로 넣는다."""
        if self.tick_units is not None:
            return self.tick_units
        reader, names = self.reader, self.names
        units = [{"key": "team", "id": 0, "name": "팀 전체", "team": 0, "buff": ctx.buff_system, "property": ctx.team_property}]
        for team, pointer, raw in reader.units(ctx.unit_manager):
            ca = reader.unit_ca(u64_at(raw, 0x490))
            if ca:
                units.append({"key": self._unit_key(pointer, ca[0]), "id": ca[0], "name": names.role(ca[0], ca[1]),
                              "team": team, "buff": u64_at(raw, 0x440), "property": u64_at(raw, 0x230),
                              "x": i64_at(raw, 0x270), "z": i64_at(raw, 0x2A8), "roleIndex": i32_at(raw, 0xAC),
                              "alive": bool(raw[0x330]), "action": u64_at(raw, 0x260), "sid": i32_at(raw, 0x47C)})
        self.tick_units = units
        return units

    def _unit_states(self, ctx):
        """시전 순간의 스냅샷 본문 (속성은 0 이 아닌 것 전부, SN 원값). 같은 틱에는 한 번만 읽는다."""
        if self.tick_unit_states is None:
            reader, states = self.reader, {}
            for unit in self._live_units(ctx):
                attrs = {k: v for k, v in reader.property_values(unit["property"]).items() if v}
                buffs = [[buff_id, row["stacks"], row["left"]] for buff_id, row in reader.buffs_of(unit["buff"]).items()]
                states[unit["key"]] = {"attrs": attrs, "buffs": buffs}
                if unit["key"] != "team":
                    states[unit["key"]]["pos"] = [unit["team"], unit["x"], unit["z"], unit["roleIndex"], int(unit["alive"])]
            self.tick_unit_states = states
        return self.tick_unit_states

    def sample_buffs(self, ctx, frame):
        """0.2초 표본: 버프별 유지 프레임·중첩을 누적하고 중첩 변화를 이벤트로 남긴다."""
        cur, reader, names = self.current, self.reader, self.names
        dt = frame - self.buff_frame if self.buff_frame is not None else 0
        self.buff_frame = frame
        seen = set()
        for unit in self._live_units(ctx):
            seen.add(unit["key"])
            row = cur["units"].setdefault(unit["key"], {"key": unit["key"], "id": unit["id"], "name": unit["name"],
                                                        "team": unit["team"], "buffs": {}})
            active = reader.buffs_of(unit["buff"])
            for buff_id, info in active.items():
                stat = row["buffs"].get(str(buff_id))
                if stat is None:
                    ca = info["ca"]
                    kind, attrs = names.buff_kind(buff_id, ca["baseEffect"])
                    stat = row["buffs"][str(buff_id)] = {
                        "id": buff_id, "label": names.buff_label(ca["idCN"], buff_id), "kind": kind,
                        "mod": names.kr.get(ca["mod"], ca["mod"]), "attrs": attrs, "stacks": 0, "left": None, "instances": 0,
                        "maxStacks": 0, "activeFrames": 0, "stackFrames": 0, "applied": 0, "firstFrame": frame}
                before, after = stat["stacks"], info["stacks"]
                stat["stacks"], stat["left"], stat["instances"] = after, info["left"], info["instances"]
                stat["maxStacks"] = max(stat["maxStacks"], after)
                stat["activeFrames"] += dt
                stat["stackFrames"] += after * dt
                if before == 0:
                    stat["applied"] += 1
                if before != after:
                    cur["buffEvents"].append([frame, unit["key"], buff_id, before, after, info["left"]])
            self._close_buffs(row, active, frame)
        for key, row in cur["units"].items():
            if key not in seen:  # 목록에서 사라진 유닛의 버프도 끝난 것으로 본다.
                self._close_buffs(row, {}, frame)
        self.buff_samples += 1

    def _close_buffs(self, row, active, frame):
        for stat in row["buffs"].values():
            if stat["stacks"] and stat["id"] not in active:
                self.current["buffEvents"].append([frame, row["key"], stat["id"], stat["stacks"], 0, None])
                stat["stacks"], stat["left"], stat["instances"] = 0, None, 0

    def finish(self, game_duration=None, reason="ended"):
        self._close_spec()
        with self.lock:
            cur = self.current
            if cur is None:
                return
            self.settle(None)
            try:
                self._read_conditions(self.result)
            except TRANSIENT:
                self.poll_errors += 1
            cur["live"] = False
            cur["ended"] = time.time()
            cur["endReason"] = reason
            cur["game_duration"] = game_duration
            cur["metrics"] = self._metrics()
            cur["summary"] = summarize(cur)
            self.closed = (self.result, cur["frame"])
            self.current, self.result = None, 0
            self.status = self.waiting_status()
            total = sum(r["damage"] for r in cur["roles"].values())
            if total <= 0:
                self.closed = None  # 버린 전투는 닫은 것으로 치지 않는다 (전투가 이어지면 다시 기록).
                return
            stamp = datetime.fromtimestamp(cur["started"]).strftime("%Y%m%d-%H%M%S")
            path = self.log_dir / f"{stamp}.json"
            self.history.insert(0, battle_meta(cur, str(path)))
            del self.history[MAX_HISTORY:]
            self._cache_body(str(cur["id"]), cur)
        self._save(cur, path)

    def delete_battle(self, battle_id):
        """끝난 전투 하나를 목록과 기록 폴더에서 지운다. 진행 중인 전투는 지우지 않는다.

        파일이 이미 없어도 목록에서는 빼서, 폴더에서 직접 지운 기록도 이 버튼으로 정리할 수 있게 한다."""
        with self.lock:
            if self.current and str(self.current["id"]) == battle_id:
                return False
            meta = next((m for m in self.history if str(m["id"]) == battle_id), None)
            if meta is None:
                return False
            self.history.remove(meta)
            self.bodies.pop(battle_id, None)
            path = meta.get("path")
        if path:
            target = Path(path)
            # 기록 폴더 안의 .json 만 지운다.
            if target.suffix == ".json" and target.resolve().parent == self.log_dir.resolve():
                try:
                    target.unlink(missing_ok=True)
                except OSError as exc:
                    self.error = f"기록 파일을 지우지 못했습니다: {exc}"
        return True

    @staticmethod
    def _load_sent():
        try:
            return {str(name) for name in json.loads(SENT_FILE.read_text(encoding="utf-8"))}
        except (OSError, ValueError, TypeError):
            return set()

    def _battle_file(self, battle_id):
        """끝난 전투의 기록 파일 경로. 진행 중이거나 목록에 없으면 None."""
        with self.lock:
            if self.current and str(self.current["id"]) == battle_id:
                return None
            meta = next((m for m in self.history if str(m["id"]) == battle_id), None)
            return Path(meta["path"]) if meta and meta.get("path") else None

    def upload_battle(self, battle_id):
        """끝난 전투 하나의 기록 파일을 기록 받는 서버에 보낸다. 화면에 보일 결과를 돌려준다(자세한 이유는 detail)."""
        path = self._battle_file(battle_id)
        if not path or not path.is_file():
            return {"ok": False, "detail": "no saved file (live battle or missing)"}
        headers = {"Content-Type": "application/json", "Content-Encoding": "gzip", "User-Agent": f"resonance-dps-meter/{SCHEMA_VERSION}"}
        if UPLOAD["key"]:
            headers["X-Meter-Key"] = UPLOAD["key"]
        request = urllib.request.Request(UPLOAD["url"], data=gzip.compress(path.read_bytes(), 6), headers=headers, method="POST")
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                reply = json.loads(response.read())
        except urllib.error.HTTPError as exc:
            return {"ok": False, "detail": f"HTTP {exc.code} from {UPLOAD['url']}"}
        except (OSError, ValueError) as exc:
            return {"ok": False, "detail": f"{exc!r} ({UPLOAD['url']})"}
        if not (isinstance(reply, dict) and reply.get("ok")):
            return {"ok": False, "detail": f"server said {reply!r}"}
        with self.lock:
            self.sent.add(path.name)
            names = sorted(self.sent)
        try:
            APPDIR.mkdir(parents=True, exist_ok=True)
            SENT_FILE.write_text(json.dumps(names), encoding="utf-8")
        except OSError:
            pass  # 보낸 표시만 못 남긴 것이라 전송 결과는 그대로 돌려준다.
        return {"ok": True, "duplicate": bool(reply.get("duplicate"))}

    def _cache_body(self, key, battle):
        self.bodies[key] = battle
        self.bodies.move_to_end(key)
        while len(self.bodies) > BODY_CACHE:
            self.bodies.popitem(last=False)

    def _save(self, battle, path):
        """임시 파일에 쓴 뒤 교체해 잘린 파일이 남지 않게 한다."""
        try:
            self.log_dir.mkdir(parents=True, exist_ok=True)
            temporary = path.with_suffix(".tmp")
            temporary.write_text(json.dumps(battle, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
            os.replace(temporary, path)
        except OSError as exc:
            self.error = f"전투 기록을 저장하지 못했습니다: {exc}"

    def _step(self, action):
        """한 단계를 실행한다. 포인터가 잠깐 어긋나서 난 오류는 삼키고, 40회 연속이면 표시한다."""
        try:
            action()
        except TRANSIENT as exc:
            self.errors += 1
            self.poll_errors += 1
            if self.errors >= MAX_ERRORS:
                self.error = f"메모리를 해석하지 못하는 상태가 계속됩니다: {exc!r}"
        else:
            if self.errors >= MAX_ERRORS:
                self.error = ""
            self.errors = 0

    def run(self):
        while True:
            try:
                if self.halted:
                    # 읽기가 막힌 그 게임에는 다시 시도하지 않는다. 게임을 새로 켰을 때만(pid 가 다름) 다시 붙는다.
                    time.sleep(PID_CHECK_SECONDS)
                    pid = find_pid()
                    if pid and pid != self.blocked_pid:
                        self.halted, self.error, self.status = False, "", "게임을 찾는 중"
                elif not self.attach():
                    time.sleep(3)
                elif not self._process_alive():
                    continue
                elif self.current:
                    began = time.perf_counter()
                    self._step(self.tick)
                    time.sleep(FRAME_SLEEP)
                else:
                    self._step(self.idle)
                    if not self.current:
                        time.sleep(IDLE_SECONDS)
            except PermissionError as exc:
                # 읽기가 막히면 오류만 표시하고 멈춘다. 다시 시도하거나 우회하지 않는다.
                self.blocked_pid = self.reader.pid if self.reader else find_pid()
                self.detach("read_blocked")
                self.status, self.error, self.halted = "읽기 권한 없음", str(exc), True
            except RuntimeError as exc:
                self.status, self.error = "버전 불일치", str(exc)
                time.sleep(30)
            except OSError as exc:
                self.error = str(exc)
                self.detach("os_error")
                time.sleep(3)

    def _find_battle(self, battle_id):
        """요청한 전투의 본문: 진행 중 → 캐시 → 파일 순서. 파일은 잠금 밖에서 읽는다."""
        with self.lock:
            if self.current and (not battle_id or str(self.current["id"]) == battle_id):
                return self.current
            meta = next((m for m in self.history if str(m["id"]) == battle_id), None) if battle_id else None
            if meta is None:
                if self.current:
                    return self.current
                meta = self.history[0] if self.history else None
            if meta is None:
                return None
            key = str(meta["id"])
            if key in self.bodies:
                self.bodies.move_to_end(key)
                return self.bodies[key]
            path = meta.get("path")
        try:
            body = json.loads(Path(path).read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return None
        with self.lock:
            self._cache_body(key, body)
        return body

    def _owners(self, battle):
        """카드 주인 표. cardOrder 의 ownerId 우선, 없으면 게임 데이터 참조 거리로 정한다."""
        roles = [r["id"] for r in (battle.get("roles") or {}).values()]
        known = {str(r) for r in roles}
        table = battle.get("cardOwners") or {}
        owners = {}
        for key in battle.get("skills") or {}:
            owner = str(table.get(key))
            owners[key] = owner if owner in known else self.names.owner(key, roles)
        return owners

    @staticmethod
    def _series(battle):
        flow = battle.get("flow") or []
        step = max(len(flow) / SERIES_ROWS, 1)
        rows = [flow[int(i * step)] for i in range(min(len(flow), SERIES_ROWS))]
        if rows:
            rows[-1] = flow[-1]
        return [[r[0], r[1], len(r[3]), r[7], r[4], r[5]] for r in rows]

    @staticmethod
    def _buff_table(battle):
        frames = max(battle.get("frame", 0) - battle.get("startFrame", 0), 0)
        rank = {1: 0, 0: 1}
        table = []
        for unit in sorted((battle.get("units") or {}).values(), key=lambda u: rank.get(u.get("team"), 2)):
            rows = []
            for stat in unit["buffs"].values():
                active = stat["activeFrames"]
                rows.append({
                    "id": stat["id"], "label": stat["label"], "kind": stat["kind"], "mod": stat["mod"], "attrs": stat["attrs"],
                    "stacks": stat["stacks"], "left": stat["left"], "instances": stat["instances"], "maxStacks": stat["maxStacks"],
                    "avgStacks": round(stat["stackFrames"] / active, 1) if active else stat["maxStacks"],
                    "uptime": round(min(active / frames * 100, 100), 1) if frames else 0, "applied": stat["applied"],
                })
            table.append({"key": unit["key"], "name": unit["name"], "id": unit["id"], "team": unit["team"], "rows": rows})
        return table

    @staticmethod
    def _buff_events(battle, unit, table):
        """한 유닛의 마지막 중첩 변화 [t, 라벨, 이전, 이후, 남은 프레임]. unit 이 없으면 첫 유닛."""
        keys = [row["key"] for row in table]
        key = unit if unit in keys else (keys[0] if keys else None)
        if key is None:
            return []
        picked = []
        for event in reversed(battle.get("buffEvents") or []):
            if event[1] == key:
                picked.append(event)
                if len(picked) >= EVENTS_TO_VIEW:
                    break
        stats = battle["units"][key]["buffs"]
        return [[round(e[0] / 60, 2), stats[str(e[2])]["label"], e[3], e[4], e[5]] for e in reversed(picked)]

    def _battle_view(self, battle, unit):
        # spec 은 AI 모델용 세부 스펙이다. 화면에는 lineup 에 고른 값만 보낸다. setup 은 옛 기록에만 있다.
        hidden = ("flow", "buffEvents", "snapshots", "byRole", "units", "setup", "spec", "ops", "hits", "actions", "dotTicks")
        view = {key: value for key, value in battle.items() if key not in hidden}
        skills = {}
        for key, row in (battle.get("skills") or {}).items():
            item = {k: v for k, v in row.items() if k != "casts"}
            if "casts" in row:
                item["castCount"] = len(row["casts"])
                item["maxCast"] = max((c[1] for c in row["casts"]), default=0)
            skills[key] = item
        table = self._buff_table(battle)
        view.update(
            skills=skills, owners=self._owners(battle), log=(battle.get("log") or [])[-LOG_TO_VIEW:],
            # pos·ai 는 분석용이라 화면에는 보내지 않는다.
            cards=[{k: v for k, v in c.items() if k not in ("pos", "ai")} for c in (battle.get("cards") or [])[-CARDS_TO_VIEW:]],
            # 요약 항목이 늘기 전에 저장된 기록은 다시 계산해서 보여 준다.
            summary=summarize(battle) if battle.get("live") or "last10s" not in (battle.get("summary") or {}) else battle["summary"],
            ledger=battle.get("ledger"), now=battle.get("now"), series=self._series(battle), buffs=table,
            buffEvents=self._buff_events(battle, unit, table), lineup=lineup_view(battle.get("spec")),
        )
        return view

    def view(self, battle_id="", unit="", listing=False):
        """화면용 응답을 UTF-8 JSON 바이트로 돌려준다. 직렬화까지 잠금 안에서 끝낸다.

        listing 이면 메인 화면용 전투 목록만 담고, 전투를 지정하면 그 전투 본문만 담는다."""
        body = None if listing else self._find_battle(battle_id)
        with self.lock:
            battles = []
            if listing or not battle_id:
                metas = ([battle_meta(self.current, "")] if self.current else []) + self.history
                battles = [{k: v for k, v in m.items() if k != "path"} for m in metas]
            error, battle = self.error, None
            if body:
                try:
                    battle = self._battle_view(body, unit)
                except TRANSIENT as exc:  # 형식이 어긋난 기록 파일 하나 때문에 화면 전체가 끊기지 않게 한다.
                    error = error or f"전투 기록을 표시하지 못했습니다: {exc!r}"
            payload = {"status": self.status, "active": self.current is not None, "armed": self.armed, "halted": self.halted, "error": error, "now": time.time(),
                       "server": {"id": SERVER, "name": SERVERS[SERVER]["name"]} if self.reader else None,
                       "servers": {server: info["name"] for server, info in SERVERS.items()},
                       "battles": battles[:MAX_HISTORY], "battle": battle}
            if battle_id and not listing:
                path = next((m.get("path") for m in self.history if str(m["id"]) == battle_id), None)
                payload["sent"] = bool(path) and Path(path).name in self.sent
            return json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


METER = None
LAST_SEEN = [0.0]
PORT = [0]


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def _send(self, body, ctype="application/json; charset=utf-8", status=200, cache="no-store"):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", cache)
        self.end_headers()
        self.wfile.write(body)

    def _host_ok(self):
        return self.headers.get("Host") in (f"127.0.0.1:{PORT[0]}", f"localhost:{PORT[0]}")

    def do_GET(self):
        if not self._host_ok():
            return self._send(b"forbidden", "text/plain", 403)
        url = urlparse(self.path)
        if url.path == "/":
            return self._send((HERE / "meter.html").read_bytes(), "text/html; charset=utf-8")
        if url.path == "/api/view":
            LAST_SEEN[0] = time.time()
            query = parse_qs(url.query)
            listing = query.get("list", [""])[0] == "1"
            return self._send(METER.view(query.get("battle", [""])[0], query.get("unit", [""])[0], listing))
        portrait = PORTRAIT_PATH.fullmatch(url.path)
        equip = EQUIP_ICON_PATH.fullmatch(url.path)
        if ASSETS and (portrait or equip):
            data = ASSETS.get(f"unit/{portrait.group(1)}" if portrait else f"equip/{equip.group(1)}")
            return self._send(data, "image/webp", cache="max-age=86400") if data else self._send(b"not found", "text/plain", 404)
        image = (ICON_FILE if url.path == "/icon.png" else PORTRAIT_DIR / f"{portrait.group(1)}.webp" if portrait
                 else EQUIP_ICON_DIR / f"{equip.group(1)}.webp" if equip else None)
        if image and not image.is_file() and (portrait or equip):
            image = EXTRA_IMAGE_DIR / ("unit" if portrait else "equip") / image.name
        if image and image.is_file():
            return self._send(image.read_bytes(), "image/png" if image == ICON_FILE else "image/webp", cache="max-age=86400")
        return self._send(b"not found", "text/plain", 404)

    def do_POST(self):
        origin = self.headers.get("Origin")  # 다른 웹페이지가 미터를 조작하지 못하게 한다.
        if not self._host_ok() or (origin and origin.split("//")[-1] != self.headers.get("Host")):
            return self._send(b"forbidden", "text/plain", 403)
        url = urlparse(self.path)
        query = parse_qs(url.query)
        on = query.get("on", ["1"])[0] == "1"
        if url.path == "/api/upload":
            return self._send(json.dumps(METER.upload_battle(query.get("battle", [""])[0])).encode("utf-8"))
        if url.path == "/api/delete":
            return self._send(json.dumps({"ok": METER.delete_battle(query.get("battle", [""])[0])}).encode("utf-8"))
        if url.path == "/api/quit":
            # 읽기가 막혀 멈춘 미터만 물러난다: 관리자 권한으로 다시 켠 미터가 이 자리를 넘겨받는다 (main 의 take_over).
            if METER.halted:
                threading.Timer(0.2, os._exit, [0]).start()
            return self._send(json.dumps({"ok": METER.halted}).encode("utf-8"))
        if url.path == "/api/pin":
            return self._send(json.dumps({"ok": set_topmost(on)}).encode("utf-8"))
        if url.path == "/api/arm":
            return self._send(json.dumps({"armed": METER.set_armed(on)}).encode("utf-8"))
        return self._send(b"not found", "text/plain", 404)


def meter_windows():
    """떠 있는 미터 창들 (제목으로 찾는다. 최소화한 창도 들어간다)."""
    user32 = ctypes.windll.user32
    proc = ctypes.WINFUNCTYPE(W.BOOL, W.HWND, W.LPARAM)
    user32.EnumWindows.argtypes = [proc, W.LPARAM]
    user32.GetWindowTextW.argtypes = [W.HWND, W.LPWSTR, ctypes.c_int]
    user32.IsWindowVisible.argtypes = [W.HWND]
    found = []

    def visit(hwnd, _):
        title = ctypes.create_unicode_buffer(256)
        user32.GetWindowTextW(hwnd, title, 256)
        if user32.IsWindowVisible(hwnd) and title.value.startswith(WINDOW_TITLE):
            found.append(hwnd)
        return True

    user32.EnumWindows(proc(visit), 0)
    return found


def set_topmost(on):
    """미터 자신의 창만 항상 위로 고정하거나 해제한다."""
    user32 = ctypes.windll.user32
    user32.SetWindowPos.argtypes = [W.HWND, W.HWND] + [ctypes.c_int] * 4 + [W.UINT]
    found = meter_windows()
    for hwnd in found:
        user32.SetWindowPos(hwnd, W.HWND(-1 if on else -2), 0, 0, 0, 0, 0x0001 | 0x0002 | 0x0010)
    return bool(found)


def find_browser():
    roots = [os.environ.get("ProgramFiles(x86)"), os.environ.get("ProgramFiles"), os.environ.get("LOCALAPPDATA")]
    for root in filter(None, roots):
        for rel in (r"Microsoft\Edge\Application\msedge.exe", r"Google\Chrome\Application\chrome.exe"):
            exe = Path(root) / rel
            if exe.exists():
                return str(exe)
    return None


def open_window(url):
    exe = find_browser()
    if not exe:
        webbrowser.open(url)
        return False
    APPDIR.mkdir(parents=True, exist_ok=True)
    subprocess.Popen([exe, f"--app={url}", "--window-size=440,720", "--no-first-run", f"--user-data-dir={APPDIR / 'window'}"])
    threading.Thread(target=pin_window, daemon=True).start()
    return True


def pin_window():
    """창이 뜰 때까지 최대 10초 기다렸다가 항상 위로 고정한다."""
    for _ in range(40):
        if set_topmost(True):
            return
        time.sleep(0.25)


def running_meter(port):
    """이 포트에서 이미 도는 미터의 상태(/api/view 응답). 없으면 None. 시스템 프록시는 거치지 않는다."""
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(f"http://127.0.0.1:{port}/api/view?list=1", timeout=2) as response:
            state = json.loads(response.read())
            return state if isinstance(state, dict) and "battles" in state else None
    except (OSError, ValueError):
        return None


def take_over(port):
    """읽기가 막혀 멈춘 미터를 물러나게 하고 포트가 빌 때까지 기다린다. 넘겨받았으면 True."""
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(urllib.request.Request(f"http://127.0.0.1:{port}/api/quit", data=b"", method="POST"), timeout=2) as response:
            if not json.loads(response.read()).get("ok"):
                return False
    except (OSError, ValueError, AttributeError):
        return False
    for _ in range(20):
        time.sleep(0.25)
        if running_meter(port) is None:
            return True
    return False


def reopen_window(port):
    """이미 도는 미터의 창을 띄운다. 프로그램을 또 켜면 같은 전투가 두 번 저장되기 때문이다."""
    if not set_topmost(True) and open_window(f"http://127.0.0.1:{port}/"):
        pin_window()


def check():
    """지금 메모리의 전투 상태를 한 번 읽어 출력한다."""
    pid = find_pid()
    if not pid:
        raise SystemExit("게임이 실행 중이 아닙니다.")
    reader = Reader(pid)
    try:
        if not reader.resolve_classes():
            raise SystemExit("전투 코드가 아직 초기화되지 않았습니다. 전투를 한 번 시작한 뒤 다시 실행하세요.")
        print(f"클래스 검증 통과 (pid {pid})")
        ctx = reader.context()
        if ctx is None:
            print("전투 컨텍스트가 없습니다 (전투 중이 아닙니다).")
            return
        check_battle(reader, Names(), ctx)
    finally:
        reader.close()


def check_battle(reader, names, ctx):
    state_names = {**STATE_NAMES, 0: "첫 안내", 2: "시작 안내"}
    team = reader.property_values(ctx.team_property)
    system = reader.read(ctx.card_system, 0x110)
    print("\n[전투 컨텍스트]")
    print(f"  상태 {ctx.state} ({state_names.get(ctx.state, '?')}) · 프레임 {ctx.frame} ({ctx.frame / 60:.1f}초) · 불릿타임 {int(ctx.bullet)}")
    print(f"  비용 {ctx.cost / 10000:.2f} / {ctx.max_cost / 10000:.2f} · 회복 초당 {team.get('CostRestore', 0) * 60 / 10000:.3f}"
          f" · 시작 비용 {ctx.start_index / 10000:.2f} / {ctx.start_cost / 10000:.2f}")
    if system is None:
        print("  카드 시스템을 읽지 못했습니다.")
    else:
        hand = reader.hand_cards(u64_at(system, 0x80), reader.dict_int_long(ctx.adjust_cost))
        print(f"  손패 {reader.link_count(u64_at(system, 0x80))} / {team.get('HandCardMax', 0) // 10000}장: "
              + (", ".join(f"{names.skill(c['id'], c['name'])}({c['cost'] / 10000:g})" for c in hand) or "없음"))
        print(f"  덱 {reader.link_count(u64_at(system, 0x88))} · 버림 {reader.link_count(u64_at(system, 0xD8))}"
              f" · 자동 드로우 {i32_at(system, 0xA4)} / {team.get('AutoDrawInterval', 0) // 10000}프레임")
        leader = reader.leader_card(u64_at(system, 0x60))
        conditions = reader.leader_conditions(u64_at(system, 0x70))
        detail = ", ".join(f"{c['progress']}/{c['max']}{' 완료' if c['finished'] else ''}" for c in conditions) or "조건 없음"
        print(f"  리더: {names.skill(leader[0], leader[1]) if leader else '없음'} · 사용 가능 {system[0x78]} · {detail} · 평균 {leader_percent(conditions)}%")
    print("\n[유닛별 버프]")
    units = [("팀 전체", "팀", ctx.buff_system)]
    team_names = {1: "아군", 2: "적", 4: "기타"}
    for key, _pointer, raw in reader.units(ctx.unit_manager):
        ca = reader.unit_ca(u64_at(raw, 0x490))
        if ca:
            units.append((names.role(ca[0], ca[1]), team_names.get(key, str(key)), u64_at(raw, 0x440)))
    for name, team_name, system_ptr in units:
        buffs = reader.buffs_of(system_ptr)
        stacked = sorted((b for b in buffs.values() if b["stacks"] >= 2), key=lambda b: -b["stacks"])
        print(f"  [{team_name}] {name}: 버프 {len(buffs)}종 · 인스턴스 {sum(b['instances'] for b in buffs.values())}개 · 중첩 2 이상 {len(stacked)}종")
        for buff in stacked:
            left = "영구" if buff["left"] is None else f"{buff['left'] / 60:.1f}초"
            kind = names.buff_kind(buff["ca"]["id"], buff["ca"]["baseEffect"])[0]
            print(f"      ×{buff['stacks']} {names.buff_label(buff['ca']['idCN'], buff['ca']['id'])} (id {buff['ca']['id']}, {kind}, 남은 {left})")
    snap = reader.snapshot(ctx.result)
    if snap is None:
        print("\n전투 결과 객체를 읽지 못했습니다.")
        return
    order = reader.card_order(snap["cardOrder"], 0)
    role_sum = sum(r["damage"] for r in snap["roles"].values())
    print(f"\n[전투 결과] duration={snap['duration']} 캐릭터 합계={role_sum:,} 게임 총합(SN)={snap['gameTotalSN']:,}")
    print(f"  cardOrder {len(order)}개 · 표시 비용 합 {sum(c['shown'] for c in order)} · 무비용 표시 {sum(c['noCost'] for c in order)}개"
          f" · 사용 합 {sum(s['use'] for s in snap['skills'].values())} · 자동 합 {sum(s['passive'] for s in snap['skills'].values())}")
    ops = reader.operation_logs(ctx.replay_manager, 0)
    print(f"  조작 기록 {len(ops)}개 (카드 사용 {sum(op['cardIndex'] >= 0 for op in ops)}개)")
    for op in ops[-5:]:
        print(f"    프레임 {op['frame']} 팀{op['team']} 손패#{op['cardIndex']} x={op['x'] / 10000:.2f} z={op['z'] / 10000:.2f} uid={op['uid']!r}"
              + (" refresh" if op["refresh"] else "") + (f" teamCard={op['teamCard']}" if op["teamCard"] >= 0 else ""))
    for team, pointer, raw in reader.units(ctx.unit_manager):
        ca = reader.unit_ca(u64_at(raw, 0x490))
        if ca and team == ALLY_TEAM:
            print(f"    아군 {names.role(ca[0], ca[1])}: roleIndex {i32_at(raw, 0xAC)} x={i64_at(raw, 0x270) / 10000:.2f} z={i64_at(raw, 0x2A8) / 10000:.2f} 생존 {int(raw[0x330])}")
    if ctx.use_card_ai and ctx.ai_core:
        print(f"  카드 AI: {json.dumps(reader.ai_state(ctx.ai_core), ensure_ascii=False)}")
    print(f"  조건: {json.dumps(reader.result_conditions(ctx.result), ensure_ascii=False)}")
    replay, replay_error = reader.replay_info(ctx.replay_manager)
    if replay:
        init = json.dumps(replay["init"], ensure_ascii=False) if replay["init"] else replay["initError"]
        print(f"  관문 {replay['levelId']} · 씨앗 {replay['randomSeed']} · 관문 인자 {init}")
    else:
        print(f"  관문: 읽지 못함 ({replay_error})")
    print(f"  출전 순서: {[names.role(i, '') for i in reader.role_order(ctx.role_list)]}")
    for key, role in sorted(snap["roles"].items(), key=lambda kv: -kv[1]["damage"]):
        print(f"  [캐릭터] {key} {names.role(key, role['name'])}: {role['damage']:,}")
    owners = {c["id"]: c["owner"] for c in order if c["owner"] > 0}
    for key, skill in sorted(snap["skills"].items(), key=lambda kv: -kv[1]["dmg"])[:30]:
        owner = owners.get(key) or names.owner(key, snap["roles"])
        who = names.role(int(owner), "") if owner else "?"
        print(f"  [스킬] {key} {names.skill(key, skill['name'])} ({who}): {skill['dmg']:,} 사용 {skill['use']} 자동 {skill['passive']} 판정 {skill['findtimes']}")


class MeterServer(ThreadingHTTPServer):
    allow_reuse_address = False  # 켜 두면 Windows 에서 두 프로세스가 같은 포트를 함께 잡아 충돌을 알 수 없다.


def serve(port, window, reuse_window=False):
    try:
        server = MeterServer(("127.0.0.1", port), Handler)
    except OSError:
        server = MeterServer(("127.0.0.1", 0), Handler)
    PORT[0] = server.server_address[1]
    url = f"http://127.0.0.1:{PORT[0]}/"
    threading.Thread(target=METER.run, daemon=True).start()
    print(url, flush=True)
    # 멈춘 미터를 넘겨받았으면 그 미터가 띄운 창이 같은 주소로 남아 있다: 있으면 그대로 쓴다.
    if window and ((reuse_window and set_topmost(True)) or open_window(url)):
        def watchdog():
            """창을 닫으면 미터도 끈다 (2026-11-23 — 그 전엔 화면 요청이 3분 끊겨야 꺼졌다).

            창이 한 번 뜬 뒤 안 보이는 것이 이어지면 끈다. 기록 중인 전투가 있으면 끝나서 저장될 때까지 기다린다.
            창을 못 찾는 경우(제목이 다른 브라우저 탭)는 예전처럼 화면 요청이 3분 끊기면 끈다."""
            seen, gone, idle = False, 0, 0
            while True:
                time.sleep(WINDOW_CHECK_SECONDS)
                shown = bool(meter_windows())
                seen, gone = seen or shown, 0 if shown else gone + 1
                idle = idle + 1 if METER.current is None else 0
                closed = seen and gone >= 2
                silent = not seen and LAST_SEEN[0] and time.time() - LAST_SEEN[0] > 180
                if (closed or silent) and idle >= 2:
                    os._exit(0)
        threading.Thread(target=watchdog, daemon=True).start()
    server.serve_forever()


def main():
    global METER
    if sys.stdout:
        sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description="레조넌스 딜 미터")
    ap.add_argument("--port", type=int, default=8770)
    ap.add_argument("--no-window", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--log-dir", default=str(DEFAULT_LOG_DIR))
    ap.add_argument("--upload-url", help=f"서버 전송 주소 (기본: upload.json, 없으면 {DEFAULT_UPLOAD_URL})")
    ap.add_argument("--upload-key", help="서버 전송 때 X-Meter-Key 로 보낼 값 (기록 받는 서버의 --key)")
    args = ap.parse_args()
    try:
        UPLOAD.update({k: str(v) for k, v in json.loads(UPLOAD_CONFIG.read_text(encoding="utf-8")).items() if k in UPLOAD and v})
    except (OSError, ValueError, AttributeError):
        pass  # upload.json 이 없으면 기본값
    UPLOAD.update({k: v for k, v in (("url", args.upload_url), ("key", args.upload_key)) if v})
    if args.check:
        return check()
    running = None if args.no_window else running_meter(args.port)
    # 이미 도는 미터가 있으면 창만 다시 연다. 다만 읽기가 막혀 멈춘 미터라면(게임이 관리자 권한) 물러나게 하고 이 미터가 넘겨받는다.
    taken = bool(running and running.get("halted")) and take_over(args.port)
    if running and not taken:
        return reopen_window(args.port)
    METER = Meter(args.log_dir)
    serve(args.port, not args.no_window, reuse_window=taken)


if __name__ == "__main__":
    main()

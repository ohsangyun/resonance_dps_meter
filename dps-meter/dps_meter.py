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


DEFAULT_LOG_DIR = HERE.parent / "logs"
PORTRAIT_PATH = re.compile(r"/unit/([0-9]{1,12})\.webp")
EQUIP_ICON_PATH = re.compile(r"/equip/([0-9]{1,12})\.webp")
APPDIR = Path(os.environ.get("LOCALAPPDATA", Path.home())) / "ResonanceDpsMeter"
ASSET_PACK = HERE / "assets.pak"
ASSET_PACK_MAGIC = b"RSMP1"
ASSET_PACK_KEY = b"b6cc60911180c260f6c7f738f7e17879462b5aa7acfa1c39"
DEFAULT_UPLOAD_URL = "https://resonance.sayuu.is-a.dev/meter/upload"
SENT_FILE = APPDIR / "sent.json"
UPLOAD = {"url": DEFAULT_UPLOAD_URL, "key": ""}
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
SERVER = "kr"
GAME_PREFS_KEY = SERVERS[SERVER]["prefs"]
PREFS_NAME = re.compile(r"^.*?(CardAIData|CardAIOn|CardAIBan)(.*?)_h\d+$")
PROCESS_NAME = SERVERS[SERVER]["process"]
WINDOW_TITLE = "레조넌스 딜 미터"

RVA = SERVERS[SERVER]["rva"]


def pack_mask(data, salt, name):
    stream = hashlib.shake_256(ASSET_PACK_KEY + salt + name.encode("utf-8")).digest(len(data))
    return (int.from_bytes(data, "little") ^ int.from_bytes(stream, "little")).to_bytes(len(data), "little")


class AssetPack:

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


def read_data(name):
    packed = ASSETS.get(name) if ASSETS else None
    if not packed:
        raise OSError(f"assets.pak 에 {name} 이 없습니다")
    return zlib.decompress(packed).decode("utf-8")


def use_server(server):
    global SERVER, PROCESS_NAME, GAME_PREFS_KEY, RVA
    info = SERVERS[server]
    SERVER, PROCESS_NAME, GAME_PREFS_KEY, RVA = server, info["process"], info["prefs"], info["rva"]


STATE_NAMES = {4: "전투 중", 3: "전투 시작 대기", 5: "대열 정비", 6: "팀 카드 선택", 7: "이동 중",
               8: "승리 연출", 1: "전투 종료"}

SCHEMA_VERSION = 7
POLL_HZ = 60
FRAME_SLEEP = 0.002
RECHECK_SECONDS = 0.05
DOT_MOD = "周期效果"
OPERATION_SIZE = 0x50
IDLE_SECONDS = 0.25
PID_CHECK_SECONDS = 3
WINDOW_CHECK_SECONDS = 2
STALE_SECONDS = 600
PAUSE_SECONDS = 2
FLOW_FRAMES = 6
BUFF_FRAMES = 3
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

SPEC_VERSION = 3
REPLAY_INIT_FIELDS = (("isBattleTest", 0x98, "bool"), ("isArena", 0x99, "bool"), ("playerTeamNO", 0x9C, "i32"),
                      ("enemyLevelMin", 0xA0, "i32"), ("difficulty", 0xA4, "i32"), ("bgId", 0xA8, "i32"), ("enemyRn", 0xAC, "i32"),
                      ("weatherList", 0xB0, "int[]"), ("weatherCount", 0xB8, "i32"), ("weatherRateSN", 0xC0, "i64"),
                      ("enemyLevelOffset", 0xC8, "i32"), ("secondWeatherList", 0xD0, "int[]"),
                      ("weatherSecondRateSN", 0xD8, "i64"), ("secondWeatherCount", 0xE0, "i32"))
REPLAY_INIT_START, REPLAY_INIT_END = 0x98, 0xE4
MAX_INT_ARRAY = 256
EQUIP_SLOTS = 3
SPEC_RETRY_TICKS = 4
SPEC_MAX_TICKS = 1200
SPEC_STRING = 8192
MAX_TEAM_UNITS = 8
UNIT_READ = 0x4B8
HISTORY_OFFSET = 0x40
HISTORY_ENTRY = 0x28
HISTORY_LIMIT = 1024
HISTORY_FORMAT = struct.Struct("<qqiiiiii")
CREDIT_FRAMES = 12
CREDIT_NODES = 20000
MID_BATTLE_FRAMES = 600
STATE_FIGHTING = 4
ALLY_TEAM = 1
DISCARD_CARD = 10600474
DISCARD_OWNER = 10000001
FIRST_WEIGHT, STEP_WEIGHT, BAN_WEIGHT = 900000, 10000, -9999999
LEADER_COND, LEADER_WEIGHT, SP_COND, SP_WEIGHT = 96200022, 1200000, 96200021, 1100000
OTHER_COND, OTHER_WEIGHTS, KEEP_COND = 96200025, {999999: 0, -999999: 2}, 96200010
DISCARD_ACTION, DISCARD_ALWAYS_COND, DISCARD_DEFAULT_COND = 96300006, 96200034, 96200016
VALUE_CONDITIONS = {"CardAIConditionKeepCards", "CardAIConditionKeepCosts", "CardAIConditionTeamAttribute"}
DISCARD_LABELS = {1: "항상 (순위대로)", 2: "사용 안 함", 3: "쓸 수 있는 카드가 없을 때", 4: "순위가 높은 카드가 없을 때"}
PET_SLOTS = {(0, 4): 12300776, (0, 5): 12300777, (1, 5): 12300771}
PET_OPTIONS = {12300776: "공격력", 12300777: "방어력", 12300771: "체력"}
EQUIP_BREAK_TOKENS = {12304698: (0, "Atk"), 12304699: (1, "Def"), 12304700: (2, "HpMax")}
EMPTY_EQUIP_ID = 11800220
UNIT_INFO_SIZE = 0x178
UNIT_INFO_INTS = {"id": 0x0, "unitViewId": 0x4, "skill1Lv": 0x8, "skill2Lv": 0xC, "skill3Lv": 0x10, "lv": 0x14,
                  "awakeLv": 0x18, "resonanceLv": 0x1C, "trustLv": 0x20, "card1Num": 0x158, "card2Num": 0x15C,
                  "card3Num": 0x160, "roleIndex": 0x170}
UNIT_INFO_EQUIPS = (
    (0x24, 0x28, (0x2C, 0x38, 0x48, 0x58, 0x68, 0x78), (0x30, 0x40, 0x50, 0x60, 0x70, 0x80)),
    (0x88, 0x8C, (0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0), (0x98, 0xA8, 0xB8, 0xC8, 0xD8, 0xE8)),
    (0xF0, 0xF4, (0xF8, 0x108, 0x118, 0x128, 0x138, 0x148), (0x100, 0x110, 0x120, 0x130, 0x140, 0x150)),
)
UNIT_INFO_LIMITS = {"id": (10000000, 19999999), "lv": (1, 200), "awakeLv": (0, 20), "resonanceLv": (0, 20), "trustLv": (0, 100),
                    "skill1Lv": (0, 100), "skill2Lv": (0, 100), "skill3Lv": (0, 100)}

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
    return i64_at(data, at + 0x10) ^ i64_at(data, at)


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def property_unit_value(data, at):
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

    def __init__(self, pid):
        self.pid = pid
        self.handle = kernel32.OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, False, pid)
        if not self.handle:
            code = ctypes.get_last_error()
            if code == ERROR_ACCESS_DENIED and runs_elevated(pid) and not ctypes.windll.shell32.IsUserAnAdmin():
                raise PermissionError("게임이 관리자 권한으로 켜져 있어 읽을 수 없습니다.")
            raise PermissionError(f"게임 프로세스를 읽을 수 없습니다 (오류 {code})")
        self.base = self._module_base("gameassembly.dll")
        self.klass = {}
        self.clear_caches()

    def close(self):
        kernel32.CloseHandle(self.handle)

    def build(self):
        head = self.read(self.base, 0x40) if self.base else None
        pe = self.read(self.base + struct.unpack_from("<I", head, 0x3C)[0], 0x58) if head and head[:2] == b"MZ" else None
        if not pe or pe[:4] != b"PE\0\0":
            return None
        return {"timeDateStamp": struct.unpack_from("<I", pe, 8)[0], "sizeOfImage": struct.unpack_from("<I", pe, 0x50)[0]}

    def clear_caches(self):
        self.strings, self.buff_cas, self.card_cas, self.unit_cas, self.leader_maxes = {}, {}, {}, {}, {}
        self.ca_ids, self.product_ids = {}, {}
        self.class_names = {}

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
        if not self.base:
            self.base = self._module_base("gameassembly.dll")
        if not self.base:
            return False
        if self.read(self.base, 2) is None:
            self._stop_if_blocked()
            return False
        build, known = self.build(), SERVERS[SERVER]["build"]
        if build and build != known:
            raise RuntimeError(f"게임이 업데이트되었습니다 ({SERVERS[SERVER]['name']} 빌드 {build['timeDateStamp']}, 미터가 아는 빌드 {known['timeDateStamp']}). "
                               "Il2CppDumper 로 주소표를 다시 뽑아야 합니다.")
        out = {}
        for name, rva in RVA.items():
            klass = self.u64(self.base + rva)
            if not klass or klass & 1:
                return False
            name_ptr = self.u64(klass + 0x10)
            raw = self.read(name_ptr, len(name) + 1) if name_ptr else None
            if raw != name.encode() + b"\0":
                raise RuntimeError("게임이 업데이트되어 RVA 가 맞지 않습니다. Il2CppDumper 로 다시 뽑아야 합니다.")
            out[name] = klass
        self.klass = out
        return True

    def _stop_if_blocked(self):
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
        table, count = self._dict_table(ptr, 24)
        if table is None:
            return None
        klass = self.klass[klass_name]
        out = []
        for i in range(count):
            hash_code, _next, key, _pad, value = struct.unpack_from("<iiiiQ", table, i * 24)
            if hash_code < 0 or not value:
                continue
            data = self.read(value, size)
            if data is None or u64_at(data, 0) != klass:
                return None
            out.append((key, data))
        return out

    def dict_int_refs(self, ptr):
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
        head = self.read(ptr, 0x20)
        if head is None:
            return []
        items, size = struct.unpack_from("<Qi", head, 0x10)
        if not 0 <= size <= MAX_LIST or size <= start:
            return []
        data = self.read(items + 0x20 + start * 8, (size - start) * 8)
        return list(struct.unpack(f"<{size - start}Q", data)) if data else []

    def link_items(self, head):
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
        init, init_error = self.replay_init_args(manager)
        return {"levelId": i32_at(replay, 0x38), "randomSeed": i32_at(replay, 0x34), "playerLv": i32_at(replay, 0x40), "isReplay": bool(head[0x28]), "units": units,
                "extraCards": read_text(u64_at(replay, 0x58)), "enemyIds": read_text(u64_at(replay, 0x60)),
                "enemyLv": i32_at(replay, 0x68), "trainWeaponSkills": read_text(u64_at(replay, 0x70)),
                "init": init, "initError": init_error}, None

    def replay_init_args(self, manager):
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
        raw = self.read(ai_core, 0xC0) if ai_core else None
        if raw is None:
            return None
        card = u64_at(raw, 0xB0)
        ca = self.card_ca(self.u64(card + 0x108)) if card else None
        return {"actionValue": i32_at(raw, 0xB8), "cardId": ca[0] if ca else None,
                "blackboard": self.dict_str_int(u64_at(raw, 0x60))}

    def class_name(self, obj):
        klass = self.u64(obj) if obj else 0
        if not klass:
            return ""
        cached = self.class_names.get(klass)
        if cached is None:
            name_ptr = self.u64(klass + 0x10)
            raw = self.read(name_ptr, 64) if name_ptr else None
            cached = self.class_names[klass] = raw.split(b"\0")[0].decode("ascii", "replace") if raw else ""
        return cached

    def struct_items(self, ptr, size):
        head = self.read(ptr, 0x20) if ptr else None
        if head is None:
            return []
        items, count = struct.unpack_from("<Qi", head, 0x10)
        if not 0 <= count <= MAX_LIST or not items:
            return []
        data = self.read(items + 0x20, count * size) if count else b""
        return [data[i * size:(i + 1) * size] for i in range(count)] if data is not None else []

    def condition(self, ptr):
        if not ptr:
            return [0, None]
        raw = self.read(ptr, 0x64)
        if raw is None:
            return [0, None]
        ca = self.read(u64_at(raw, 0x38), 0x20)
        value = i32_at(raw, 0x60) if self.class_name(ptr) in VALUE_CONDITIONS else None
        return [i32_at(ca, 0x18) if ca else 0, value]

    def ai_settings(self, ai_core):
        raw = self.read(ai_core, 0xF0) if ai_core else None
        if raw is None:
            return None
        unit = lambda b: self.condition(u64_at(b, 0)) + [i32_at(b, 8)]
        return {
            "weights": self.dict_int_int(u64_at(raw, 0xD8)),
            "conds": {key: [unit(b) for b in self.struct_items(ptr, 16)] for key, ptr in self.dict_int_refs(u64_at(raw, 0xE0))},
            "replace": {key: [list(struct.unpack_from("<iiii", b, 0)) for b in self.struct_items(ptr, 16)]
                        for key, ptr in self.dict_int_refs(u64_at(raw, 0xE8))},
            "adjust": [unit(b) for b in self.struct_items(u64_at(raw, 0x98), 16)],
            "avail": [self.condition(ptr) for ptr in self.list_items(u64_at(raw, 0x88))],
            "actions": [[self.product_id(u64_at(b, 0x10))] + self.condition(u64_at(b, 8)) + [i32_at(b, 0)]
                        for b in self.struct_items(u64_at(raw, 0xC8), 24)],
        }

    def card_order(self, ptr, start):
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
        cached = self.card_cas.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0xD8)
            if raw is None:
                return None
            cached = self.card_cas[ptr] = (i32_at(raw, 0x18), self.string(u64_at(raw, 0x58)), i64_at(raw, 0xD0))
        return cached

    def property_card_ca(self, raw):
        card = u64_at(raw, 0x70) or u64_at(raw, 0x68)
        return self.card_ca(self.u64(card + 0x108)) if card else None

    def hand_cards(self, head, adjust):
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
        raw = self.read(property_ptr, 0xD8) if property_ptr else None
        ca = self.property_card_ca(raw) if raw else None
        return ca[:2] if ca else None

    def leader_conditions(self, list_ptr):
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
        cached = self.unit_cas.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x60)
            if raw is None:
                return None
            cached = self.unit_cas[ptr] = (i32_at(raw, 0x18), self.string(u64_at(raw, 0x58)))
        return cached

    def units(self, manager):
        raw = self.read(manager, 0x58)
        if raw is None:
            return []
        out = []
        for team, list_ptr in self.dict_int_refs(u64_at(raw, 0x50)):
            for unit in self.list_items(list_ptr):
                data = self.read(unit, UNIT_READ) if unit else None
                if data is not None:
                    out.append((team, unit, data))
                if len(out) >= MAX_UNITS:
                    return out
        return out

    def role_order(self, list_ptr):
        out = []
        for unit in self.list_items(list_ptr):
            ca = self.unit_ca(self.u64(unit + 0x490)) if unit else None
            if ca:
                out.append(ca[0])
        return out

    def buff_ca(self, ptr):
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
        if not ptr:
            return 0
        cached = self.ca_ids.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x20)
            cached = self.ca_ids[ptr] = i32_at(raw, 0x18) if raw else 0
        return cached

    def product_id(self, ptr):
        if not ptr:
            return 0
        cached = self.product_ids.get(ptr)
        if cached is None:
            raw = self.read(ptr, 0x40)
            cached = self.product_ids[ptr] = self.ca_id(u64_at(raw, 0x38)) if raw else 0
        return cached

    def action_of(self, action):
        raw = self.read(action, 0x178) if action else None
        if raw is None:
            return None
        return (self.ca_id(u64_at(raw, 0x170)), i32_at(raw, 0xBC), i32_at(raw, 0xC0), self.product_id(u64_at(raw, 0xE8)),
                bool(raw[0x10D]), bool(raw[0xE0]))

    def history_head(self, system):
        queue = self.u64(system + HISTORY_OFFSET) if system else 0
        head = self.read(queue, 0x28) if queue else None
        if head is None:
            return None
        capacity, array, ptr, length = i32_at(head, 0x10), u64_at(head, 0x18), i32_at(head, 0x20), i32_at(head, 0x24)
        if not 0 < capacity <= HISTORY_LIMIT or not 0 <= length <= capacity or not 0 <= ptr < capacity or not array:
            return None
        return queue, capacity, array, ptr, length

    def history_slots(self, array, first, count, capacity):
        out = []
        while count > 0:
            n = min(count, capacity - first)
            raw = self.read(array + 0x20 + first * HISTORY_ENTRY, n * HISTORY_ENTRY)
            if raw is None:
                return None
            for before, after, sid, frame, source, from_sid, buff_id, _time in HISTORY_FORMAT.iter_unpack(raw):
                out.append((sid, frame, buff_id, source, from_sid, before, after))
            count -= n
            first = 0
        return out

    def dots_of(self, system):
        head = self.read(system, 0x38)
        if head is None:
            return []
        out = []
        for link in (u64_at(head, 0x18), u64_at(head, 0x30)):
            for item in self.link_items(link):
                raw = self.read(item, 0x128)
                if raw is None or raw[0x30] or raw[0x58]:
                    continue
                ca = self.buff_ca(u64_at(raw, 0x100))
                if ca is None or ca["mod"] != DOT_MOD:
                    continue
                out.append((item, ca["id"], i32_at(raw, 0x40), i32_at(raw, 0x120), i32_at(raw, 0x124)))
        return out

    def buffs_of(self, system):
        head = self.read(system, 0x38)
        if head is None:
            return {}
        out = {}
        for link in (u64_at(head, 0x18), u64_at(head, 0x30)):
            for item in self.link_items(link):
                raw = self.read(item, 0x108)
                if raw is None or raw[0x30] or raw[0x58]:
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

    def __init__(self):
        self.roster, self.kr, self.records, self.zh_names = {}, {}, {}, []
        self.equip_items, self.equip_breaks, self.affixes, self.reso = {}, {}, {}, {}
        self.edges, self.reach = None, {}
        self.edge_lock = threading.Lock()
        self.labels, self.kinds = {}, {}
        self.glossary = sorted(GLOSSARY.items(), key=lambda kv: -len(kv[0]))
        try:
            text = read_data("data/game.js")
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
            roster = json.loads(read_data("data/kr_roster.json"))
            pairs = {r["zh"]: r["name"] for r in roster if r.get("zh") and r.get("name")}
            self.zh_names = sorted(pairs.items(), key=lambda kv: -len(kv[0]))
        except (OSError, ValueError, KeyError, TypeError) as exc:
            print("캐릭터 목록을 읽지 못했습니다:", exc, file=sys.stderr)
        try:
            extra = json.loads(read_data("data/extra_names.json"))
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
        for zh, name in self.zh_names:
            if len(zh) > 1 or piece == zh:
                piece = piece.replace(zh, name)
        piece = self.kr.get(piece, piece)
        for zh, ko in self.glossary:
            piece = piece.replace(zh, ko)
        return piece

    def buff_label(self, id_cn, buff_id=0):
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
        ranked = sorted((self._distances(r).get(str(skill), 99), str(r)) for r in roles)
        if not ranked or ranked[0][0] == 99 or (len(ranked) > 1 and ranked[0][0] == ranked[1][0]):
            return None
        return ranked[0][1]


class EffectBook:

    PREFER = {"카드": 0, "일반 공격": 1, "돌파": 2, "공명": 3, "패시브": 4, "소환물": 5}

    def __init__(self):
        self.units, self.kw, self.eq, self.par, self.mod, self.mods = {}, {}, {}, {}, {}, []
        try:
            data = json.loads(read_data("data/effects.json"))
            self.units, self.kw, self.eq = data.get("u") or {}, data.get("kw") or {}, data.get("eq") or {}
            self.par, self.mod, self.mods = data.get("par") or {}, data.get("mod") or {}, data.get("mods") or []
        except (OSError, ValueError, KeyError, TypeError) as exc:
            print("효과 이름표를 읽지 못했습니다:", exc, file=sys.stderr)

    def kind_of(self, node):
        index = self.mod.get(str(node))
        return self.mods[index] if index is not None and index < len(self.mods) else ""

    def ancestor_levels(self, node, wanted, depth=8):
        out, frontier, seen = [], [str(node)], {str(node)}
        for _ in range(depth):
            following, level = [], set()
            for n in frontier:
                for p in self.par.get(n, ()):
                    key = str(p)
                    if key in seen:
                        continue
                    seen.add(key)
                    if p in wanted:
                        level.add(p)
                    following.append(key)
            if level:
                out.append(level)
            frontier = following
            if not frontier:
                break
        return out


    def nodes(self, role):
        return (self.units.get(str(role)) or {}).get("n") or {}

    def damage_ancestors(self, role):
        n = self.nodes(role)
        frontier = [k for k in n if self.kind_of(k) == "伤害"]
        seen = set(frontier)
        while frontier:
            following = []
            for k in frontier:
                for p in self.par.get(k, ()):
                    key = str(p)
                    if key in n and key not in seen:
                        seen.add(key)
                        following.append(key)
            frontier = following
        return {k for k in seen if self.kind_of(k) not in ("Bullet", "FrameEvent", "UnitAction", "UnitState", "Card", "Skill", "Unit", "Controller", "Weather")}

    def candidates(self, role, buff_id, source, who, credit):
        u = self.units.get(str(role))
        if not u:
            return []
        n = u.get("n") or {}
        cands = list(n.get(str(buff_id)) or [])
        if not cands:
            return []
        src = n.get(str(source)) if source and source != role else None
        if src:
            cands = [c for c in cands if c in src] or cands
        if who:
            s = (u.get("s") or {}).get(str(who))
            if s is not None and s in cands:
                cands = [s]
        if len(cands) > 1 and credit:
            kind, card = credit
            feats = u.get("f") or []
            if kind == "own":
                c = (u.get("c") or {}).get(str(card))
                if c in cands:
                    cands = [c]
                elif c is not None:
                    cands = [x for x in cands if feats[x][0] == "소환물" and feats[x][4] == c] or cands
            elif kind == "other":
                cands = [c for c in cands if c in ((u.get("t") or {}).get(str(buff_id)) or ())] or cands
            elif kind == "none":
                cands = [c for c in cands if feats[c][0] != "카드"] or cands
        feats = u.get("f") or []
        return sorted(cands, key=lambda c: (self.PREFER.get(feats[c][0], 9), feats[c][1], c))

    def feature_name(self, role, index):
        f = ((self.units.get(str(role)) or {}).get("f") or [])[index]
        kind, level, name, _card, _parent, link = f
        if kind == "돌파":
            return f"{name} (돌파 {level})", kind
        if kind == "공명":
            return f"{name} (공명 {level})", kind
        if kind == "소환물":
            return f"{name} (소환물)", kind
        if kind == "카드" and link == "생성":
            return f"{name} (생성 카드)", kind
        if link and link != "생성":
            return f"{name or kind} ({link} 연계)", kind
        return name or kind, kind

    def label(self, role, role_name, buff_id, source, who, credit, team_roles=None, summon_card=0):
        kw = self.kw.get(str(buff_id))
        if kw:
            name, kind = kw
            suffix = {"dot": " (지속 피해)", "zone": " (장판)"}.get(kind, "")
            return (f"{name}{suffix}" if name else f"{role_name} 지속 피해"), "키워드", "exact"
        cands = self.candidates(role, buff_id, source, who, credit)
        if len(cands) == 1:
            name, kind = self.feature_name(role, cands[0])
            if kind == "소환물" and summon_card:
                card = (self.units.get(str(role)) or {}).get("c", {}).get(str(summon_card))
                if card is not None:
                    name = f"{name[:-len(' (소환물)')]} ({self.feature_name(role, card)[0]} 소환물)" if name.endswith(" (소환물)") else name
            return name, kind, "exact"
        if cands:
            names = list(dict.fromkeys(self.feature_name(role, c)[0] for c in cands))
            return " / ".join(names), self.feature_name(role, cands[0])[1], "multi"
        if str(buff_id) in self.eq:
            return f"{self.eq[str(buff_id)]} (장비)", "장비", "exact"
        for other, other_name in (team_roles or {}).items():
            if other != role:
                got = self.candidates(other, buff_id, source, None, None)
                if got:
                    name, kind = self.feature_name(other, got[0])
                    return f"{name} ({other_name} 연계)", kind, "data"
        return f"효과 {buff_id}", "기타", "data"


TRACE_WINDOW = 600
TRACE_NEAR = 180


def trace_multi(book, battle):
    names, hits = battle.get("effectList"), battle.get("dmgHits")
    if not names or not hits or not book.par:
        return 0
    rows_of = {}
    keys_of = {}
    for hit in hits:
        if hit[2]:
            keys_of.setdefault(hit[3], set()).add(hit[2])
            keys_of.setdefault(str(hit[2]), set()).add(hit[2])
    roles = {hit[2] for hit in hits if hit[2]}
    for f, sid, key, buff, src, _fsid in battle.get("allyHist") or []:
        for role in (roles if key == "team" else keys_of.get(key, ())):
            rows_of.setdefault(role, {}).setdefault(buff, []).append([f, sid, src, False])
    for table in rows_of.values():
        for rows in table.values():
            rows.sort(key=lambda r: r[1])
    levels_cache, index, fixed = {}, {(r[0], r[1]): i for i, r in enumerate(names)}, 0

    def levels(role, node):
        key = (role, node)
        if key not in levels_cache:
            levels_cache[key] = book.ancestor_levels(node, rows_of.get(role) or {})
        return levels_cache[key]

    def pick(role, node, at, fifo):
        table = rows_of.get(role) or {}
        for level in levels(role, node):
            window = TRACE_WINDOW if fifo else TRACE_NEAR
            rows = [r + [b] for b in level for r in table[b] if at - window <= r[0] <= at and not (fifo and r[3])]
            if rows:
                chosen = min(rows, key=lambda r: r[1]) if fifo else max(rows, key=lambda r: r[1])
                if fifo:
                    for r in table[chosen[4]]:
                        if r[1] == chosen[1]:
                            r[3] = True
                return chosen
        return None
    spawned = {}
    for hit in sorted(hits, key=lambda h: h[1]):
        if hit[2] and book.kind_of(hit[5]) == "Bullet":
            got = pick(hit[2], hit[5], hit[0], True)
            if got:
                spawned[hit[1]] = got
    for hit in hits:
        if not (0 <= hit[10] < len(names)) or names[hit[10]][3] != "multi":
            continue
        role = hit[2]
        credit = ("own", hit[9]) if hit[9] > 0 else ("other", -hit[9]) if hit[9] < 0 else ("none", 0)
        node_feats = book.nodes(role)
        cands = book.candidates(role, hit[4], hit[5], hit[8], None if credit[0] == "none" else credit)
        entry = spawned.get(hit[1])
        if entry is None and book.kind_of(hit[5]) != "Bullet":
            entry = pick(role, hit[5], hit[0], False)
        for _ in range(8):
            if entry is None or len(cands) <= 1:
                break
            f, _sid, src, _used, buff = entry
            for node in (buff, src):
                if node and node != role:
                    cands = [c for c in cands if c in (node_feats.get(str(node)) or ())] or cands
            node = src if src and src != role and str(src) in book.mod else buff
            entry = pick(role, node, f, False) if len(cands) > 1 else None
        if len(cands) > 1 and credit[0] == "none":
            cands = [c for c in cands if c in book.candidates(role, hit[4], hit[5], hit[8], credit)] or cands
        if len(cands) == 1:
            name, kind = book.feature_name(role, cands[0])
            i = index.get((role, name))
            if i is None:
                i = index[(role, name)] = len(names)
                names.append([role, name, kind, "trace"])
            hit[10] = i
            fixed += 1
    return fixed


def read_card_prefs():
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
    packer = zlib.compressobj(6, zlib.DEFLATED, -15, 8, 0)
    text = json.dumps(data, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return base64.b64encode(packer.compress(text) + packer.flush()).decode("ascii")


def expected_weights(card_list):
    out = {}
    for index, card in enumerate(card_list):
        card_id = int(card["id"])
        if card_id == DISCARD_CARD and card.get("useType", 1) == 2:
            continue
        banned = card_id != DISCARD_CARD and card.get("useType", 1) == 2
        out[card_id] = BAN_WEIGHT if banned else FIRST_WEIGHT - STEP_WEIGHT * index
    return out


def pick_card_slot(slots, party, level_id=None, weights=None):
    party_set = set(party)
    rows = []
    for key, slot in slots.items():
        data = slot["data"]
        owners = {c.get("ownerId") for c in data["cardList"]} - {DISCARD_OWNER}
        roles = {r for r in data.get("roleList") or [] if isinstance(r, int) and r > 0}
        rows.append((key, slot, owners, roles))
    level_key = f"LevelRoleList_{level_id}"
    if weights:
        ranks = {v for v in weights.values() if v != BAN_WEIGHT}
        exact = [row for row in rows if row[2] <= party_set
                 and all(weights.get(k) == v for k, v in expected_weights(row[1]["data"]["cardList"]).items())
                 and {v for v in expected_weights(row[1]["data"]["cardList"]).values() if v != BAN_WEIGHT} == ranks]
        if exact:
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


def card_owner_skill(names, card_id, party):
    owner = names.owner(card_id, party)
    if owner is None:
        return DISCARD_OWNER, None, None
    for index, row in enumerate((names.records.get(owner) or {}).get("skillList") or [], 1):
        card = (names.records.get(str(row.get("skillId"))) or {}).get("cardID")
        links = [x.get("Id") for x in (names.records.get(str(card)) or {}).get("linkCardId") or [] if isinstance(x, dict)]
        if card == card_id or card_id in links:
            return int(owner), row.get("skillId"), index
    direct = [int(key) for key, record in names.records.items() if record.get("cardID") == card_id]
    return int(owner), direct[0] if direct else None, None


def memory_auto_set(names, settings, party, leader):
    weights = {int(k): v for k, v in (settings.get("weights") or {}).items()}
    if not weights:
        return None, ["weights"]
    conds = {int(k): v for k, v in (settings.get("conds") or {}).items()}
    replace = {int(k): v for k, v in (settings.get("replace") or {}).items()}
    unknown = ["discardType"]
    links = set()
    for card_id in weights:
        for link in (names.records.get(str(card_id)) or {}).get("linkCardId") or []:
            if isinstance(link, dict) and link.get("Id") != card_id and weights.get(link.get("Id")) == weights[card_id]:
                links.add(link.get("Id"))
    ranked, banned = {}, []
    for card_id, weight in weights.items():
        if card_id in links:
            continue
        if weight == BAN_WEIGHT:
            banned.append(card_id)
        elif weight <= FIRST_WEIGHT and (FIRST_WEIGHT - weight) % STEP_WEIGHT == 0 and (FIRST_WEIGHT - weight) // STEP_WEIGHT not in ranked:
            ranked[(FIRST_WEIGHT - weight) // STEP_WEIGHT] = card_id
        else:
            unknown.append(f"weight:{card_id}")
    order, banned = [], sorted(banned)
    discard_gap = DISCARD_CARD not in weights
    for index in range(max(ranked) + 1 if ranked else 0):
        if index in ranked:
            order.append(ranked[index])
        elif discard_gap:
            order.append(DISCARD_CARD)
            discard_gap = False
        elif banned:
            order.append(banned.pop(0))
        else:
            unknown.append(f"gap:{index}")
    order += banned
    cards = []
    for card_id in order:
        record = names.records.get(str(card_id)) or {}
        conditions, actions = record.get("ExCondList") or [], record.get("ExActList") or []
        use_type, use_param = (2 if weights.get(card_id, BAN_WEIGHT) == BAN_WEIGHT else 1), -1
        if card_id == DISCARD_CARD:
            owner, skill, skill_index = DISCARD_OWNER, record.get("skillId"), None
            for action, cond, _value, weight in settings.get("actions") or []:
                if action == DISCARD_ACTION and weight == weights.get(card_id) and cond != DISCARD_ALWAYS_COND:
                    hits = [i for i, c in enumerate(conditions) if c.get("condId") == cond or (cond == DISCARD_DEFAULT_COND and (c.get("condId") or 0) <= 0)]
                    use_type = 3 + hits[0] if hits else use_type
                    unknown += [] if hits else [f"discardCond:{cond}"]
        else:
            owner, skill, skill_index = card_owner_skill(names, card_id, party)
            for cond, value, _weight in conds.get(card_id) or []:
                hits = [i for i, c in enumerate(conditions) if c.get("condId") == cond]
                if not hits:
                    unknown.append(f"cond:{card_id}:{cond}")
                    continue
                use_type = 3 + hits[0]
                if value is not None:
                    use_param = round(value / 100) if conditions[hits[0]].get("typeEnum") == "percent" else value
            for _weight, _cond, action, param in replace.get(card_id) or []:
                hits = [i for i, c in enumerate(actions) if c.get("condId") == action]
                if not hits:
                    unknown.append(f"action:{card_id}:{action}")
                    continue
                use_type, use_param = 3 + len(conditions) + hits[0], param
        cards.append({"id": str(card_id), "ownerId": owner, "skillId": skill, "skillIndex": skill_index,
                      "useType": use_type, "useParam": use_param, "targetType": 0, "equipIdList": []})
    adjust = {(cond, weight) for cond, _value, weight in settings.get("adjust") or []}
    other = [OTHER_WEIGHTS[w] for c, w in adjust if c == OTHER_COND and w in OTHER_WEIGHTS]
    keep = [value for cond, value in settings.get("avail") or [] if cond == KEEP_COND]
    decoded = {"cardList": cards, "header": leader or (party[0] if party else None), "roleList": list(party),
               "isLeaderCardOn": (LEADER_COND, LEADER_WEIGHT) in adjust, "isSpCardOn": (SP_COND, SP_WEIGHT) in adjust,
               "otherCard": other[0] if other else 1, "keepCardNum": 0 if not keep or keep[0] in (None, -1) else keep[0],
               "discardType": None}
    if not keep:
        unknown.append("keepCardNum")
    return decoded, unknown


def compare_auto_sets(registry, memory):
    diffs = [key for key in ("isLeaderCardOn", "isSpCardOn", "otherCard", "keepCardNum") if registry.get(key) != memory.get(key)]
    pick = lambda d: [(int(c["id"]), c.get("useType", 1), c.get("useParam", -1) if c.get("useType", 1) > 2 else -1)
                      for c in d.get("cardList") or [] if c.get("useType", 1) != 2]
    if pick(registry) != pick(memory):
        diffs.append("cardList")
    ban = lambda d: sorted(int(c["id"]) for c in d.get("cardList") or [] if c.get("useType", 1) == 2)
    if ban(registry) != ban(memory):
        diffs.append("banned")
    return diffs


def auto_use_spec(names, state, party, leader, level_id, warnings):
    flags = state.flags or {}
    on = state.ai_last
    registry_on = flags["CardAIOn"] != 0 if isinstance(flags.get("CardAIOn"), int) else None
    out = {"on": on if on is not None else registry_on,
           "onSource": "memory:TeamData.isUseCardAI" if on is not None else "registry:CardAIOn" if registry_on is not None else None,
           "everOnDuringBattle": state.ai_ever if on is not None else None, "registryOn": registry_on,
           "registryBanFlag": flags.get("CardAIBan"), "code": None, "decoded": None, "cards": [],
           "source": {"from": None, "slot": None, "matchedBy": None, "readAt": "전투 시작 (게임이 자동 사용 설정을 저장한 뒤의 값)",
                      "changedDuringBattle": state.slot_changed, "weightCheck": None}}
    settings = state.ai_settings or state.ai_pending
    memory, unknown = memory_auto_set(names, settings, party, leader) if settings else (None, ["ai_settings"])
    if memory is not None and not state.ai_settings:
        unknown.append("unconfirmed")
    out["memory"] = {"decoded": memory, "unknown": unknown, "matchesRegistry": None, "diffs": None, "raw": settings}

    def from_memory(why, quiet=False):
        if memory is None:
            warnings.append(f"이번 파티에 맞는 자동 사용 슬롯을 확정하지 못했고({why}) 전투 메모리의 카드 AI 설정도 읽지 못했습니다. 코드는 비워 둡니다.")
            return out
        export = {k: v for k, v in memory.items() if v is not None}
        out.update({"code": encode_code(export), "decoded": memory})
        out["source"].update({"from": "memory"})
        for rank, card in enumerate(memory["cardList"], 1):
            card_id = int(card["id"])
            out["cards"].append({"rank": rank, "id": card_id, "name": names.skill(card_id, ""), "ownerId": card["ownerId"],
                                 "ownerName": names.roster.get(card["ownerId"]) if card["ownerId"] != DISCARD_OWNER else None,
                                 "skillId": card["skillId"], "skillIndex": card["skillIndex"], "useType": card["useType"],
                                 "useTypeLabel": use_type_label(names, card_id, card["useType"]), "useParam": card["useParam"],
                                 "useParamMap": None, "targetType": 0, "equipIdList": [], "isDiscardEntry": card_id == DISCARD_CARD,
                                 "expectedWeight": (state.weights or {}).get(card_id)})
        if not quiet:
            warnings.append(f"레지스트리 슬롯을 확정하지 못해({why}) 전투 메모리의 카드 AI 설정으로 코드를 만들었습니다. 버리기 방식(discardType)과 사용 안 함 카드의 순위는 메모리에 없어 비우거나 뒤로 둡니다.")
        return out

    if state.slots is None:
        out["source"]["matchedBy"] = "registry-unreadable"
        warnings.append("레지스트리에서 자동 사용 설정을 읽지 못했습니다" + (f": {state.prefs_error}" if state.prefs_error else ""))
        return from_memory("registry-unreadable")
    same = sorted(((k, sl) for k, sl in state.slots.items() if memory is not None and not compare_auto_sets(sl["data"], memory)),
                  key=lambda row: (row[0] != f"LevelRoleList_{level_id}", set(row[1]["data"].get("roleList") or []) != set(party), row[0]))
    if same:
        key, slot, why = same[0][0], same[0][1], "memory" if len(same) == 1 else f"memory-tie:{len(same)}"
    else:
        key, slot, why = pick_card_slot(state.slots, party, level_id, state.weights)
    out["source"]["matchedBy"] = why
    if slot is None:
        return from_memory(why)
    state.slot_key = key
    data = slot["data"]
    export = json.loads(slot["text"])
    if set(export.get("roleList") or []) != set(party):
        export["roleList"] = list(party)
    if leader:
        if export.get("header") not in (None, leader):
            warnings.append(f"레지스트리의 header({export['header']})가 이번 전투의 리더({leader})와 달라 리더로 고쳐 코드를 만들었습니다.")
        export["header"] = leader
    elif not export.get("header"):
        export["header"] = party[0] if party else None
    cards = data["cardList"]
    weights = expected_weights(cards)
    out["code"] = encode_code(export)
    out["decoded"] = export
    if memory is not None:
        diffs = compare_auto_sets(export, memory)
        out["memory"].update({"matchesRegistry": not diffs, "diffs": diffs})
        if diffs:
            out.update({"code": None, "decoded": None})
            from_memory(why, quiet=True)
            out["source"]["slot"] = key
            warnings.append(f"레지스트리 슬롯 {key} 가 전투 메모리의 카드 AI 설정과 달라({', '.join(diffs)}) 메모리 쪽으로 코드를 만들었습니다. 게임이 클라우드 설정이나 다른 슬롯을 썼을 수 있습니다.")
            return out
    out["source"].update({"from": "registry", "slot": key})
    for rank, card in enumerate(cards, 1):
        card_id, owner = int(card["id"]), card.get("ownerId")
        out["cards"].append({
            "rank": rank, "id": card_id, "name": names.skill(card_id, ""), "ownerId": owner,
            "ownerName": names.roster.get(owner) if owner != DISCARD_OWNER else None, "skillId": card.get("skillId"),
            "skillIndex": card.get("skillIndex"), "useType": card.get("useType"),
            "useTypeLabel": use_type_label(names, card_id, card.get("useType")), "useParam": card.get("useParam"),
            "useParamMap": card.get("useParamMap"), "targetType": card.get("targetType"), "equipIdList": card.get("equipIdList"),
            "isDiscardEntry": card_id == DISCARD_CARD, "expectedWeight": weights.get(card_id)})
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
    out = {key: i32_at(data, at + offset) for key, offset in UNIT_INFO_INTS.items()}
    equips, pets = [], []
    for equip_slot, (id_at, lv_at, slot_ids, slot_values) in enumerate(UNIT_INFO_EQUIPS):
        equip_id = i32_at(data, at + id_at)
        options = []
        for slot, (slot_id, slot_value) in enumerate(zip(slot_ids, slot_values)):
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
    out = []
    for row in mem["options"]:
        value = round(row["valueSN"] / 10000, 4) if row["valueSN"] else None
        option = option_row(names, item, option_kind(row["slot"]), row["slot"], row["id"], value, "memory:Replay.UnitInfo")
        option["valueSN"] = row["valueSN"]
        out.append(option)
    return out


def break_level_candidates(names, item, level, bonus):
    steps = names.equip_breaks.get(str(item.get("q"))) or []
    base = max(math.floor(item.get(flat, 0) + item.get(growth, 0) * (level - 1) + 1e-9)
               for flat, growth in (("atk", "gAtk"), ("def", "gDef"), ("hp", "gHp")))
    up, out = 0, []
    for stage in range(len(steps) + 1):
        if stage:
            if level < (steps[stage - 1].get("needLv") or 0):
                break
            if steps[stage - 1].get("effect") == "MainAttrUp":
                up += steps[stage - 1].get("add") or 0
        if math.floor(base * (1 + up) + 1e-9) - base == round(bonus):
            out.append(stage)
    return out


def equip_spec(names, slot, mem, bonus):
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
    if unit is None:
        return None
    return [{"id": row["id"], "stat": PET_OPTIONS[row["id"]], "value": round(row["valueSN"] / 10000, 4), "valueSN": row["valueSN"]}
            for row in unit["pets"] if row["valueSN"]]


def member_spec(names, role_id, order, unit, leader, attrs, warnings):
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
        "autoUse": "registry:PlayerPrefs + memory:CardAICore 대조 (슬롯을 못 고르면 memory:CardAICore 로 되짚음)",
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
    return types.SimpleNamespace(
        slots=None, flags=None, prefs_error=None, slot_key=None, slot_changed=False,
        replay=None, replay_error=None, weights=None, ai_settings=None, ai_pending=None, attrs=None, attrs_complete=False, attrs_frame=None, team_attrs=None,
        ai_last=None, ai_ever=False, ticks=0, memory_done=False)


def lineup_view(spec):
    if not isinstance(spec, dict):
        return None
    auto = spec.get("autoUse") or {}
    source = auto.get("source") or {}
    team = []
    for member in spec.get("team") or []:
        equips = [{"id": e.get("id"), "name": e.get("name"), "lv": e.get("level")} if e and e.get("enabledInTeamPreset") is not False else None
                  for e in (member.get("equips") or [])[:EQUIP_SLOTS]]
        equips += [None] * (EQUIP_SLOTS - len(equips))
        team.append({"id": member.get("id"), "name": member.get("name"), "leader": bool(member.get("leader")),
                     "lv": member.get("level"), "equips": equips})
    return {"code": auto.get("code"), "on": auto.get("on"), "codeMissing": source.get("matchedBy") if not auto.get("code") else None, "team": team}


def cost_units(sn):
    return round(sn / 10000, 2)


def leader_percent(conditions):
    if not conditions:
        return None
    ratios = [min(max(c["progress"] / c["max"], 0), 1) if c["max"] > 0 else 0 for c in conditions]
    return round(sum(ratios) / len(ratios) * 100)


def max_window(flow, seconds):
    best, base, left = 0, (flow[0][6] if flow else 0), 0
    for row in flow:
        while flow[left][0] <= row[0] - seconds:
            base = flow[left][6]
            left += 1
        best = max(best, row[6] - base)
    return best


def last_window(flow, seconds):
    if not flow:
        return 0
    start = flow[-1][0] - seconds
    return flow[-1][6] - next(row[6] for row in flow if row[0] >= start)


def estimate_used_cost(flow, cards):
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
    roles = battle.get("roles") or {}
    conditions = battle.get("conditions") or {}
    order = [str(r) for r in conditions.get("roleOrder") or [] if str(r) in roles]
    rest = sorted((key for key in roles if key not in order), key=lambda key: -roles[key].get("damage", 0))
    leader = str((battle.get("cardOwners") or {}).get(str(conditions.get("leaderCardId"))))
    return [{"id": roles[key].get("id", key), "name": roles[key].get("name") or key, "leader": key == leader}
            for key in order + rest]


def battle_meta(battle, path):
    return {"id": battle["id"], "server": battle.get("server"), "started": battle["started"], "live": bool(battle.get("live")),
            "total": sum(r.get("damage", 0) for r in battle["roles"].values()), "party": party_of(battle),
            "seconds": battle.get("game_duration") or (battle.get("frame") or 0) / 60, "path": path}


def read_meta(path):
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
        self.effects = EffectBook()
        self.lock = threading.RLock()
        self.reader = None
        self.status = "게임을 찾는 중"
        self.error = ""
        self.armed = True
        self.halted = False
        self.blocked_pid = None
        self.errors = 0
        self.pid_checked = 0.0
        self.current = None
        self.result = 0
        self.closed = None
        self.prev = None
        self.history = []
        self.bodies = collections.OrderedDict()
        self.sent = self._load_sent()
        self._reset_battle()
        self._load_history()
        threading.Thread(target=self.names._build_edges, daemon=True).start()

    def _reset_battle(self):
        self.cost_prev = None
        self.cost_before = 0
        self.pending_cost = 0
        self.unpaid = collections.deque()
        self.spends = collections.deque()
        self.card_count = 0
        self.op_count = 0
        self.pending_ops = collections.deque()
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
        self.seen_frame = None
        self.full_at = 0.0
        self.frame_samples = self.frames_skipped = 0
        self.action_state = {}
        self.dot_state = {}
        self.spec_state = None
        self.hist_state = {}
        self.history_ok = False
        self.hist_overflow = 0
        self.tick_card_deltas = []
        self.credit_hits = collections.deque()
        self.credit_cards = collections.deque()
        self.credit_stats = {"matched": 0, "cardsUnmatched": 0, "ambiguous": 0}
        self.effect_index = {}
        self.known_nodes = (None, set())
        self.log_bucket = {}

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
        with self.lock:
            self.armed = bool(on)
            if not self.current and self.reader and self.reader.klass:
                self.status = self.waiting_status()
            return self.armed

    def begin(self, ctx, snap):
        reader = self.reader
        reader.clear_caches()
        snap = reader.snapshot(ctx.result) or snap
        self._reset_battle()
        now = time.time()
        battle = {
            "schemaVersion": SCHEMA_VERSION, "id": int(now * 1000), "server": SERVER, "build": reader.build(),
            "started": now, "ended": None, "live": True,
            "endReason": None, "game_duration": None, "pollHz": POLL_HZ,
            "timeBase": "frame/60",
            "attrsUnit": "SN=값x10000", "startFrame": ctx.frame, "frame": ctx.frame, "state": ctx.state,
            "firstHitFrame": None, "first_hit": None, "last_hit": None, "gameTotalSN": 0,
            "conditions": {"leaderCardId": None, "leaderCard": None, "roleOrder": []},
            "roles": {}, "skills": {}, "cardOwners": {}, "timeline": {}, "byRole": {}, "log": [], "cards": [], "costGains": [],
            "ledger": {"openingSN": 0, "naturalSN": 0, "startSN": 0, "gainedSN": 0, "spentSN": 0, "otherSpentSN": 0,
                       "overflowSN": 0, "capFrames": 0, "frames": 0, "pendingSN": 0, "currentSN": 0},
            "flow": [], "leaderProgress": [], "units": {}, "buffEvents": [], "snapshots": [], "ops": [], "now": None,
            "hits": [], "actions": [], "dotTicks": [],
            "dmgHits": [], "allyHist": [], "effectList": [], "hitCheck": {},
            "summary": None, "metrics": {},
            "spec": None,
        }
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
        try:
            texts, state.flags = read_card_prefs()
            state.slots = parse_card_slots(texts)
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
            state.prefs_error = type(exc).__name__

    def _refresh_spec(self, battle, state):
        with self.lock:
            try:
                battle["spec"] = compose_spec(self.names, state, battle)
            except Exception as exc:
                print("세부 스펙을 만들지 못했습니다:", type(exc).__name__, file=sys.stderr)
                battle["spec"] = {"specVersion": SPEC_VERSION, "autoUse": None, "team": [],
                                  "warnings": [f"세부 스펙을 만들지 못했습니다: {type(exc).__name__}"]}

    def _capture_spec(self, ctx):
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
            settings = reader.ai_settings(ctx.ai_core)
            if settings and settings.get("weights") and settings == state.ai_pending:
                state.ai_settings, state.weights = settings, settings["weights"]
            state.ai_pending = settings
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
            return
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
            if not ended:
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
        cur, reader, frame = self.current, self.reader, ctx.frame
        cur["frame"], cur["state"] = frame, ctx.state
        self.tick_units = self.tick_unit_states = None
        new_cards = reader.card_order(snap["cardOrder"], self.card_count)
        for item in new_cards:
            self._note_owner(cur, item)
        self.tick_card_deltas = []
        self.apply_damage(snap, frame)
        self.apply_history(ctx, frame, snap)
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
            self._read_conditions(ctx.result)
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
            delta = (skill["dmg"] - old["dmg"]) & 0xFFFFFFFF
            if 0 < delta < 1 << 31:
                row["dmgSum"] = row.get("dmgSum", 0) + delta
                row["updates"] += 1
                row["maxUpdate"] = max(row["maxUpdate"], delta)
                if not row["casts"]:
                    row["casts"].append([frame, 0])
                row["casts"][-1][1] += delta
                owner = self._owner_of(key, snap)
                self.tick_card_deltas.append([frame, int(key), delta, int(owner) if owner else 0])
                if not self.history_ok:
                    cur["log"].append([t, row["name"], delta])
                if owner:
                    owned[owner] = owned.get(owner, 0) + delta
        for key, delta in role_delta.items():
            role_key = str(key)
            attributed = owned.get(role_key, 0)
            if delta or attributed:
                bucket = cur["byRole"].setdefault(role_key, {}).setdefault(second, [0, 0])
                bucket[0] += delta
                bucket[1] += attributed
            if delta:
                cur["hits"].append([frame, key, delta, attributed])
        self.tick_use, self.tick_passive = tick_use, tick_passive
        self.prev = snap

    def apply_history(self, ctx, frame, snap):
        cur, reader = self.current, self.reader
        units = self._live_units(ctx)
        by_sid = {u["sid"]: u for u in units if u["key"] != "team"}
        by_ptr = {u["ptr"]: u for u in units if u["key"] != "team"}
        roles = {int(k) for k in cur["roles"] if str(k).isdigit()}
        if self.known_nodes[0] != roles:
            known = set()
            for role in roles:
                known.update(self.effects.damage_ancestors(role))
            self.known_nodes = (roles, known)
        known = self.known_nodes[1]
        hits = []
        for unit in units:
            head = reader.history_head(unit["buff"])
            if head is None:
                continue
            queue, capacity, array, ptr, length = head
            state = self.hist_state.get(unit["key"])
            ally = unit["key"] == "team" or unit["team"] == ALLY_TEAM
            if ally and state is not None and state[0] == queue and state[1] == ptr and state[2] == length:
                continue
            last_sid = state[3] if state is not None and state[0] == queue else 0
            entries = reader.history_slots(array, 0, length, capacity)
            if entries is None:
                continue
            new = sorted(e for e in entries if e[0] > last_sid)
            try:
                if ally:
                    rows = [[f, sid, unit["key"], buff_id, source, from_sid] for sid, f, buff_id, source, from_sid, _b, _a in new if str(buff_id) in known]
                    got = []
                else:
                    rows, got = [], self._hits_of(unit, new, by_sid, by_ptr, roles)
            except TRANSIENT:
                self.poll_errors += 1
                continue
            if last_sid and len(new) >= capacity:
                self.hist_overflow += 1
            self.hist_state[unit["key"]] = [queue, ptr, length, new[-1][0] if new else last_sid]
            self.history_ok = True
            cur["allyHist"].extend(rows)
            hits += got
        if hits or self.tick_card_deltas:
            self._attribute(hits, frame, snap)

    @staticmethod
    def _role_of(attacker, by_ptr, roles):
        unit, who, card = attacker, 0, 0
        for _ in range(4):
            if unit is None:
                break
            if unit["id"] in roles and unit["team"] == ALLY_TEAM:
                return unit["id"], who, card
            if not who:
                who, card = unit["id"], unit.get("summonCard", 0) if 10000000 < unit.get("summonCard", 0) < 20000000 else 0
            unit = by_ptr.get(unit.get("owner"))
        return 0, who, card

    def _hits_of(self, target, entries, by_sid, by_ptr, roles):
        rows, stack = [], []
        for sid, f, buff_id, source, from_sid, before, after in entries:
            if after > before:
                stack.clear()
                continue
            inner = 0
            while stack and stack[-1][2] == f and stack[-1][1] >= after and stack[-1][0] <= before:
                b0, a0, _f0 = stack.pop()
                inner += b0 - a0
            stack.append((before, after, f))
            own = before - after - inner
            if own <= 0:
                continue
            attacker = by_sid.get(from_sid)
            role, who, summon_card = self._role_of(attacker, by_ptr, roles)
            dmg = own // 10000 if own % 10000 == 0 else round(own / 10000)
            rows.append([f, sid, role, attacker["key"] if attacker else "", buff_id, source, dmg, target["key"], who, None, -1, summon_card])
        return rows

    def _attribute(self, hits, frame, snap):
        cur = self.current
        cur["dmgHits"].extend(hits)
        self.credit_hits.extend(hits)
        self.credit_cards.extend(self.tick_card_deltas)
        for hit in hits:
            if self._needs_credit(hit):
                continue
            self._label(hit, None)
        self._match_credits(frame, final=False)

    def _needs_credit(self, hit):
        role = hit[2]
        if not role or str(hit[4]) in self.effects.kw:
            return False
        return len(self.effects.candidates(role, hit[4], hit[5], hit[8], None)) > 1

    def _match_credits(self, frame, final):
        pending = [h for h in self.credit_hits if h[9] is None]
        for card in sorted(list(self.credit_cards), key=lambda c: -c[2]):
            picked = None
            for low in (card[0], card[0] - 2, card[0] - CREDIT_FRAMES):
                picked = self._subset([h for h in pending if low <= h[0] <= card[0]], card[2])
                if picked is not None:
                    break
            if picked is None:
                continue
            if picked is False:
                self.credit_stats["ambiguous"] += 1
                continue
            owner = card[3]
            for hit in picked:
                hit[9] = card[1] if owner and owner == hit[2] else -card[1]
                pending.remove(hit)
                if hit[10] < 0:
                    self._label(hit, ("own" if hit[9] > 0 else "other", card[1]))
            self.credit_cards.remove(card)
            self.credit_stats["matched"] += 1
        horizon = None if final else frame - CREDIT_FRAMES
        while self.credit_cards and (horizon is None or self.credit_cards[0][0] < horizon):
            self.credit_cards.popleft()
            self.credit_stats["cardsUnmatched"] += 1
        while self.credit_hits and (horizon is None or self.credit_hits[0][0] < horizon):
            hit = self.credit_hits.popleft()
            if hit[9] is None:
                hit[9] = 0
                if hit[10] < 0:
                    self._label(hit, ("none", 0))
            elif hit[10] < 0:
                self._label(hit, None)

    @staticmethod
    def _subset(pool, target):
        items = sorted((h for h in pool if 0 < h[6] <= target), key=lambda h: -h[6])
        found, nodes = [], [0]

        def sig(chosen):
            return tuple(sorted((h[2], h[4], h[5], h[6], h[8]) for h in chosen))

        def walk(start, left, chosen):
            if left == 0:
                s = sig(chosen)
                if not any(s == f[0] for f in found):
                    found.append((s, list(chosen)))
                return len(found) > 1
            nodes[0] += 1
            if nodes[0] > CREDIT_NODES:
                return True
            prev = None
            for i in range(start, len(items)):
                h = items[i]
                key = (h[2], h[4], h[5], h[6], h[8])
                if h[6] > left or key == prev:
                    continue
                prev = key
                chosen.append(h)
                if walk(i + 1, left - h[6], chosen):
                    return True
                chosen.pop()
            return False
        walk(0, target, [])
        if nodes[0] > CREDIT_NODES and len(found) <= 1:
            return None
        if not found:
            return None
        return False if len(found) > 1 else found[0][1]

    def _label(self, hit, credit):
        cur = self.current
        role, buff_id, source, dmg, who = hit[2], hit[4], hit[5], hit[6], hit[8]
        role_row = cur["roles"].get(str(role)) or {}
        team = {int(k): v.get("name", "") for k, v in cur["roles"].items() if str(k).isdigit()}
        summon_card = hit[11] if len(hit) > 11 else 0
        name, kind, how = self.effects.label(role, role_row.get("name", ""), buff_id, source, who, credit, team, summon_card) if role else ("때린 유닛 미확인", "기타", "data")
        key = (role, name)
        index = self.effect_index.get(key)
        if index is None:
            index = self.effect_index[key] = len(cur["effectList"])
            cur["effectList"].append([role, name, kind, how])
        hit[10] = index
        t_frame = hit[0]
        label = f"{role_row.get('name', '?')} · {name}"
        bucket = self.log_bucket.get((t_frame, label))
        if bucket is None:
            bucket = self.log_bucket[(t_frame, label)] = [round(t_frame / 60, 2), label, 0]
            cur["log"].append(bucket)
            if len(self.log_bucket) > 4096:
                self.log_bucket.clear()
        bucket[2] += dmg

    def effects_view(self, battle):
        hits, names = battle.get("dmgHits"), battle.get("effectList")
        if not hits or names is None:
            return None
        out = {}
        for hit in hits:
            index = hit[10] if len(hit) > 10 else -1
            role, name, kind, how = names[index] if 0 <= index < len(names) else (hit[2], "판별 중", "기타", "multi")
            row = out.setdefault(str(role), {}).setdefault(name, {"name": name, "kind": kind, "how": how, "value": 0, "hits": 0})
            row["value"] += hit[6]
            row["hits"] += 1
        return {role: sorted(rows.values(), key=lambda r: -r["value"]) for role, rows in out.items()}

    def _hit_check(self, battle):
        totals = {}
        unknown = 0
        for hit in battle.get("dmgHits") or []:
            if hit[2]:
                totals[str(hit[2])] = totals.get(str(hit[2]), 0) + hit[6]
            else:
                unknown += hit[6]
        roles = {key: [row.get("damage", 0), totals.get(key, 0)] for key, row in battle["roles"].items()}
        multi = sum(1 for hit in battle.get("dmgHits") or [] if 0 <= hit[10] < len(battle["effectList"]) and battle["effectList"][hit[10]][3] == "multi")
        return {"hits": len(battle.get("dmgHits") or []), "byRole": roles, "unknownRoleDamage": unknown, "overflow": self.hist_overflow,
                "multiHits": multi, "credit": dict(self.credit_stats), "historyRead": self.history_ok}

    def apply_actions(self, ctx, frame):
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
                if owner is None or interval <= 0 or last is None or last[1] != interval:
                    continue
                if count < last[0] and last[0] + (frame - last[2]) >= interval:
                    cur["dotTicks"].append([frame, buff_id, owner, pointer & 0xFFFFFF, 1])
        for pointer in [p for p in states if p not in seen]:
            del states[pointer]

    def apply_cost(self, ctx, team, frame):
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
        if self.pending_ops:
            for card in reversed(cur["cards"][-len(new_cards):]):
                if card["target"] is None and self.pending_ops:
                    card["target"] = self.pending_ops.popleft()

    def _take_operations(self, ctx, frame):
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
        while self.pending_ops and frame - self.pending_ops[0]["frame"] > SETTLE_FRAMES * 4:
            self.pending_ops.popleft()

    def _unit_positions(self, ctx):
        try:
            return {u["key"]: [u["team"], u["x"], u["z"], u["roleIndex"], int(u["alive"])]
                    for u in self._live_units(ctx) if u["key"] != "team"}
        except TRANSIENT:
            self.poll_errors += 1
            return None

    def settle(self, frame):
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
        known = self.unit_keys.get(pointer)
        if known and known[0] == unit_id:
            return known[1]
        count = self.unit_counts.get(unit_id, 0) + 1
        self.unit_counts[unit_id] = count
        key = str(unit_id) if count == 1 else f"{unit_id}#{count}"
        self.unit_keys[pointer] = (unit_id, key)
        return key

    def _live_units(self, ctx):
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
                              "alive": bool(raw[0x330]), "action": u64_at(raw, 0x260), "sid": i32_at(raw, 0x47C),
                              "ptr": pointer, "owner": u64_at(raw, 0x4A8), "summonCard": i32_at(raw, 0x4B0)})
        self.tick_units = units
        return units

    def _unit_states(self, ctx):
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
            if key not in seen:
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
            self._match_credits(cur["frame"], final=True)
            traced = trace_multi(self.effects, cur)
            cur["hitCheck"] = self._hit_check(cur)
            cur["hitCheck"]["traced"] = traced
            cur["effects"] = self.effects_view(cur)
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
                self.closed = None
                return
            stamp = datetime.fromtimestamp(cur["started"]).strftime("%Y%m%d-%H%M%S")
            path = self.log_dir / f"{stamp}.json"
            self.history.insert(0, battle_meta(cur, str(path)))
            del self.history[MAX_HISTORY:]
            self._cache_body(str(cur["id"]), cur)
        self._save(cur, path)

    def delete_battle(self, battle_id):
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
        with self.lock:
            if self.current and str(self.current["id"]) == battle_id:
                return None
            meta = next((m for m in self.history if str(m["id"]) == battle_id), None)
            return Path(meta["path"]) if meta and meta.get("path") else None

    def upload_battle(self, battle_id):
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
            pass
        return {"ok": True, "duplicate": bool(reply.get("duplicate"))}

    def _cache_body(self, key, battle):
        self.bodies[key] = battle
        self.bodies.move_to_end(key)
        while len(self.bodies) > BODY_CACHE:
            self.bodies.popitem(last=False)

    def _save(self, battle, path):
        try:
            self.log_dir.mkdir(parents=True, exist_ok=True)
            temporary = path.with_suffix(".tmp")
            temporary.write_text(json.dumps(battle, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
            os.replace(temporary, path)
        except OSError as exc:
            self.error = f"전투 기록을 저장하지 못했습니다: {exc}"

    def _step(self, action):
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
        hidden = ("flow", "buffEvents", "snapshots", "byRole", "units", "setup", "spec", "ops", "hits", "actions", "dotTicks",
                  "dmgHits", "allyHist", "effectList")
        view = {key: value for key, value in battle.items() if key not in hidden}
        skills = {}
        for key, row in (battle.get("skills") or {}).items():
            item = {k: v for k, v in row.items() if k != "casts"}
            if "casts" in row:
                item["castCount"] = len(row["casts"])
                item["maxCast"] = max((c[1] for c in row["casts"]), default=0)
                item.setdefault("dmgSum", sum(c[1] for c in row["casts"]))
            skills[key] = item
        if battle.get("dmgHits"):
            view["effects"] = battle.get("effects") if not battle.get("live") and battle.get("effects") else self.effects_view(battle)
            view["hitCheck"] = battle.get("hitCheck") if not battle.get("live") else None
        table = self._buff_table(battle)
        view.update(
            skills=skills, owners=self._owners(battle), log=(battle.get("log") or [])[-LOG_TO_VIEW:],
            cards=[{k: v for k, v in c.items() if k not in ("pos", "ai")} for c in (battle.get("cards") or [])[-CARDS_TO_VIEW:]],
            summary=summarize(battle) if battle.get("live") or "last10s" not in (battle.get("summary") or {}) else battle["summary"],
            ledger=battle.get("ledger"), now=battle.get("now"), series=self._series(battle), buffs=table,
            buffEvents=self._buff_events(battle, unit, table), lineup=lineup_view(battle.get("spec")),
        )
        return view

    def view(self, battle_id="", unit="", listing=False):
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
                except TRANSIENT as exc:
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
        name = "ui/icon.png" if url.path == "/icon.png" else f"unit/{portrait.group(1)}" if portrait else f"equip/{equip.group(1)}" if equip else None
        data = ASSETS.get(name) if ASSETS and name else None
        if data:
            return self._send(data, "image/png" if name == "ui/icon.png" else "image/webp", cache="max-age=86400")
        return self._send(b"not found", "text/plain", 404)

    def do_POST(self):
        origin = self.headers.get("Origin")
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
            if METER.halted:
                threading.Timer(0.2, os._exit, [0]).start()
            return self._send(json.dumps({"ok": METER.halted}).encode("utf-8"))
        if url.path == "/api/pin":
            return self._send(json.dumps({"ok": set_topmost(on)}).encode("utf-8"))
        if url.path == "/api/arm":
            return self._send(json.dumps({"armed": METER.set_armed(on)}).encode("utf-8"))
        return self._send(b"not found", "text/plain", 404)


def meter_windows():
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
    for _ in range(40):
        if set_topmost(True):
            return
        time.sleep(0.25)


def running_meter(port):
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(f"http://127.0.0.1:{port}/api/view?list=1", timeout=2) as response:
            state = json.loads(response.read())
            return state if isinstance(state, dict) and "battles" in state else None
    except (OSError, ValueError):
        return None


def take_over(port):
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
    if not set_topmost(True) and open_window(f"http://127.0.0.1:{port}/"):
        pin_window()


def check():
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
    allow_reuse_address = False


def serve(port, window, reuse_window=False):
    try:
        server = MeterServer(("127.0.0.1", port), Handler)
    except OSError:
        server = MeterServer(("127.0.0.1", 0), Handler)
    PORT[0] = server.server_address[1]
    url = f"http://127.0.0.1:{PORT[0]}/"
    threading.Thread(target=METER.run, daemon=True).start()
    print(url, flush=True)
    if window and ((reuse_window and set_topmost(True)) or open_window(url)):
        def watchdog():
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
    ap.add_argument("--upload-url", help=f"서버 전송 주소 (기본 {DEFAULT_UPLOAD_URL})")
    ap.add_argument("--upload-key", help="서버 전송 때 X-Meter-Key 로 보낼 값 (기록 받는 서버의 --key)")
    args = ap.parse_args()
    try:
        UPLOAD.update({k: str(v) for k, v in json.loads(read_data("data/upload.json")).items() if k in UPLOAD and v})
    except (OSError, ValueError, AttributeError, zlib.error):
        pass
    UPLOAD.update({k: v for k, v in (("url", args.upload_url), ("key", args.upload_key)) if v})
    if args.check:
        return check()
    running = None if args.no_window else running_meter(args.port)
    taken = bool(running and running.get("halted")) and take_over(args.port)
    if running and not taken:
        return reopen_window(args.port)
    METER = Meter(args.log_dir)
    serve(args.port, not args.no_window, reuse_window=taken)


if __name__ == "__main__":
    main()

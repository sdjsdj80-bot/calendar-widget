#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
캘린더 위젯 — 아이폰 캘린더(iCloud + Google)를 윈도우 바탕화면에 띄우는 위젯

  Google 캘린더    내 Google 계정에 설치한 작은 연결 코드(Apps Script 웹 앱)로 읽고 추가해요.
  iCloud 캘린더    CalDAV로 읽고 추가해요.
  다른 캘린더       iCal 주소로 읽기만 해요.
  대한민국 공휴일   Google 공휴일 캘린더로 빨간 날을 표시해요.
  어느 쪽에 추가하든 아이폰 캘린더에도 나타나요.

화면: 바탕화면 전체를 쓰는 여러 주 달력 + 오른쪽 시간표와 할 일,
      일정 시작 전 알림, 컴퓨터를 켰을 때 오늘 일정과 할 일 요약.

설정은 %APPDATA%\CalendarWidget\config.json 에 저장되고,
앱 암호와 Google 연결 비밀 키는 윈도우 계정으로 암호화(DPAPI)해서 저장해요.
"""
from __future__ import annotations

import base64
from collections import Counter
import ctypes
import hashlib
import html
import json
import os
import queue
import re
import secrets
import struct
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import uuid
import webbrowser
import xml.etree.ElementTree as ET
import zipfile
import zlib
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta, timezone
from datetime import time as dt_time
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import parse_qs, quote, urlencode, urljoin, urlparse

import tkinter as tk
from tkinter import font as tkfont
from tkinter import messagebox, ttk

import icalendar
import recurring_ical_events

try:  # 윈도우에 등록된 인증서 목록을 써요. 백신이 HTTPS를 검사해도 브라우저처럼 연결돼요.
    import truststore
    truststore.inject_into_ssl()
except Exception:
    truststore = None

import requests

try:  # 설치 파일을 만들 때 함께 들어가는 값 (버전, Google 로그인 정보, 업데이트 저장소)
    import build_info as _build
except ImportError:
    _build = None

APP_NAME = "CalendarWidget"
APP_TITLE = "캘린더 위젯"
VERSION = getattr(_build, "VERSION", "2.0.0")
GOOGLE_CLIENT_ID = os.environ.get("CW_GOOGLE_CLIENT_ID") or getattr(_build, "GOOGLE_CLIENT_ID", "")
GOOGLE_CLIENT_SECRET = os.environ.get("CW_GOOGLE_CLIENT_SECRET") or getattr(_build, "GOOGLE_CLIENT_SECRET", "")
BUILT_IN_GOOGLE_CLIENT = bool(GOOGLE_CLIENT_ID)


def use_google_client(client_id: str, client_secret: str) -> None:
    """설정에서 불러온 Google 로그인 정보를 써요 (설치 파일에 들어 있지 않을 때)"""
    global GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET
    GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET = client_id, client_secret


def read_google_client_file(path: str) -> tuple[str, str]:
    """Google Cloud에서 내려받은 client_secret_….json에서 (클라이언트 ID, 보안 비밀)을 읽어요."""
    try:
        with open(path, encoding="utf-8-sig") as f:
            data = json.load(f)
    except (OSError, ValueError) as exc:
        raise SyncError("파일을 읽지 못했어요. Google Cloud에서 내려받은 JSON 파일을 골라 주세요.") from exc
    info = data.get("installed") if isinstance(data, dict) else None
    if isinstance(info, dict) and str(info.get("client_id", "")).endswith(".apps.googleusercontent.com"):
        return str(info["client_id"]), str(info.get("client_secret", ""))
    if isinstance(data, dict) and "web" in data:
        raise SyncError("'웹 애플리케이션'용 파일이에요. Google Cloud에서 클라이언트를 '데스크톱 앱'으로 다시 만들어 주세요.")
    raise SyncError("Google Cloud에서 내려받은 client_secret JSON 파일이 아니에요.")
UPDATE_REPO = os.environ.get("CW_UPDATE_REPO") or getattr(_build, "UPDATE_REPO", "")  # 예: "myname/calendar-widget"
USER_AGENT = f"{APP_NAME}/{VERSION}"
IS_WINDOWS = sys.platform == "win32"

ICLOUD_CALDAV = "https://caldav.icloud.com/"
KOREAN_HOLIDAYS_ICS = (
    "https://calendar.google.com/calendar/ical/"
    "ko.south_korea%23holiday%40group.v.calendar.google.com/public/basic.ics"
)

# 내 Google 계정에 설치하는 연결 코드(Apps Script 웹 앱). __TOKEN__ 자리에 비밀 키가 들어가요.
GOOGLE_SCRIPT = r"""/**
 * 캘린더 위젯 - Google 캘린더 연결 코드
 * 이 코드는 내 Google 계정 안에서만 실행돼요.
 * TOKEN은 위젯이 만든 비밀 키예요. 다른 사람에게 보여 주지 마세요.
 */
const TOKEN = '__TOKEN__';
const VERSION = 1;

function doGet() {
  return json_({ ok: true, app: 'calendar-widget', version: VERSION });
}

function doPost(e) {
  let req = null;
  try {
    req = JSON.parse(e.postData.contents);
  } catch (err) {
    return json_({ ok: false, error: 'bad_request' });
  }
  if (!req || req.token !== TOKEN) {
    return json_({ ok: false, error: 'unauthorized' });
  }
  try {
    if (req.action === 'ping') return json_(ping_());
    if (req.action === 'list') return json_(list_(req));
    if (req.action === 'add') return json_(add_(req));
    return json_({ ok: false, error: 'unknown_action' });
  } catch (err) {
    return json_({ ok: false, error: String((err && err.message) || err) });
  }
}

function json_(obj) {
  return ContentService.createTextOutput(JSON.stringify(obj))
      .setMimeType(ContentService.MimeType.JSON);
}

function ping_() {
  return {
    ok: true,
    version: VERSION,
    primary: CalendarApp.getDefaultCalendar().getName(),
    calendars: CalendarApp.getAllCalendars().length
  };
}

function list_(req) {
  const start = new Date(req.start);
  const end = new Date(req.end);
  const tz = Session.getScriptTimeZone();
  const owned = {};
  CalendarApp.getAllOwnedCalendars().forEach(function (c) { owned[c.getId()] = true; });
  const calendars = [];
  const events = [];
  CalendarApp.getAllCalendars().forEach(function (cal) {
    if (cal.isHidden()) return;
    const id = cal.getId();
    calendars.push({
      id: id,
      name: cal.getName(),
      color: cal.getColor(),
      writable: owned[id] === true,
      primary: cal.isMyPrimaryCalendar(),
      holiday: id.indexOf('#holiday@') !== -1
    });
    cal.getEvents(start, end).forEach(function (ev) {
      const item = {
        cal: id,
        uid: ev.getId(),
        title: ev.getTitle(),
        location: ev.getLocation(),
        notes: ev.getDescription(),
        allDay: ev.isAllDayEvent()
      };
      if (item.allDay) {
        item.start = Utilities.formatDate(ev.getAllDayStartDate(), tz, 'yyyy-MM-dd');
        item.end = Utilities.formatDate(ev.getAllDayEndDate(), tz, 'yyyy-MM-dd');
      } else {
        item.start = ev.getStartTime().toISOString();
        item.end = ev.getEndTime().toISOString();
      }
      events.push(item);
    });
  });
  return { ok: true, version: VERSION, calendars: calendars, events: events };
}

function add_(req) {
  const cal = req.calendarId ? CalendarApp.getCalendarById(req.calendarId)
                             : CalendarApp.getDefaultCalendar();
  if (!cal) return { ok: false, error: 'calendar_not_found' };
  const options = {};
  if (req.location) options.location = req.location;
  if (req.description) options.description = req.description;
  const ev = req.allDay
      ? cal.createAllDayEvent(req.title, ymd_(req.start), ymd_(req.end), options)
      : cal.createEvent(req.title, new Date(req.start), new Date(req.end), options);
  return { ok: true, uid: ev.getId() };
}

function ymd_(text) {
  const p = String(text).split('-').map(Number);
  return new Date(p[0], p[1] - 1, p[2]);
}
"""

# 캘린더 색이 없을 때 쓰는 색
PALETTE = ["#3B7DDD", "#2E9E6B", "#E8833A", "#8E5CD9", "#D9A21B", "#1FA3B8", "#D9487A"]

WEEKDAY_FULL = ["월요일", "화요일", "수요일", "목요일", "금요일", "토요일", "일요일"]
WEEKDAY_SHORT = ["월", "화", "수", "목", "금", "토", "일"]
GRID_HEADER = ["일", "월", "화", "수", "목", "금", "토"]  # 한국 달력처럼 일요일부터

DEFAULTS = {
    "google_refresh": "",        # Google 로그인 정보 (암호화된 값)
    "google_client_id": "",      # 설치 파일에 Google 로그인 정보가 없을 때 설정에서 불러온 값
    "google_client_secret": "",  # (암호화된 값)
    "google_email": "",
    "google_can_write": True,
    "update_mode": "auto",       # auto(자동으로 설치) | notify(알려만 주기) | off
    "welcomed": False,
    "google_url": "",            # (예전 방식) Google 연결 코드 웹 앱 주소
    "google_token": "",          # 연결 코드의 비밀 키 (암호화된 값)
    "apple_id": "",
    "app_password": "",          # 암호화된 값
    "ics_urls": [],
    "show_holidays": True,
    "refresh_minutes": 5,
    "default_calendar": "",      # (예전 설정) 비어 있으면 Google 기본 캘린더
    # 일정 추가 창의 빠른 선택 버튼 두 개. key가 비어 있으면 알아서 골라요.
    "quick_slots": [{"label": "학사일정", "key": ""}, {"label": "개인", "key": ""}],
    "quick_last": 0,
    "layout": 2,                 # 화면 배치 버전 (2 = 바탕화면 전체를 쓰는 달력)
    "weeks": 5,                  # 보이는 주 수 (1~8)
    "split_months": True,        # 달이 바뀌는 곳에서 줄을 나누고 달 이름을 보여 줘요
    "start_last_week": True,
    "show_week_numbers": False,
    "show_lunar": True,
    "show_timeline": True,
    "todo_done": "strike",
    "todo_color": "purple",      # 할 일 추가 창에서 마지막에 고른 색 (처음은 보라)
    "font_style": "gyeonggi",    # 위젯 글꼴: gyeonggi(경기천년 제목 · 바탕) | system(맑은 고딕)
    "todo_sync": "",             # 날짜 있는 할 일을 넣을 Google 캘린더 (아이폰에서도 보이게)
    "todo_tasks": False,         # 할 일을 Google Tasks와 맞춰요 (하위 할 일 · 체크로 끝내기)
    "todo_tasks_list": "@default",
    "todo_rollover": True,       # 끝내지 못한 할 일은 달력에서 오늘로 넘겨 보여 줘요
    "todo_mirror": "",           # Tasks를 쓸 때 날짜 있는 할 일을 복사해 둘 캘린더 (아이폰 기본 캘린더에서 보이게)
    "last_calendar": "",         # 일정 추가 창에서 마지막에 고른 캘린더 ('__todo__'는 할 일)
    "cal_order": [],             # 위 막대 캘린더 단추 순서 (Alt를 누른 채 끌어서 바꿔요)
    "removed_cals": [],          # '목록에서 숨기기'를 한 캘린더 (단추도 일정도 안 보여요)       # 끝낸 할 일: strike(취소줄로 계속) | today(오늘까지만) | hide(바로 숨기기)
    "timeline_start": 7,
    "timeline_end": 23,
    "event_scale": 100,          # 일정 글자 크기 (80~150%)
    "opacity": 100,
    "theme": "paper",            # paper | night | light | dark | system
    "colors": {},                # 테마별로 바꾼 색
    "locked": False,
    "pinned": False,
    "geometry": None,            # [x, y, w, h]
    "side_width": 0,
    "side_layout": 0,            # 2: 시간표 | 할 일 두 열 + 아래 메모
    "afterschool": {             # 방과후 시간표: 엑셀의 표시 → 일정 이름 · 시간
        "rules": [
            {"code": "특", "title": "특기적성", "time": "16:50~17:40", "vacation": "", "color": "#33B679"},
            {"code": "전1", "title": "전공1", "time": "18:20~21:00", "vacation": "08:30~15:10", "color": "#039BE5"},
            {"code": "전2", "title": "전공2", "time": "18:20~21:00", "vacation": "08:30~15:10", "color": "#039BE5"},
            {"code": "전3", "title": "전공3", "time": "18:20~21:00", "vacation": "08:30~15:10", "color": "#039BE5"},
            {"code": "토1", "title": "토스1", "time": "18:20~21:00", "vacation": "08:30~15:10", "color": "#F4511E"},
        ],
        "vacation_months": [7, 1],
    },
    "school": {},                # 급식: 고른 학교 (이름, 교육청 코드, 학교 코드)
    "neis_key": "",              # 나이스 교육정보 개방 포털 인증키 (없어도 돼요)
    "timetable_url": "https://script.google.com/macros/s/AKfycbzef-18J1DM8QMZirmHAGGjLR3JmeS1aikLfXhPxu8j-U1UD1nDj2vlpXbirXSpenHC-g/exec",
    "hidden_cals": [],           # 위 막대에서 숨긴 캘린더
    "cal_colors": {},            # 위젯에서 바꾼 캘린더 색
    "notify_minutes": 10,        # 0(끄기) | 5 | 10 | 30 | 60
    "boot_summary": True,
    # 아래 두 값은 설정 화면에 없어요 (테스트나 다른 CalDAV 서버용)
    "caldav_url": ICLOUD_CALDAV,
    "holiday_url": KOREAN_HOLIDAYS_ICS,
}


# ───────────────────────── 파일 위치 · 로그 ─────────────────────────

def app_home() -> str:
    custom = os.environ.get("CALENDAR_WIDGET_HOME")
    if custom:
        base = custom
    elif IS_WINDOWS:
        base = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), APP_NAME)
    else:
        base = os.path.join(os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config"), APP_NAME)
    os.makedirs(base, exist_ok=True)
    return base


HOME = app_home()
CONFIG_PATH = os.path.join(HOME, "config.json")
LOG_PATH = os.path.join(HOME, "error.log")


def log_error(text: str) -> None:
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {text}\n")
    except OSError:
        pass


# ───────────────────────── 윈도우 기능 (ctypes) ─────────────────────────

if IS_WINDOWS:
    from ctypes import wintypes

    user32 = ctypes.WinDLL("user32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    user32.GetParent.argtypes = [wintypes.HWND]
    user32.GetParent.restype = wintypes.HWND
    user32.GetForegroundWindow.restype = wintypes.HWND
    user32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    user32.GetWindowThreadProcessId.restype = wintypes.DWORD
    user32.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int,
                                    ctypes.c_int, ctypes.c_int, wintypes.UINT]
    user32.SetWindowPos.restype = wintypes.BOOL
    user32.IsIconic.argtypes = [wintypes.HWND]
    user32.IsWindowVisible.argtypes = [wintypes.HWND]
    user32.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
    user32.GetSystemMetrics.argtypes = [ctypes.c_int]
    kernel32.CreateMutexW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
    kernel32.CreateMutexW.restype = wintypes.HANDLE

    class RECT(ctypes.Structure):
        _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                    ("right", ctypes.c_long), ("bottom", ctypes.c_long)]

    class MONITORINFO(ctypes.Structure):
        _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", RECT), ("rcWork", RECT),
                    ("dwFlags", wintypes.DWORD)]

    user32.MonitorFromWindow.argtypes = [wintypes.HWND, wintypes.DWORD]
    user32.MonitorFromWindow.restype = ctypes.c_void_p
    user32.GetMonitorInfoW.argtypes = [ctypes.c_void_p, ctypes.POINTER(MONITORINFO)]
    user32.GetMonitorInfoW.restype = wintypes.BOOL
    user32.SystemParametersInfoW.argtypes = [wintypes.UINT, wintypes.UINT, ctypes.c_void_p, wintypes.UINT]
    user32.SystemParametersInfoW.restype = wintypes.BOOL
    user32.GetWindow.argtypes = [wintypes.HWND, wintypes.UINT]
    user32.GetWindow.restype = wintypes.HWND
    user32.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(RECT)]
    user32.GetWindowRect.restype = wintypes.BOOL
    user32.SetForegroundWindow.argtypes = [wintypes.HWND]
    user32.SetForegroundWindow.restype = wintypes.BOOL
    _get_window_long = getattr(user32, "GetWindowLongPtrW", None) or user32.GetWindowLongW
    _set_window_long = getattr(user32, "SetWindowLongPtrW", None) or user32.SetWindowLongW
    _get_window_long.argtypes = [wintypes.HWND, ctypes.c_int]
    _get_window_long.restype = ctypes.c_ssize_t
    _set_window_long.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t]
    _set_window_long.restype = ctypes.c_ssize_t

    def window_class(hwnd) -> str:
        buf = ctypes.create_unicode_buffer(256)
        user32.GetClassNameW(hwnd, buf, 256)
        return buf.value

    def window_pid(hwnd) -> int:
        pid = wintypes.DWORD()
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        return pid.value

    class _Blob(ctypes.Structure):
        _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]

    def _dpapi(data: bytes, encrypt: bool) -> bytes:
        buf = ctypes.create_string_buffer(data, len(data))
        blob_in = _Blob(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
        blob_out = _Blob()
        crypt32 = ctypes.windll.crypt32
        fn = crypt32.CryptProtectData if encrypt else crypt32.CryptUnprotectData
        if not fn(ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)):
            raise ctypes.WinError()
        try:
            return ctypes.string_at(blob_out.pbData, blob_out.cbData)
        finally:
            ctypes.windll.kernel32.LocalFree(blob_out.pbData)


def protect(secret: str) -> str:
    """앱 암호를 저장용 문자열로 바꿔요. 윈도우에서는 DPAPI로 암호화해요."""
    if not secret:
        return ""
    raw = secret.encode("utf-8")
    if IS_WINDOWS:
        try:
            return "dpapi:" + base64.b64encode(_dpapi(raw, True)).decode("ascii")
        except Exception as exc:
            log_error(f"DPAPI 암호화 실패: {exc}")
    return "b64:" + base64.b64encode(raw).decode("ascii")


def unprotect(stored: str) -> str:
    if not stored:
        return ""
    kind, _, payload = stored.partition(":")
    try:
        data = base64.b64decode(payload)
        if kind == "dpapi" and IS_WINDOWS:
            return _dpapi(data, False).decode("utf-8")
        if kind == "b64":
            return data.decode("utf-8")
    except Exception as exc:
        log_error(f"저장된 앱 암호를 읽지 못함: {exc}")
    return ""


def enable_dpi_awareness() -> None:
    if not IS_WINDOWS:
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


_instance_mutex = None


def acquire_single_instance() -> bool:
    global _instance_mutex
    if not IS_WINDOWS:
        return True
    _instance_mutex = kernel32.CreateMutexW(None, False, "Local\\CalendarWidget_SingleInstance")
    return ctypes.get_last_error() != 183  # ERROR_ALREADY_EXISTS


def windows_dark_mode() -> bool:
    if not IS_WINDOWS:
        return False
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize") as key:
            value, _ = winreg.QueryValueEx(key, "AppsUseLightTheme")
            return value == 0
    except OSError:
        return False


RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"


def autostart_command() -> str:
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}"'
    pythonw = os.path.join(os.path.dirname(sys.executable), "pythonw.exe")
    if not os.path.exists(pythonw):
        pythonw = sys.executable
    return f'"{pythonw}" "{os.path.abspath(__file__)}"'


def fix_autostart_path() -> None:
    """자동 실행이 켜져 있는데 다른 프로그램(예: 파이썬으로 실행하던 위젯)을 가리키면 지금 프로그램으로 바꿔요."""
    if not IS_WINDOWS:
        return
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0,
                            winreg.KEY_QUERY_VALUE | winreg.KEY_SET_VALUE) as key:
            try:
                current, _ = winreg.QueryValueEx(key, APP_NAME)
            except FileNotFoundError:
                return  # 자동 실행을 꺼 두었으면 그대로 둬요
            wanted = autostart_command()
            if os.path.normcase(str(current).strip()) != os.path.normcase(wanted):
                winreg.SetValueEx(key, APP_NAME, 0, winreg.REG_SZ, wanted)
    except OSError as exc:
        log_error(f"자동 실행 경로 확인 실패: {exc}")


def get_autostart() -> bool:
    if not IS_WINDOWS:
        return False
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as key:
            winreg.QueryValueEx(key, APP_NAME)
            return True
    except OSError:
        return False


def set_autostart(enabled: bool) -> None:
    if not IS_WINDOWS:
        return
    import winreg
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as key:
        if enabled:
            winreg.SetValueEx(key, APP_NAME, 0, winreg.REG_SZ, autostart_command())
        else:
            try:
                winreg.DeleteValue(key, APP_NAME)
            except FileNotFoundError:
                pass


def virtual_screen(root: tk.Misc) -> tuple[int, int, int, int]:
    """모니터 여러 대를 합친 화면 범위 (왼쪽, 위, 너비, 높이)."""
    if IS_WINDOWS:
        try:
            m = user32.GetSystemMetrics
            return m(76), m(77), m(78), m(79)
        except Exception:
            pass
    return 0, 0, root.winfo_screenwidth(), root.winfo_screenheight()


class DesktopLayer:
    """윈도우에서 위젯을 바탕화면 그림처럼 모든 창 아래에 깔아 둬요.

    - 다른 프로그램 창은 언제나 위젯 위에 떠요. 위젯을 눌러도 앞으로 튀어나오지 않아요.
      (WS_EX_NOACTIVATE: 눌러도 활성 창이 되지 않으니 지금 쓰던 한글이나 탐색기에서 키보드도 빠져나가지 않아요.)
    - 위젯을 눌러서 날짜를 고르거나 일정 · 할 일을 추가하는 것은 그대로 돼요.
    - 바탕화면 보기(Win+D)를 누르면 위젯이 바탕화면 위에 보이고, 다른 창을 쓰기 시작하면 다시 아래로 내려가요.
    """

    DESKTOP = {"Progman", "WorkerW"}
    SHELL = {"Shell_TrayWnd", "Shell_SecondaryTrayWnd", "NotifyIconOverflowWindow",
             "TopLevelWindowForOverflowXamlIsland", "Windows.UI.Core.CoreWindow",
             "XamlExplorerHostIslandWindow", "MultitaskingViewFrame", "ForegroundStaging",
             "#32768", "tooltips_class32"}
    HWND_TOPMOST, HWND_NOTOPMOST, HWND_BOTTOM = -1, -2, 1
    FLAGS = 0x0001 | 0x0002 | 0x0010  # SWP_NOSIZE | SWP_NOMOVE | SWP_NOACTIVATE
    GWL_EXSTYLE, WS_EX_NOACTIVATE = -20, 0x08000000
    GW_HWNDNEXT, GW_HWNDPREV = 2, 3

    def __init__(self, app: "App"):
        self.app = app
        self.pid = os.getpid()
        self.state = "bottom"

    def hwnd(self) -> int:
        try:
            return int(self.app.wm_frame(), 16)
        except Exception:
            return user32.GetParent(self.app.winfo_id()) or self.app.winfo_id()

    def install(self) -> None:
        self.round_corners()
        self.to_bottom()
        self.tick()

    def tick(self) -> None:
        try:
            self._update()
        except Exception:
            pass
        self.app.after(300, self.tick)

    def _no_activate(self, hwnd: int) -> None:
        style = _get_window_long(hwnd, self.GWL_EXSTYLE)
        if not style & self.WS_EX_NOACTIVATE:
            _set_window_long(hwnd, self.GWL_EXSTYLE, style | self.WS_EX_NOACTIVATE)

    def to_bottom(self) -> None:
        hwnd = self.hwnd()
        self._no_activate(hwnd)
        user32.SetWindowPos(hwnd, self.HWND_NOTOPMOST, 0, 0, 0, 0, self.FLAGS)
        user32.SetWindowPos(hwnd, self.HWND_BOTTOM, 0, 0, 0, 0, self.FLAGS)
        self.state = "bottom"
        desk, between = self._desktop_above(hwnd)
        if desk and not between:
            self._place_above(hwnd, desk)  # 바탕화면 뒤로 숨어 버렸으면 바로 위로 올려요

    def to_top(self) -> None:
        user32.SetWindowPos(self.hwnd(), self.HWND_TOPMOST, 0, 0, 0, 0, self.FLAGS)
        self.state = "top"

    def _update(self) -> None:
        hwnd = self.hwnd()
        self._no_activate(hwnd)
        fg = user32.GetForegroundWindow()
        cls = window_class(fg) if fg else ""
        ours = bool(fg) and window_pid(fg) == self.pid
        if self.state == "top":
            # 바탕화면 보기 중: 다른 프로그램을 쓰기 시작하면 다시 아래로
            if fg and not ours and cls not in self.DESKTOP and cls not in self.SHELL:
                self.to_bottom()
            return
        if user32.IsIconic(hwnd) or not user32.IsWindowVisible(hwnd):
            user32.ShowWindow(hwnd, 4)  # SW_SHOWNOACTIVATE
        desk, between = self._desktop_above(hwnd)
        if desk and between:
            # 바탕화면이 다른 창들보다 위로 올라왔어요: 바탕화면 보기(Win+D)
            if cls in self.DESKTOP:
                self.to_top()
        elif desk:
            self._place_above(hwnd, desk)  # 바탕화면 뒤에 숨어 버렸으면 바로 위로
        elif fg and not ours and cls not in self.DESKTOP and cls not in self.SHELL and self._covers(hwnd, fg):
            self.to_bottom()  # 지금 쓰는 창을 덮고 있으면 아래로

    def _desktop_above(self, hwnd: int) -> tuple[int, bool]:
        """위젯 바로 위쪽에서 가장 가까운 바탕화면 창을 찾아요.

        돌려주는 값: (바탕화면 창, 그 사이에 다른 프로그램 창이 있는지)
        사이에 다른 창이 있으면 바탕화면 보기(Win+D)로 바탕화면이 올라온 것이고,
        없으면 위젯이 바탕화면 뒤로 잘못 들어간 거예요.
        """
        between = False
        h = user32.GetWindow(hwnd, self.GW_HWNDPREV)
        for _ in range(5000):
            if not h:
                return 0, False
            if user32.IsWindowVisible(h):
                if window_class(h) in self.DESKTOP:
                    rect = RECT()
                    if user32.GetWindowRect(h, ctypes.byref(rect)) and \
                            rect.right - rect.left >= 400 and rect.bottom - rect.top >= 300:
                        return h, between
                elif window_pid(h) != self.pid and window_class(h) not in self.SHELL \
                        and not _get_window_long(h, self.GWL_EXSTYLE) & 0x8:  # 작업 표시줄 · 항상 위 창은 빼고
                    between = True
            h = user32.GetWindow(h, self.GW_HWNDPREV)
        return 0, False

    def _covers(self, hwnd: int, fg: int) -> bool:
        """위젯이 지금 쓰는 창보다 위에 있는지 봐요."""
        h = user32.GetWindow(hwnd, self.GW_HWNDNEXT)
        for _ in range(5000):
            if not h:
                return False
            if h == fg:
                return True
            h = user32.GetWindow(h, self.GW_HWNDNEXT)
        return False

    def _place_above(self, hwnd: int, desk: int) -> None:
        """위젯을 바탕화면 창 바로 위(다른 창들보다는 아래)에 놓아요."""
        above = user32.GetWindow(desk, self.GW_HWNDPREV)
        if not above or above == hwnd or _get_window_long(above, self.GWL_EXSTYLE) & 0x8:  # WS_EX_TOPMOST
            target = self.HWND_NOTOPMOST  # 바탕화면 위에 보통 창이 없으면 보통 창 중 맨 위 = 바탕화면 바로 위
        else:
            target = above
        user32.SetWindowPos(hwnd, target, 0, 0, 0, 0, self.FLAGS)

    def round_corners(self) -> None:
        try:  # 윈도우 11에서만 적용돼요
            pref = ctypes.c_int(2)  # DWMWCP_ROUND
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                wintypes.HWND(self.hwnd()), 33, ctypes.byref(pref), ctypes.sizeof(pref))
        except Exception:
            pass


# ───────────────────────── 설정 ─────────────────────────

def load_config() -> dict:
    cfg = dict(DEFAULTS)
    data = {}
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            cfg.update(data)
        else:
            data = {}
    except FileNotFoundError:
        pass
    except Exception as exc:
        log_error(f"설정 파일을 읽지 못함: {exc}")
    if not isinstance(cfg.get("ics_urls"), list):
        cfg["ics_urls"] = []
    for key, lo, hi in (("refresh_minutes", 1, 60), ("opacity", 30, 100), ("weeks", 1, 8),
                        ("timeline_start", 0, 23), ("timeline_end", 1, 24), ("event_scale", 80, 150)):
        try:
            cfg[key] = min(hi, max(lo, int(cfg[key])))
        except (TypeError, ValueError):
            cfg[key] = DEFAULTS[key]
    cfg["event_scale"] = int(round(cfg["event_scale"] / 10) * 10)
    if cfg["timeline_end"] <= cfg["timeline_start"]:
        cfg["timeline_end"] = min(24, cfg["timeline_start"] + 1)
    if cfg.get("notify_minutes") not in (0, 5, 10, 30, 60):
        cfg["notify_minutes"] = 10
    slots = cfg.get("quick_slots")
    if not (isinstance(slots, list) and len(slots) == 2 and all(isinstance(x, dict) for x in slots)):
        slots = [dict(x) for x in DEFAULTS["quick_slots"]]
    cfg["quick_slots"] = [{"label": str(x.get("label") or DEFAULTS["quick_slots"][i]["label"])[:10],
                           "key": str(x.get("key") or "")} for i, x in enumerate(slots)]
    if cfg["quick_slots"][0]["label"] == "학교":  # 예전 이름을 새 이름으로
        cfg["quick_slots"][0]["label"] = "학사일정"
    if cfg.get("quick_last") not in (0, 1, 3):  # 3은 '할 일'
        cfg["quick_last"] = 0
    if cfg.get("side_layout") != 2:  # 두 열로 바뀐 패널은 더 넓어야 해서 폭을 새 기본값으로 한 번 돌려요
        cfg["side_width"], cfg["side_layout"] = 0, 2
    after = cfg.get("afterschool")
    if not (isinstance(after, dict) and isinstance(after.get("rules"), list)
            and all(isinstance(r, dict) and r.get("code") for r in after["rules"])):
        cfg["afterschool"] = json.loads(json.dumps(DEFAULTS["afterschool"]))
    if not isinstance(cfg["afterschool"].get("vacation_months"), list):
        cfg["afterschool"]["vacation_months"] = [7, 1]
    for rule in cfg["afterschool"]["rules"]:  # 색 칸이 없던 예전 규칙에는 처음 값의 색을 넣어요
        if "color" not in rule:
            code = str(rule.get("code") or "")
            rule["color"] = ("#33B679" if code.startswith("특") else "#F4511E" if code.startswith("토")
                             else "#039BE5" if code.startswith("전") else "")
    if not cfg.get("todo_purple_v1"):  # 할 일 기본 색이 초록에서 보라로 바뀌었어요
        if cfg.get("todo_color") == "green":
            cfg["todo_color"] = "purple"
        cfg["todo_purple_v1"] = True
    if cfg.get("font_style") not in ("gyeonggi", "system"):
        cfg["font_style"] = "gyeonggi"
    if cfg.get("todo_done") not in ("strike", "today", "hide"):
        cfg["todo_done"] = "strike"
    if cfg.get("update_mode") not in ("auto", "notify", "off"):
        cfg["update_mode"] = "auto"
    if cfg.get("theme") not in (*THEMES, "system"):
        cfg["theme"] = "paper"
    if not isinstance(cfg.get("colors"), dict):
        cfg["colors"] = {}
    if not str(cfg.get("default_calendar") or "").startswith(("google:", "icloud:")):
        cfg["default_calendar"] = ""  # 예전 버전 값은 버리고 Google 기본 캘린더로
    if data and data.get("layout") != 2:
        # 예전의 작은 위젯에서 넘어오면 바탕화면 전체를 쓰는 배치로 시작해요
        cfg.update({"layout": 2, "geometry": None, "side_width": 0, "theme": "paper", "pinned": False})
    return cfg


def save_config(cfg: dict) -> None:
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    os.replace(tmp, CONFIG_PATH)


# ───────────────────────── 날짜 · 시간 도우미 ─────────────────────────

def local_midnight(d: date) -> datetime:
    return datetime(d.year, d.month, d.day).astimezone()


def fmt_time(dt: datetime) -> str:
    h = dt.hour
    return f"{'오전' if h < 12 else '오후'} {h % 12 or 12}:{dt.minute:02d}"


def fmt_day(d: date) -> str:
    return f"{d.month}월 {d.day}일 ({WEEKDAY_SHORT[d.weekday()]})"


def relative_label(d: date, today: date) -> str:
    n = (d - today).days
    return {0: "오늘", 1: "내일", 2: "모레", -1: "어제"}.get(n, f"{n}일 후" if n > 0 else f"{-n}일 전")


def parse_date(text: str, today: date) -> date | None:
    s = text.strip().replace(" ", "")
    m = re.fullmatch(r"(\d{4})[-./년]?(\d{1,2})[-./월]?(\d{1,2})일?", s)
    if m:
        y, mo, d = map(int, m.groups())
    else:
        m = re.fullmatch(r"(\d{1,2})[-./월](\d{1,2})일?", s)
        if not m:
            return None
        y, (mo, d) = today.year, map(int, m.groups())
    try:
        return date(y, mo, d)
    except ValueError:
        return None


def parse_time(text: str) -> dt_time | None:
    """'15:05', '9:5', '905', '1505', '오후 3시 5분', '3시', '오전 9시 30분' → 시각"""
    s = (text or "").strip().replace(" ", "")
    pm = s.startswith("오후")
    am = s.startswith("오전")
    if pm or am:
        s = s[2:]
    m = (re.fullmatch(r"(\d{1,2})[:.시](\d{1,2})분?", s) or re.fullmatch(r"(\d{1,2})시?", s)
         or re.fullmatch(r"(\d{1,2})(\d{2})", s))
    if not m:
        return None
    h = int(m.group(1))
    mi = int(m.group(2)) if m.re.groups >= 2 and m.group(2) else 0
    if pm and h < 12:
        h += 12
    if am and h == 12:
        h = 0
    if not (0 <= h <= 23 and 0 <= mi <= 59):
        return None
    return dt_time(h, mi)


def hex_rgb(c: str) -> tuple[int, int, int]:
    c = c.lstrip("#")
    return int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)


# Google 캘린더의 일정 색 24가지 (2026년 6월부터 웹 · 앱의 기본 팔레트)
GOOGLE_EVENT_COLORS = [
    ("#AD1457", "라디치오"), ("#D81B60", "체리블라썸"), ("#E67C73", "플라밍고"), ("#D50000", "토마토"),
    ("#F4511E", "귤"), ("#EF6C00", "호박"), ("#F09300", "망고"), ("#F6BF26", "바나나"),
    ("#E4C441", "시트론"), ("#C0CA33", "아보카도"), ("#7CB342", "피스타치오"), ("#0B8043", "바질"),
    ("#33B679", "세이지"), ("#009688", "유칼립투스"), ("#039BE5", "공작"), ("#4285F4", "코발트"),
    ("#7986CB", "라벤더"), ("#3F51B5", "블루베리"), ("#B39DDB", "위스테리아"), ("#9E69AF", "자수정"),
    ("#8E24AA", "포도"), ("#795548", "코코아"), ("#616161", "그래파이트"), ("#A79B8E", "자작나무")]
# 예전부터 있던 일정 색 11가지 (colorId) — 지금 권한으로 Google에 그대로 저장돼요
CLASSIC_EVENT_COLORS = {"1": "#7986CB", "2": "#33B679", "3": "#8E24AA", "4": "#E67C73", "5": "#F6BF26",
                        "6": "#F4511E", "7": "#039BE5", "8": "#616161", "9": "#3F51B5", "10": "#0B8043",
                        "11": "#D50000"}
CLASSIC_ID_BY_HEX = {hex_: cid for cid, hex_ in CLASSIC_EVENT_COLORS.items()}


def _lab(color: str) -> tuple[float, float, float]:
    """sRGB 색을 사람 눈의 차이에 가까운 Lab 값으로 바꿔요."""
    def lin(v: float) -> float:
        v /= 255
        return v / 12.92 if v <= 0.04045 else ((v + 0.055) / 1.055) ** 2.4
    r, g, b = (lin(v) for v in hex_rgb(color))
    x = (0.4124 * r + 0.3576 * g + 0.1805 * b) / 0.95047
    y = 0.2126 * r + 0.7152 * g + 0.0722 * b
    z = (0.0193 * r + 0.1192 * g + 0.9505 * b) / 1.08883

    def f(t: float) -> float:
        return t ** (1 / 3) if t > 0.008856 else 7.787 * t + 16 / 116
    fx, fy, fz = f(x), f(y), f(z)
    return 116 * fy - 16, 500 * (fx - fy), 200 * (fy - fz)


def nearest_classic_color_id(color: str) -> str:
    """24색이나 직접 고른 색과 눈으로 보기에 가장 비슷한 예전 일정 색 번호"""
    target = _lab(color)
    return min(CLASSIC_EVENT_COLORS, key=lambda cid: sum((a - b) ** 2 for a, b in
                                                         zip(target, _lab(CLASSIC_EVENT_COLORS[cid]))))


def blend(c1: str, c2: str, t: float) -> str:
    a, b = hex_rgb(c1), hex_rgb(c2)
    return "#%02X%02X%02X" % tuple(round(x + (y - x) * t) for x, y in zip(a, b))


# ───────────────────────── 일정 모델 · 해석 ─────────────────────────

class SyncError(Exception):
    """사용자에게 그대로 보여 줄 수 있는 오류"""


class RateLimited(SyncError):
    """Google이 잠깐 쉬었다가 다시 보내 달라고 할 때 (많이 한꺼번에 넣을 때)"""


class NeedPermission(SyncError):
    """로그인할 때 받은 권한으로는 할 수 없는 일 (다시 로그인해서 새 권한에 동의해야 해요)"""


def network_error(where: str, exc: Exception) -> SyncError:
    """연결 실패를 원인별로 알기 쉬운 말로 바꾸고, 자세한 내용은 error.log에 남겨요."""
    log_error(f"{where} 연결 실패: {exc!r}")
    if isinstance(exc, requests.exceptions.SSLError):
        text = (f"{where}의 보안 인증서를 확인하지 못했어요. "
                "백신이나 보안 프로그램이 인터넷 연결을 검사하고 있으면 생길 수 있어요.")
    elif isinstance(exc, requests.exceptions.ProxyError):
        text = f"프록시 설정 때문에 {where}에 연결하지 못했어요."
    elif isinstance(exc, requests.exceptions.Timeout):
        text = f"{where} 응답이 너무 늦어요. 잠시 뒤에 다시 해 보세요."
    else:
        text = f"{where}에 연결하지 못했어요. 인터넷 연결을 확인해 주세요."
    return SyncError(f"{text} ({type(exc).__name__})")


@dataclass
class Event:
    title: str
    start: date | datetime   # 종일이면 date, 아니면 현지 시간대 datetime
    end: date | datetime     # 종일이면 끝나는 다음 날(포함 안 함)
    all_day: bool
    cal_name: str
    color: str
    location: str = ""
    notes: str = ""
    kind: str = "event"      # event | holiday | observance
    source: str = ""
    uid: str = ""
    cal_key: str = ""        # 어느 캘린더의 일정인지 (위 막대에서 보이기 · 색을 고를 때 써요)
    ref: dict = field(default_factory=dict)  # Google 일정을 고칠 때 쓰는 값 (캘린더 ID, 일정 ID, 참석자 …)

    def days(self):
        if self.all_day:
            d, last = self.start, self.end - timedelta(days=1)
        else:
            d = self.start.date()
            last = (self.end - timedelta(microseconds=1)).date() if self.end > self.start else d
        while d <= last:
            yield d
            d += timedelta(days=1)


@dataclass
class RemoteCalendar:
    name: str
    url: str                 # iCloud는 캘린더 주소, Google은 캘린더 ID
    color: str
    writable: bool = True
    source: str = "iCloud"
    primary: bool = False
    owner: bool = False      # 내가 주인인 캘린더 (지울 수 있어요)

    @property
    def key(self) -> str:
        return f"{self.source.lower()}:{self.url}"

    @property
    def label(self) -> str:
        return f"{self.name} ({self.source})"


@dataclass
class FetchResult:
    events: list
    problems: list
    calendars: list


def _component_to_event(comp, cal_name, color, source, holiday) -> Event | None:
    if str(comp.get("STATUS", "")).upper() == "CANCELLED":
        return None
    dtstart = comp.get("DTSTART")
    if dtstart is None:
        return None
    start = dtstart.dt
    dtend, duration = comp.get("DTEND"), comp.get("DURATION")
    end = dtend.dt if dtend is not None else (start + duration.dt if duration is not None else None)
    if isinstance(start, datetime):
        start = start.astimezone()                 # 시간대 없는 시간은 현지 시간으로 봐요
        if end is None:
            end = start
        elif isinstance(end, datetime):
            end = end.astimezone()
        else:
            end = local_midnight(end)
        end = max(end, start)
        all_day = False
    else:
        if isinstance(end, datetime):
            end = end.date()
        if end is None or end <= start:
            end = start + timedelta(days=1)
        all_day = True
    title = str(comp.get("SUMMARY", "") or "").strip() or "(제목 없음)"
    location = str(comp.get("LOCATION", "") or "").strip()
    notes = str(comp.get("DESCRIPTION", "") or "").strip()
    kind = "event"
    if holiday:
        kind = "observance" if ("기념일" in notes or "observance" in notes.lower()) else "holiday"
        notes = ""
    uid = str(comp.get("UID", "") or "")
    return Event(title, start, end, all_day, cal_name, color, location, notes, kind, source, uid=uid)


def parse_events(cal, start: date, end: date, *, cal_name: str, color: str,
                 source: str, holiday: bool = False) -> list[Event]:
    """iCalendar 데이터에서 start~end 사이의 일정을 꺼내요. 반복 일정도 펼쳐요."""
    try:
        components = list(recurring_ical_events.of(cal, skip_bad_series=True).between(start, end))
    except Exception as exc:
        log_error(f"반복 일정 해석 실패 ({cal_name}): {exc}")
        return []
    events = []
    for comp in components:
        try:
            ev = _component_to_event(comp, cal_name, color, source, holiday)
        except Exception as exc:
            log_error(f"일정 하나를 건너뜀 ({cal_name}): {exc}")
            continue
        if ev:
            events.append(ev)
    return events


def calendar_name(cal, fallback: str) -> str:
    return str(cal.get("X-WR-CALNAME", "") or "").strip() or fallback


def build_event_ics(uid: str, title: str, start, end, all_day: bool, location: str = "",
                    description: str = "") -> bytes:
    cal = icalendar.Calendar()
    cal.add("prodid", f"-//{APP_NAME}//{VERSION}//KO")
    cal.add("version", "2.0")
    ev = icalendar.Event()
    now = datetime.now(timezone.utc).replace(microsecond=0)
    ev.add("uid", uid)
    ev.add("dtstamp", now)
    ev.add("created", now)
    ev.add("last-modified", now)
    ev.add("summary", title)
    if location:
        ev.add("location", location)
    if description:
        ev.add("description", description)
    if all_day:
        ev.add("dtstart", start)
        ev.add("dtend", end)
    else:
        ev.add("dtstart", start.astimezone(timezone.utc))
        ev.add("dtend", end.astimezone(timezone.utc))
    cal.add_component(ev)
    return cal.to_ical()


# ───────────────────────── 네트워크 ─────────────────────────

NS = {"d": "DAV:", "c": "urn:ietf:params:xml:ns:caldav", "a": "http://apple.com/ns/ical/"}
PROPFIND_BODY = (
    '<?xml version="1.0" encoding="utf-8"?>'
    '<d:propfind xmlns:d="DAV:" xmlns:c="urn:ietf:params:xml:ns:caldav" '
    'xmlns:a="http://apple.com/ns/ical/"><d:prop>{props}</d:prop></d:propfind>'
)
REPORT_BODY = (
    '<?xml version="1.0" encoding="utf-8"?>'
    '<c:calendar-query xmlns:d="DAV:" xmlns:c="urn:ietf:params:xml:ns:caldav">'
    '<d:prop><d:getetag/><c:calendar-data/></d:prop>'
    '<c:filter><c:comp-filter name="VCALENDAR"><c:comp-filter name="VEVENT">'
    '<c:time-range start="{start}" end="{end}"/>'
    '</c:comp-filter></c:comp-filter></c:filter></c:calendar-query>'
)


def _ok_props(response) -> ET.Element:
    """multistatus 응답에서 상태가 200인 속성만 모아요."""
    merged = ET.Element("props")
    for propstat in response.findall("d:propstat", NS):
        status = propstat.findtext("d:status", default="", namespaces=NS)
        if " 200 " not in status + " ":
            continue
        prop = propstat.find("d:prop", NS)
        if prop is not None:
            merged.extend(list(prop))
    return merged


def _clean_color(value: str | None) -> str:
    v = (value or "").strip()
    if v.startswith("#") and len(v) >= 7:
        try:
            int(v[1:7], 16)
            return v[:7].upper()
        except ValueError:
            pass
    return ""


def _can_write(props: ET.Element) -> bool:
    privileges = props.find("d:current-user-privilege-set", NS)
    if privileges is None:
        return True
    for priv in privileges.findall("d:privilege", NS):
        for child in priv:
            if child.tag.split("}")[-1] in ("all", "write", "write-content", "bind"):
                return True
    return False


class CalDAVClient:
    """iCloud에 필요한 만큼만 구현한 작은 CalDAV 클라이언트예요."""

    def __init__(self, username: str, password: str, base_url: str = ICLOUD_CALDAV, timeout: int = 25):
        self.base_url = base_url if base_url.endswith("/") else base_url + "/"
        self.http = requests.Session()
        self.http.auth = (username, password)
        self.http.headers["User-Agent"] = USER_AGENT
        self.timeout = timeout

    def _send(self, method: str, url: str, body: bytes | None = None, headers: dict | None = None):
        try:
            resp = self.http.request(method, url, data=body, headers=headers, timeout=self.timeout)
        except requests.RequestException as exc:
            raise network_error("iCloud", exc) from exc
        if resp.status_code == 401:
            raise SyncError("iCloud 로그인에 실패했어요. Apple ID와 앱 암호를 확인해 주세요.")
        if resp.status_code == 403:
            raise SyncError("이 iCloud 캘린더에 접근할 권한이 없어요.")
        if resp.status_code >= 400:
            raise SyncError(f"iCloud가 요청을 처리하지 못했어요 (HTTP {resp.status_code}).")
        return resp

    def _dav(self, method: str, url: str, body: str, depth: int) -> ET.Element:
        resp = self._send(method, url, body.encode("utf-8"),
                          {"Depth": str(depth), "Content-Type": 'application/xml; charset="utf-8"'})
        try:
            return ET.fromstring(resp.content)
        except ET.ParseError as exc:
            raise SyncError("iCloud 응답을 읽지 못했어요.") from exc

    def discover(self) -> list[RemoteCalendar]:
        root = self._dav("PROPFIND", self.base_url,
                         PROPFIND_BODY.format(props="<d:current-user-principal/>"), 0)
        href = root.findtext(".//d:current-user-principal/d:href", namespaces=NS)
        if not href:
            raise SyncError("iCloud 계정 정보를 찾지 못했어요. Apple ID를 확인해 주세요.")
        principal = urljoin(self.base_url, href.strip())

        root = self._dav("PROPFIND", principal, PROPFIND_BODY.format(props="<c:calendar-home-set/>"), 0)
        href = root.findtext(".//c:calendar-home-set/d:href", namespaces=NS)
        if not href:
            raise SyncError("iCloud 캘린더 위치를 찾지 못했어요.")
        home = urljoin(principal, href.strip())

        props_xml = ("<d:resourcetype/><d:displayname/><c:supported-calendar-component-set/>"
                     "<a:calendar-color/><d:current-user-privilege-set/>")
        root = self._dav("PROPFIND", home, PROPFIND_BODY.format(props=props_xml), 1)
        calendars = []
        for resp in root.findall("d:response", NS):
            href = resp.findtext("d:href", namespaces=NS)
            if not href:
                continue
            props = _ok_props(resp)
            rtype = props.find("d:resourcetype", NS)
            if rtype is None or rtype.find("c:calendar", NS) is None:
                continue
            comps = props.find("c:supported-calendar-component-set", NS)
            if comps is not None:
                names = {(c.get("name") or "").upper() for c in comps.findall("c:comp", NS)}
                if names and "VEVENT" not in names:
                    continue  # 미리 알림 목록 같은 것은 빼요
            name = (props.findtext("d:displayname", default="", namespaces=NS) or "").strip() or "캘린더"
            calendars.append(RemoteCalendar(
                name=name,
                url=urljoin(home, href.strip()),
                color=_clean_color(props.findtext("a:calendar-color", default="", namespaces=NS)),
                writable=_can_write(props),
            ))
        return calendars

    def calendar_query(self, cal_url: str, start_utc: datetime, end_utc: datetime) -> list[str]:
        body = REPORT_BODY.format(start=start_utc.strftime("%Y%m%dT%H%M%SZ"),
                                  end=end_utc.strftime("%Y%m%dT%H%M%SZ"))
        root = self._dav("REPORT", cal_url, body, 1)
        out = []
        for resp in root.findall("d:response", NS):
            data = _ok_props(resp).findtext("c:calendar-data", default="", namespaces=NS)
            if data and data.strip():
                out.append(data)
        return out

    def put_event(self, cal_url: str, uid: str, ics: bytes) -> str:
        url = cal_url.rstrip("/") + "/" + quote(uid, safe="") + ".ics"
        self._send("PUT", url, ics, {"Content-Type": "text/calendar; charset=utf-8", "If-None-Match": "*"})
        return url

    def delete(self, url: str) -> None:
        try:
            resp = self.http.request("DELETE", url, timeout=self.timeout)
        except requests.RequestException as exc:
            raise network_error("iCloud", exc) from exc
        if resp.status_code >= 400 and resp.status_code not in (404, 410):  # 이미 지워졌으면 괜찮아요
            raise SyncError(f"iCloud 일정을 지우지 못했어요 (HTTP {resp.status_code}).")


def clean_notes(text: str) -> str:
    """Google 메모에 섞인 HTML 태그를 걷어 내요."""
    if "<" in text and ">" in text:
        text = re.sub(r"(?i)<br\s*/?>|</p>|</div>|</li>", "\n", text)
        text = re.sub(r"<[^>]+>", "", text)
    return html.unescape(text).strip()


def parse_iso(text: str) -> datetime:
    t = text.strip()
    if t.endswith("Z"):
        t = t[:-1] + "+00:00"
    return datetime.fromisoformat(t)


def parse_google(data: dict) -> tuple[list[RemoteCalendar], list[Event]]:
    """연결 코드가 돌려준 JSON을 캘린더 목록과 일정으로 바꿔요."""
    calendars, by_id = [], {}
    for i, c in enumerate(data.get("calendars") or []):
        cid = str(c.get("id") or "")
        if not cid:
            continue
        cal = RemoteCalendar(name=str(c.get("name") or "Google 캘린더"), url=cid,
                             color=_clean_color(c.get("color")) or PALETTE[i % len(PALETTE)],
                             writable=bool(c.get("writable")), source="Google", primary=bool(c.get("primary")))
        calendars.append(cal)
        by_id[cid] = (cal, bool(c.get("holiday")))
    events = []
    for item in data.get("events") or []:
        try:
            cal, holiday = by_id[item["cal"]]
            if item.get("allDay"):
                start = date.fromisoformat(str(item["start"])[:10])
                end = date.fromisoformat(str(item["end"])[:10])
                if end <= start:
                    end = start + timedelta(days=1)
                all_day = True
            else:
                start = parse_iso(str(item["start"])).astimezone()
                end = max(parse_iso(str(item["end"])).astimezone(), start)
                all_day = False
            notes = clean_notes(str(item.get("notes") or ""))
            kind = "event"
            if holiday:
                kind = "observance" if ("기념일" in notes or "observance" in notes.lower()) else "holiday"
                notes = ""
            events.append(Event(str(item.get("title") or "").strip() or "(제목 없음)", start, end, all_day,
                                cal.name, cal.color, str(item.get("location") or "").strip(), notes, kind,
                                "Google", uid=str(item.get("uid") or ""), cal_key=f"google:{item['cal']}"))
        except (KeyError, TypeError, ValueError) as exc:
            log_error(f"Google 일정 하나를 건너뜀: {exc}")
    return calendars, events


def month_floor(d: date) -> date:
    return d.replace(day=1)


def month_ceil(d: date) -> date:
    """d가 1일이면 그대로, 아니면 다음 달 1일"""
    return d if d.day == 1 else (d.replace(day=28) + timedelta(days=4)).replace(day=1)


def month_starts(start: date, end: date) -> list[date]:
    out, d = [], month_floor(start)
    while d < end:
        out.append(d)
        d = month_ceil(d + timedelta(days=1))
    return out


def add_interval(intervals: list, start: date, end: date) -> list:
    """겹치거나 맞닿은 구간을 합쳐서 정렬된 목록으로 돌려줘요."""
    out: list = []
    for a, b in sorted(list(intervals) + [(start, end)]):
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def missing_parts(intervals: list, start: date, end: date) -> list:
    """[start, end) 가운데 intervals로 덮이지 않은 부분들"""
    parts, cur = [], start
    for a, b in sorted(intervals):
        if b <= cur:
            continue
        if a >= end:
            break
        if a > cur:
            parts.append((cur, min(a, end)))
        cur = max(cur, b)
        if cur >= end:
            break
    if cur < end:
        parts.append((cur, end))
    return parts


def event_span(ev: Event) -> tuple[date, date]:
    """일정이 걸친 날 (첫날, 마지막 날의 다음 날)"""
    if ev.all_day:
        return ev.start, max(ev.end, ev.start + timedelta(days=1))
    last = (ev.end - timedelta(microseconds=1)).date() if ev.end > ev.start else ev.start.date()
    return ev.start.date(), last + timedelta(days=1)


def event_to_dict(ev: Event) -> dict:
    data = {k: getattr(ev, k) for k in ("title", "all_day", "cal_name", "location", "notes", "kind", "source", "uid",
                                        "cal_key", "ref")}
    data["color"] = ev.__dict__.get("_orig_color", ev.color)  # 위젯에서 바꾼 색이 아니라 원래 색을 저장해요
    data["start"], data["end"] = ev.start.isoformat(), ev.end.isoformat()
    return data


def event_from_dict(d: dict) -> Event:
    conv = date.fromisoformat if d["all_day"] else datetime.fromisoformat
    return Event(d["title"], conv(d["start"]), conv(d["end"]), bool(d["all_day"]), d.get("cal_name", ""),
                 d.get("color", "#888888"), d.get("location", ""), d.get("notes", ""), d.get("kind", "event"),
                 d.get("source", ""), uid=d.get("uid", ""), cal_key=d.get("cal_key", ""), ref=d.get("ref") or {})


def dedupe_events(events: list[Event]) -> list[Event]:
    """같은 일정이 여러 경로로 들어오면(예: Google 연결 + Google iCal 주소) 앞의 것만 남겨요."""
    seen, out = set(), []
    for ev in events:
        if ev.uid:
            key = (ev.uid, ev.start if ev.all_day else ev.start.astimezone(timezone.utc))
            if key in seen:
                continue
            seen.add(key)
        out.append(ev)
    return out


class GoogleScriptClient:
    """내 Google 계정에 설치한 연결 코드(Apps Script 웹 앱)와 이야기해요."""

    def __init__(self, url: str, token: str, timeout: int = 45):
        self.url, self.token, self.timeout = url.strip(), token, timeout

    def call(self, action: str, **params) -> dict:
        body = json.dumps({"token": self.token, "action": action, **params}, ensure_ascii=False).encode("utf-8")
        try:
            resp = requests.post(self.url, data=body, timeout=self.timeout,
                                 headers={"Content-Type": "application/json", "User-Agent": USER_AGENT})
        except requests.RequestException as exc:
            raise network_error("Google", exc) from exc
        if resp.status_code == 404:
            raise SyncError("Google 웹 앱 주소를 찾을 수 없어요. 설정의 웹 앱 URL을 확인해 주세요.")
        if resp.status_code >= 400:
            raise SyncError(f"Google 웹 앱이 요청을 처리하지 못했어요 (HTTP {resp.status_code}).")
        try:
            data = resp.json()
        except ValueError:
            raise SyncError("Google 웹 앱이 일정 대신 다른 화면을 보냈어요. "
                            "배포할 때 액세스를 '모든 사용자'로 했는지 확인해 주세요.") from None
        if not isinstance(data, dict) or not data.get("ok"):
            code = data.get("error", "") if isinstance(data, dict) else ""
            if code == "unauthorized":
                raise SyncError("Google 연결 코드의 비밀 키가 맞지 않아요. "
                                "설정에서 코드를 다시 복사해 붙여 넣고 새 버전으로 배포해 주세요.")
            if code == "calendar_not_found":
                raise SyncError("일정을 넣을 Google 캘린더를 찾지 못했어요.")
            raise SyncError(f"Google 캘린더에서 오류가 났어요: {code or '알 수 없는 오류'}")
        return data


# ── Google 계정으로 로그인 (OAuth 2.0, 데스크톱 앱 + PKCE) ──
LOGIN_EXPIRED = "Google 로그인이 풀렸어요"
GOOGLE_AUTH_URL = os.environ.get("CW_GOOGLE_AUTH_URL") or "https://accounts.google.com/o/oauth2/v2/auth"
GOOGLE_TOKEN_URL = os.environ.get("CW_GOOGLE_TOKEN_URL") or "https://oauth2.googleapis.com/token"
GOOGLE_REVOKE_URL = os.environ.get("CW_GOOGLE_REVOKE_URL") or "https://oauth2.googleapis.com/revoke"
GOOGLE_API = os.environ.get("CW_GOOGLE_API") or "https://www.googleapis.com/calendar/v3"
SCOPE_READ = "https://www.googleapis.com/auth/calendar.readonly"
SCOPE_WRITE = "https://www.googleapis.com/auth/calendar.events"
SCOPE_FULL = "https://www.googleapis.com/auth/calendar"        # 캘린더 만들기 · 지우기까지
SCOPE_DRIVE = "https://www.googleapis.com/auth/drive.file"     # 위젯이 올린 첨부 파일만 다뤄요
GOOGLE_DRIVE = os.environ.get("CW_GOOGLE_DRIVE") or "https://www.googleapis.com/drive/v3"
GOOGLE_UPLOAD = os.environ.get("CW_GOOGLE_UPLOAD") or "https://www.googleapis.com/upload/drive/v3"
SCOPE_TASKS = "https://www.googleapis.com/auth/tasks"           # Google Tasks (할 일 · 하위 할 일)
GOOGLE_TASKS = os.environ.get("CW_GOOGLE_TASKS") or "https://tasks.googleapis.com/tasks/v1"
TIME_MARK = "[시간] "  # Tasks는 시간을 못 받아서 메모 끝에 적어 둬요
DEADLINE_MARK = "[기한] "  # 기한(마감일)도 Tasks API로는 못 주고받아서 메모 끝에 적어 둬요
TASKS_POLL_MS = 60_000  # Tasks 앱에서 넣은 할 일을 1분마다 확인해요
ATTACH_FOLDER = "캘린더 위젯 첨부"
ATTACH_MARK = "[첨부 파일]"
ATTACH_MAX_MB = 50

open_browser = webbrowser.open  # 시험할 때 바꿔 끼울 수 있게 따로 둬요


class GoogleCalendarAPI:
    """Google Calendar API를 직접 불러요. 로그인 정보(refresh token)로 접근 토큰을 받아 써요."""

    def __init__(self, refresh_token: str, timeout: int = 30):
        self.refresh_token = refresh_token
        self.timeout = timeout
        self.access_token = ""
        self.expires_at = 0.0
        self.http = requests.Session()
        self.http.headers["User-Agent"] = USER_AGENT

    def _refresh(self) -> None:
        try:
            resp = self.http.post(GOOGLE_TOKEN_URL, timeout=self.timeout, data={
                "client_id": GOOGLE_CLIENT_ID, "client_secret": GOOGLE_CLIENT_SECRET,
                "refresh_token": self.refresh_token, "grant_type": "refresh_token"})
        except requests.RequestException as exc:
            raise network_error("Google", exc) from exc
        try:
            data = resp.json()
        except ValueError:
            data = {}
        if resp.status_code != 200 or not data.get("access_token"):
            if data.get("error") in ("invalid_grant", "unauthorized_client", "invalid_client"):
                raise SyncError("Google 로그인이 풀렸어요. 설정의 Google 탭에서 다시 로그인해 주세요.")
            raise SyncError(f"Google 로그인 정보를 새로 받지 못했어요 (HTTP {resp.status_code}).")
        self.access_token = data["access_token"]
        self.expires_at = time.monotonic() + int(data.get("expires_in", 3600)) - 60

    def _request(self, method: str, path: str, raw: bool = False, headers: dict | None = None, **kwargs):
        url = path if path.startswith("http") else GOOGLE_API + path
        timeout = kwargs.pop("timeout", self.timeout)
        for attempt in range(2):
            if not self.access_token or time.monotonic() >= self.expires_at:
                self._refresh()
            try:
                resp = self.http.request(method, url, timeout=timeout,
                                         headers={"Authorization": f"Bearer {self.access_token}", **(headers or {})},
                                         **kwargs)
            except requests.RequestException as exc:
                raise network_error("Google", exc) from exc
            if resp.status_code == 401 and attempt == 0:
                self.access_token = ""  # 토큰이 막 만료됐으면 한 번 더
                continue
            if resp.status_code == 429 or (resp.status_code == 403 and "ratelimit" in resp.text.lower()):
                raise RateLimited("Google이 잠깐 쉬었다가 다시 보내 달라고 했어요.")
            if resp.status_code == 403:
                text = resp.text.lower()
                if "insufficient" in text:
                    raise NeedPermission("이 기능은 Google 권한이 더 필요해요. 설정 → Google에서 로그아웃한 뒤 다시 로그인해서 "
                                         "새 권한(캘린더 관리, 첨부 파일)에 모두 동의해 주세요.")
                if "accessnotconfigured" in text or "service_disabled" in text or "has not been used" in text:
                    which = "Google Tasks API" if "tasks" in text else "Google Drive API" if "drive" in text else "필요한 API"
                    raise SyncError(f"Google Cloud에서 {which}가 꺼져 있어요. Google Cloud → API 및 서비스 → 라이브러리에서 "
                                    f"'{which}'를 찾아 사용 설정해 주세요.")
                if "only the data owner" in text or ("owner" in text and method == "DELETE"):
                    raise SyncError("이 캘린더는 내가 만든 캘린더가 아니라서 지울 수 없어요.")
                raise SyncError("Google 캘린더에 접근할 권한이 없어요. "
                                "설정의 Google 탭에서 다시 로그인하고 캘린더 권한을 모두 체크해 주세요.")
            if resp.status_code in (404, 410):
                raise SyncError("Google 캘린더를 찾지 못했어요.")
            if resp.status_code >= 400:
                raise SyncError(f"Google 캘린더가 요청을 처리하지 못했어요 (HTTP {resp.status_code}).")
            if raw:
                return resp
            return resp.json() if resp.content else {}
        raise SyncError("Google 로그인이 풀렸어요. 설정의 Google 탭에서 다시 로그인해 주세요.")

    def calendar_list(self) -> list:
        items, page = [], None
        while True:
            params = {"minAccessRole": "reader", "maxResults": 250}
            if page:
                params["pageToken"] = page
            data = self._request("GET", "/users/me/calendarList", params=params)
            items += data.get("items") or []
            page = data.get("nextPageToken")
            if not page:
                return items

    def events(self, calendar_id: str, start_utc: datetime, end_utc: datetime) -> list:
        items, page = [], None
        while True:
            params = {"timeMin": start_utc.strftime("%Y-%m-%dT%H:%M:%SZ"),
                      "timeMax": end_utc.strftime("%Y-%m-%dT%H:%M:%SZ"),
                      "singleEvents": "true", "orderBy": "startTime", "maxResults": 2500, "showDeleted": "false",
                      "eventLabelVersion": 1}
            if page:
                params["pageToken"] = page
            data = self._request("GET", f"/calendars/{quote(calendar_id, safe='')}/events", params=params)
            items += data.get("items") or []
            page = data.get("nextPageToken")
            if not page:
                return items

    def calendar_labels(self, calendar_id: str) -> dict:
        """캘린더에 만들어 둔 일정 라벨(색) {라벨 ID: 색}. 30분 동안 기억해요."""
        cache = self.__dict__.setdefault("_labels", {})
        hit = cache.get(calendar_id)
        if hit and time.time() - hit[0] < 1800:
            return hit[1]
        labels = {}
        try:
            data = self._request("GET", f"/calendars/{quote(calendar_id, safe='')}",
                                 params={"eventLabelVersion": 1})
            for lab in (data.get("labelProperties") or {}).get("eventLabels") or []:
                color = _clean_color(lab.get("backgroundColor"))
                if lab.get("id") and color:
                    labels[str(lab["id"])] = color
        except SyncError:
            labels = {}  # 라벨을 못 읽어도 일정은 그대로 보여요
        cache[calendar_id] = (time.time(), labels)
        return labels

    def insert_event(self, calendar_id: str, body: dict, send_updates: str = "none") -> dict:
        params = {"sendUpdates": send_updates}
        if "attachments" in body:
            params["supportsAttachments"] = "true"
        return self._request("POST", f"/calendars/{quote(calendar_id, safe='')}/events", params=params, json=body)

    def create_calendar(self, name: str) -> dict:
        return self._request("POST", "/calendars", json={"summary": name, "timeZone": "Asia/Seoul"})

    def delete_calendar(self, calendar_id: str) -> None:
        self._request("DELETE", f"/calendars/{quote(calendar_id, safe='')}")

    def _tasks_url(self, list_id: str, *parts: str) -> str:
        return f"{GOOGLE_TASKS}/lists/{quote(list_id, safe='@')}/tasks" + "".join(f"/{quote(p, safe='')}" for p in parts)

    def task_lists(self) -> list:
        """Tasks 목록들 [{id, title}] (내 할 일 + 직접 만든 목록)"""
        out, page = [], None
        while True:
            params = {"maxResults": 100}
            if page:
                params["pageToken"] = page
            data = self._request("GET", f"{GOOGLE_TASKS}/users/@me/lists", params=params)
            out += [{"id": str(x["id"]), "title": str(x.get("title") or "")} for x in data.get("items") or [] if x.get("id")]
            page = data.get("nextPageToken")
            if not page:
                return out

    def default_task_list(self) -> str:
        return str(self._request("GET", f"{GOOGLE_TASKS}/users/@me/lists/@default").get("id") or "@default")

    def tasks_all(self, list_id: str) -> list:
        """목록의 할 일을 모두 (끝낸 것 · 숨긴 것 · 지운 것까지) 받아요."""
        items, page = [], None
        while True:
            params = {"maxResults": 100, "showCompleted": "true", "showHidden": "true", "showDeleted": "true"}
            if page:
                params["pageToken"] = page
            data = self._request("GET", self._tasks_url(list_id), params=params)
            items += data.get("items") or []
            page = data.get("nextPageToken")
            if not page:
                return items

    def task_insert(self, list_id: str, body: dict, parent: str | None = None) -> dict:
        return self._request("POST", self._tasks_url(list_id), params={"parent": parent} if parent else {}, json=body)

    def task_patch(self, list_id: str, task_id: str, body: dict) -> dict:
        return self._request("PATCH", self._tasks_url(list_id, task_id), json=body)

    def task_move(self, list_id: str, task_id: str, parent: str | None = None) -> dict:
        return self._request("POST", self._tasks_url(list_id, task_id) + "/move",
                             params={"parent": parent} if parent else {})

    def task_delete(self, list_id: str, task_id: str) -> None:
        try:
            self._request("DELETE", self._tasks_url(list_id, task_id))
        except SyncError as exc:
            if "찾지 못했어요" not in str(exc):
                raise

    def drive_folder(self) -> str:
        """첨부 파일을 모아 둘 드라이브 폴더 ('캘린더 위젯 첨부'). 없으면 만들어요."""
        if getattr(self, "_folder", ""):
            return self._folder
        q = f"name='{ATTACH_FOLDER}' and mimeType='application/vnd.google-apps.folder' and trashed=false"
        found = self._request("GET", GOOGLE_DRIVE + "/files", params={"q": q, "fields": "files(id,name)", "spaces": "drive"})
        files = found.get("files") or []
        if files:
            self._folder = str(files[0]["id"])
        else:
            made = self._request("POST", GOOGLE_DRIVE + "/files", params={"fields": "id"},
                                 json={"name": ATTACH_FOLDER, "mimeType": "application/vnd.google-apps.folder"})
            self._folder = str(made["id"])
        return self._folder

    def upload_file(self, path: str, folder_id: str) -> dict:
        """파일 하나를 드라이브에 올리고 일정에 붙일 정보를 돌려줘요."""
        import mimetypes
        name = os.path.basename(path)
        size = os.path.getsize(path)
        if size > ATTACH_MAX_MB * 1024 * 1024:
            raise SyncError(f"'{name}'은 {ATTACH_MAX_MB}MB보다 커서 넣을 수 없어요.")
        mime = mimetypes.guess_type(path)[0] or "application/octet-stream"
        start = self._request("POST", GOOGLE_UPLOAD + "/files", raw=True,
                              params={"uploadType": "resumable", "fields": "id,name,mimeType,webViewLink,iconLink"},
                              headers={"X-Upload-Content-Type": mime, "X-Upload-Content-Length": str(size)},
                              json={"name": name, "parents": [folder_id]})
        session = start.headers.get("Location", "")
        if not session:
            raise SyncError("드라이브에 파일을 올릴 준비를 하지 못했어요.")
        with open(path, "rb") as fh:
            info = self._request("PUT", session, raw=True, data=fh.read(), headers={"Content-Type": mime},
                                 timeout=600).json()
        return {"fileUrl": info.get("webViewLink") or f"https://drive.google.com/open?id={info['id']}",
                "title": info.get("name") or name, "mimeType": info.get("mimeType") or mime,
                "fileId": info.get("id", ""), "iconLink": info.get("iconLink", "")}

    def patch_event(self, calendar_id: str, event_id: str, body: dict, send_updates: str = "none",
                    label_version: bool = False) -> dict:
        params = {"sendUpdates": send_updates}
        if label_version:
            params["eventLabelVersion"] = 1
        if "attachments" in body:
            params["supportsAttachments"] = "true"
        return self._request("PATCH", f"/calendars/{quote(calendar_id, safe='')}/events/{quote(event_id, safe='')}",
                             params=params, json=body)

    def move_event(self, calendar_id: str, event_id: str, destination: str, send_updates: str = "none") -> dict:
        return self._request("POST",
                             f"/calendars/{quote(calendar_id, safe='')}/events/{quote(event_id, safe='')}/move",
                             params={"destination": destination, "sendUpdates": send_updates})

    def delete_event(self, calendar_id: str, event_id: str, send_updates: str = "none") -> None:
        try:
            self._request("DELETE", f"/calendars/{quote(calendar_id, safe='')}/events/{quote(event_id, safe='')}",
                          params={"sendUpdates": send_updates})
        except SyncError as exc:
            if "찾지 못했어요" not in str(exc):  # 이미 지워졌으면 괜찮아요
                raise


def google_login(timeout: int = 300) -> dict:
    """브라우저로 Google 로그인을 받아요. 로그인을 마치면 로그인 정보와 계정 주소를 돌려줘요."""
    if not GOOGLE_CLIENT_ID:
        raise SyncError("이 프로그램에는 Google 로그인 정보가 들어 있지 않아요.")
    verifier = secrets.token_urlsafe(64)
    challenge = base64.urlsafe_b64encode(hashlib.sha256(verifier.encode("ascii")).digest()).rstrip(b"=").decode()
    state = secrets.token_urlsafe(16)
    result: dict = {}

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_GET(self):
            query = parse_qs(urlparse(self.path).query)
            if query.get("state", [""])[0] != state:
                self._page(404, "")  # 아이콘 요청처럼 상관없는 요청은 무시해요
                return
            if "error" in query:
                result["error"] = query["error"][0]
                self._page(200, "로그인을 취소했어요. 이 창을 닫아도 돼요.")
            else:
                result["code"] = query.get("code", [""])[0]
                self._page(200, "로그인이 끝났어요. 이 창을 닫고 캘린더 위젯으로 돌아가세요.")

        def _page(self, status: int, message: str):
            body = ('<!doctype html><meta charset="utf-8"><title>캘린더 위젯</title>'
                    '<body style="font-family:\'Malgun Gothic\',sans-serif;text-align:center;padding:14vh 24px;'
                    f'color:#38332D;background:#F7F3EC"><h2>캘린더 위젯</h2><p>{html.escape(message)}</p></body>'
                    ).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

    server = HTTPServer(("127.0.0.1", 0), Handler)
    server.timeout = 0.5
    redirect = f"http://127.0.0.1:{server.server_address[1]}"
    params = {"client_id": GOOGLE_CLIENT_ID, "redirect_uri": redirect, "response_type": "code",
              "scope": f"{SCOPE_FULL} {SCOPE_DRIVE} {SCOPE_TASKS}", "code_challenge": challenge, "code_challenge_method": "S256",
              "state": state, "access_type": "offline", "prompt": "consent select_account"}
    try:
        open_browser(GOOGLE_AUTH_URL + "?" + urlencode(params))
        deadline = time.monotonic() + timeout
        while not result and time.monotonic() < deadline:
            server.handle_request()
    finally:
        server.server_close()
    if not result:
        raise SyncError("로그인 시간이 지났어요. 다시 시도해 주세요.")
    if "error" in result:
        raise SyncError("Google 로그인을 취소했어요." if result["error"] == "access_denied"
                        else f"Google 로그인 중에 문제가 생겼어요 ({result['error']}).")
    try:
        resp = requests.post(GOOGLE_TOKEN_URL, timeout=30, headers={"User-Agent": USER_AGENT}, data={
            "client_id": GOOGLE_CLIENT_ID, "client_secret": GOOGLE_CLIENT_SECRET, "code": result["code"],
            "code_verifier": verifier, "grant_type": "authorization_code", "redirect_uri": redirect})
    except requests.RequestException as exc:
        raise network_error("Google", exc) from exc
    try:
        data = resp.json()
    except ValueError:
        data = {}
    if resp.status_code != 200 or not data.get("refresh_token"):
        log_error(f"Google 토큰 교환 실패: HTTP {resp.status_code} {data.get('error', '')}")
        raise SyncError("Google에서 로그인 정보를 받지 못했어요. 다시 시도해 주세요.")
    granted = set((data.get("scope") or "").split())
    if not granted & {SCOPE_READ, SCOPE_WRITE, SCOPE_FULL}:
        raise SyncError("캘린더 보기 권한이 허용되지 않았어요. 다시 로그인해서 캘린더 권한을 모두 체크해 주세요.")
    api = GoogleCalendarAPI(data["refresh_token"])
    api.access_token = data.get("access_token", "")
    api.expires_at = time.monotonic() + int(data.get("expires_in", 3600)) - 60
    email = next((c.get("id", "") for c in api.calendar_list() if c.get("primary")), "")
    return {"refresh_token": data["refresh_token"], "email": email, "can_write": bool(granted & {SCOPE_WRITE, SCOPE_FULL})}


def revoke_google(token: str) -> None:
    try:
        requests.post(GOOGLE_REVOKE_URL, params={"token": token}, timeout=10, headers={"User-Agent": USER_AGENT})
    except requests.RequestException:
        pass


def google_api_event(item: dict, cal: RemoteCalendar, holiday: bool, labels: dict | None = None) -> Event | None:
    """Calendar API의 일정 하나를 위젯의 일정으로 바꿔요."""
    if item.get("status") == "cancelled":
        return None
    if any(a.get("self") and a.get("responseStatus") == "declined" for a in item.get("attendees") or []):
        return None  # 거절한 초대는 빼요
    s, e = item.get("start") or {}, item.get("end") or {}
    if "date" in s:
        start = date.fromisoformat(s["date"])
        end = date.fromisoformat(e.get("date") or s["date"])
        if end <= start:
            end = start + timedelta(days=1)
        all_day = True
    else:
        start = parse_iso(s["dateTime"]).astimezone()
        end = max(parse_iso(e.get("dateTime") or s["dateTime"]).astimezone(), start)
        all_day = False
    notes = clean_notes(str(item.get("description") or ""))
    kind = "event"
    if holiday:
        kind = "observance" if ("기념일" in notes or "observance" in notes.lower()) else "holiday"
        notes = ""
    attendees = [{k: a[k] for k in ("email", "displayName", "responseStatus", "organizer", "self", "optional",
                                    "resource") if k in a}
                 for a in item.get("attendees") or [] if a.get("email")]
    organizer_self = (item.get("organizer") or {}).get("self", True)
    widget_color = _clean_color(((item.get("extendedProperties") or {}).get("private") or {}).get("widgetColor"))
    label_id, color_id = str(item.get("eventLabelId") or ""), str(item.get("colorId") or "")
    event_color = widget_color or (labels or {}).get(label_id, "") or CLASSIC_EVENT_COLORS.get(color_id, "")
    ref = {"calendar_id": cal.url, "event_id": str(item.get("id") or ""), "event_color": event_color,
           "label_id": label_id, "color_id": color_id,
           "todo_id": str(((item.get("extendedProperties") or {}).get("private") or {}).get("widgetTodo") or ""),
           "attachments": [dict(a) for a in item.get("attachments") or [] if isinstance(a, dict) and a.get("fileUrl")],
           "recurring": bool(item.get("recurringEventId")), "attendees_raw": attendees,
           "guests_can_modify": bool(item.get("guestsCanModify")),
           "editable": bool(cal.writable) and not holiday and (organizer_self or bool(item.get("guestsCanModify")))}
    return Event(str(item.get("summary") or "").strip() or "(제목 없음)", start, end, all_day, cal.name, cal.color,
                 str(item.get("location") or "").strip(), notes, kind, "Google",
                 uid=str(item.get("iCalUID") or item.get("id") or ""), cal_key=cal.key, ref=ref)


def google_from_api(api: GoogleCalendarAPI, start: date, end: date, can_write: bool) -> tuple[list, list]:
    s_utc = local_midnight(start).astimezone(timezone.utc)
    e_utc = local_midnight(end).astimezone(timezone.utc)
    calendars, events = [], []
    for i, item in enumerate(api.calendar_list()):
        cid = str(item.get("id") or "")
        if not cid or item.get("hidden"):  # '목록에서 숨기기'만 빼고, 웹에서 체크를 꺼 둔 캘린더도 가져와요
            continue
        cal = RemoteCalendar(name=str(item.get("summaryOverride") or item.get("summary") or "Google 캘린더"),
                             url=cid, color=_clean_color(item.get("backgroundColor")) or PALETTE[i % len(PALETTE)],
                             writable=can_write and item.get("accessRole") in ("owner", "writer"),
                             source="Google", primary=bool(item.get("primary")),
                             owner=item.get("accessRole") == "owner")
        calendars.append(cal)
        holiday = "#holiday@" in cid
        labels = {} if holiday else api.calendar_labels(cid)
        for raw in api.events(cid, s_utc, e_utc):
            try:
                ev = google_api_event(raw, cal, holiday, labels)
            except (KeyError, TypeError, ValueError) as exc:
                log_error(f"Google 일정 하나를 건너뜀: {exc}")
                continue
            if ev:
                events.append(ev)
    return calendars, events


# ── 업데이트 (GitHub 릴리스) ──
def is_frozen() -> bool:
    """설치 파일로 설치한 exe로 실행 중인지"""
    return bool(getattr(sys, "frozen", False))


def resource_path(*parts: str) -> str:
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, *parts)


def version_tuple(text: str) -> tuple:
    nums = [int(x) for x in re.findall(r"\d+", text or "")[:3]]
    return tuple(nums + [0] * (3 - len(nums)))


def update_info_url() -> str:
    custom = os.environ.get("CW_UPDATE_URL")
    if custom:
        return custom
    return f"https://github.com/{UPDATE_REPO}/releases/latest/download/latest.json" if UPDATE_REPO else ""


def check_for_update() -> dict | None:
    """새 버전이 있으면 그 정보를, 없으면 None을 돌려줘요."""
    url = update_info_url()
    if not url:
        return None
    try:
        resp = requests.get(url, timeout=20, headers={"User-Agent": USER_AGENT})
    except requests.RequestException as exc:
        raise network_error("업데이트 서버", exc) from exc
    if resp.status_code == 404:
        return None  # 아직 릴리스가 없거나 설치 파일이 올라오는 중이에요
    if resp.status_code >= 400:
        raise SyncError(f"업데이트를 확인하지 못했어요 (HTTP {resp.status_code}).")
    try:
        data = resp.json()
        version, installer, sha = str(data["version"]), str(data["installer"]), str(data["sha256"]).lower()
    except (ValueError, KeyError, TypeError):
        raise SyncError("업데이트 정보를 읽지 못했어요.") from None
    if version_tuple(version) <= version_tuple(VERSION) or not re.fullmatch(r"[0-9a-f]{64}", sha):
        return None
    tag = str(data.get("tag") or f"v{version}")
    base = f"https://github.com/{UPDATE_REPO}/releases"
    return {"version": version, "name": os.path.basename(installer), "sha256": sha,
            "url": str(data.get("url") or f"{base}/download/{tag}/{installer}"),
            "page": str(data.get("page") or f"{base}/tag/{tag}")}


def download_update(info: dict) -> str:
    folder = os.path.join(tempfile.gettempdir(), APP_NAME)
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, info["name"])
    digest = hashlib.sha256()
    try:
        with requests.get(info["url"], stream=True, timeout=60, headers={"User-Agent": USER_AGENT}) as resp:
            if resp.status_code >= 400:
                raise SyncError(f"업데이트 파일을 내려받지 못했어요 (HTTP {resp.status_code}).")
            with open(path + ".part", "wb") as f:
                for chunk in resp.iter_content(1 << 16):
                    f.write(chunk)
                    digest.update(chunk)
    except requests.RequestException as exc:
        raise network_error("업데이트 서버", exc) from exc
    if digest.hexdigest() != info["sha256"]:
        os.remove(path + ".part")
        raise SyncError("내려받은 업데이트 파일이 손상됐어요. 나중에 다시 시도할게요.")
    os.replace(path + ".part", path)
    return path


def launch_installer(path: str) -> None:
    """설치 파일을 조용히 실행해요. 설치가 끝나면 설치 파일이 위젯을 다시 켜 줘요."""
    flags = 0x00000008 | 0x00000200 if IS_WINDOWS else 0  # DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP
    subprocess.Popen([path, "/VERYSILENT", "/SUPPRESSMSGBOXES", "/NORESTART", "/CLOSEAPPLICATIONS"],
                     creationflags=flags, close_fds=True)


def ics_label(url: str) -> tuple[str, str]:
    """iCal 주소로 (오류 메시지에 쓸 이름, 출처 이름)을 정해요."""
    return ("Google 캘린더", "Google") if "google.com" in url else ("구독 캘린더", "구독")


def fetch_ics(url: str, label: str = "구독 캘린더") -> bytes:
    url = url.strip()
    if url.lower().startswith("webcal://"):
        url = "https://" + url[len("webcal://"):]
    try:
        resp = requests.get(url, timeout=25, headers={"User-Agent": USER_AGENT})
    except requests.RequestException as exc:
        raise network_error(label, exc) from exc
    if resp.status_code == 404:
        raise SyncError(f"{label} 주소를 찾을 수 없어요. 'iCal 형식의 비공개 주소'를 다시 복사해 주세요.")
    if resp.status_code >= 400:
        raise SyncError(f"{label}을(를) 가져오지 못했어요 (HTTP {resp.status_code}).")
    if b"BEGIN:VCALENDAR" not in resp.content[:4096]:
        raise SyncError(f"{label} 주소가 iCal 주소가 아니에요. 'iCal 형식의 비공개 주소'를 넣어 주세요.")
    return resp.content


class CalendarService:
    """모든 네트워크 작업을 맡아요. 작업 스레드에서만 써요."""

    def __init__(self):
        self.settings: dict = {}
        self.client: CalDAVClient | None = None
        self.calendars: list[RemoteCalendar] = []         # iCloud 캘린더
        self.google_calendars: list[RemoteCalendar] = []  # 마지막으로 받은 Google 캘린더
        self.google_api: GoogleCalendarAPI | None = None
        self.discovered_at = 0.0
        self._holidays: tuple[date, object] | None = None

    def configure(self, settings: dict) -> None:
        keys = ("caldav_url", "apple_id", "password")
        if tuple(settings.get(k) for k in keys) != tuple(self.settings.get(k) for k in keys):
            self.client, self.calendars, self.discovered_at = None, [], 0.0
        if (settings.get("google_url"), settings.get("google_token"), settings.get("google_refresh")) != \
                (self.settings.get("google_url"), self.settings.get("google_token"), self.settings.get("google_refresh")):
            self.google_calendars, self.google_api = [], None
        if settings.get("holiday_url") != self.settings.get("holiday_url"):
            self._holidays = None
        self.settings = dict(settings)

    def _google_api(self) -> GoogleCalendarAPI | None:
        token = self.settings.get("google_refresh")
        if not token:
            return None
        if self.google_api is None or self.google_api.refresh_token != token:
            self.google_api = GoogleCalendarAPI(token)
        return self.google_api

    def _google(self) -> GoogleScriptClient | None:
        s = self.settings
        if s.get("google_url") and s.get("google_token"):
            return GoogleScriptClient(s["google_url"], s["google_token"])
        return None

    def _icloud_ready(self) -> bool:
        s = self.settings
        if not (s.get("apple_id") and s.get("password")):
            self.client, self.calendars = None, []
            return False
        if self.client is None or time.monotonic() - self.discovered_at > 1800:
            client = CalDAVClient(s["apple_id"], s["password"], s.get("caldav_url") or ICLOUD_CALDAV)
            self.calendars = client.discover()
            self.client, self.discovered_at = client, time.monotonic()
        return True

    def _holiday_calendar(self):
        today = date.today()
        if self._holidays is None or self._holidays[0] != today:
            data = fetch_ics(self.settings.get("holiday_url") or KOREAN_HOLIDAYS_ICS, "공휴일 캘린더")
            self._holidays = (today, icalendar.Calendar.from_ical(data))
        return self._holidays[1]

    def fetch(self, start: date, end: date) -> FetchResult:
        events, problems = [], []
        google_has_holidays = False

        api = self._google_api()
        google = None if api else self._google()
        if api is not None:
            try:
                self.google_calendars, google_events = google_from_api(
                    api, start, end, bool(self.settings.get("google_can_write", True)))
                events += google_events
            except SyncError as exc:
                problems.append(str(exc))
            except Exception:
                log_error("Google 동기화 오류\n" + traceback.format_exc())
                problems.append("Google 일정을 읽다가 문제가 생겼어요.")
        elif google is None:
            self.google_calendars = []
        else:
            try:
                data = google.call("list", start=local_midnight(start).isoformat(),
                                   end=local_midnight(end).isoformat())
                self.google_calendars, google_events = parse_google(data)
                events += google_events
            except SyncError as exc:
                problems.append(str(exc))
            except Exception:
                log_error("Google 동기화 오류\n" + traceback.format_exc())
                problems.append("Google 일정을 읽다가 문제가 생겼어요.")

        google_has_holidays = any("#holiday@" in c.url and "south_korea" in c.url for c in self.google_calendars)
        try:
            if self._icloud_ready():
                s_utc = local_midnight(start).astimezone(timezone.utc)
                e_utc = local_midnight(end).astimezone(timezone.utc)
                for i, cal in enumerate(self.calendars):
                    color = cal.color or PALETTE[i % len(PALETTE)]
                    for data in self.client.calendar_query(cal.url, s_utc, e_utc):
                        try:
                            ical = icalendar.Calendar.from_ical(data)
                        except Exception as exc:
                            log_error(f"iCloud 일정 하나를 읽지 못함: {exc}")
                            continue
                        for ev in parse_events(ical, start, end, cal_name=cal.name, color=color, source="iCloud"):
                            ev.cal_key = cal.key
                            events.append(ev)
        except SyncError as exc:
            problems.append(str(exc))
            self.client = None
        except Exception:
            log_error("iCloud 동기화 오류\n" + traceback.format_exc())
            problems.append("iCloud 일정을 읽다가 문제가 생겼어요.")
            self.client = None

        for j, url in enumerate(self.settings.get("ics_urls") or []):
            label, source = ics_label(url)
            try:
                ical = icalendar.Calendar.from_ical(fetch_ics(url, label))
                color = PALETTE[(len(self.calendars) + len(self.google_calendars) + j) % len(PALETTE)]
                for ev in parse_events(ical, start, end, cal_name=calendar_name(ical, label), color=color,
                                       source=source):
                    ev.cal_key = f"ics:{url}"
                    events.append(ev)
            except SyncError as exc:
                problems.append(str(exc))
            except Exception:
                log_error("iCal 캘린더 오류\n" + traceback.format_exc())
                problems.append(f"{label}을(를) 읽다가 문제가 생겼어요.")

        if self.settings.get("show_holidays") and not google_has_holidays:
            try:
                for ev in parse_events(self._holiday_calendar(), start, end, cal_name="대한민국 공휴일",
                                       color="#E03A3E", source="공휴일", holiday=True):
                    ev.cal_key = "holiday"
                    events.append(ev)
            except Exception as exc:
                log_error(f"공휴일 오류: {exc}")
                problems.append("공휴일 정보를 가져오지 못했어요.")
        return FetchResult(dedupe_events(events), problems, self.google_calendars + self.calendars)

    @staticmethod
    def _google_body(payload: dict, old: dict | None = None) -> tuple[dict, str]:
        """Google 일정 내용과 참석자에게 메일을 보낼지(sendUpdates)를 만들어요. old는 고칠 때 원래 일정의 값이에요."""
        if payload["all_day"]:
            when = {"start": {"date": payload["start"].isoformat()}, "end": {"date": payload["end"].isoformat()}}
        else:
            when = {"start": {"dateTime": payload["start"].isoformat()}, "end": {"dateTime": payload["end"].isoformat()}}
        body = {"summary": payload["title"], **when}
        description = payload.get("description", "")
        if "attachments" in payload:  # 첨부 파일 링크를 설명 끝에도 적어 아이폰 캘린더에서도 열 수 있게 해요
            block = attachment_block(payload["attachments"])
            description = split_attachment_block(description) + ("\n\n" + block if block else "")
            if payload["attachments"] or (old or {}).get("attachments"):
                body["attachments"] = [{k: a[k] for k in ("fileUrl", "title", "mimeType", "fileId", "iconLink") if a.get(k)}
                                       for a in payload["attachments"]][:25]
        for key, value in (("location", payload.get("location", "")), ("description", description.strip())):
            if value or old is not None:  # 고칠 때는 지운 내용도 반영해요
                body[key] = value
        had = list((old or {}).get("attendees_raw") or [])
        emails = list(payload.get("attendees") or [])
        guests = [a for a in had if not (a.get("self") or a.get("organizer") or a.get("resource"))]
        if emails or guests:
            keep = [a for a in had if a.get("self") or a.get("organizer") or a.get("resource")]
            by_email = {a["email"].lower(): a for a in had}
            seen = {a["email"].lower() for a in keep}
            listed = []
            for email in emails:
                if email.lower() not in seen:
                    seen.add(email.lower())
                    listed.append(by_email.get(email.lower(), {"email": email}))  # 원래 있던 사람은 응답을 그대로 둬요
            body["attendees"] = keep + listed
        if emails or guests or old is not None:
            body["guestsCanModify"] = bool(payload.get("guests_can_modify"))
        if "color" in payload and (old is None or payload["color"] != old.get("event_color", "")):
            if payload["color"] or old is not None:  # '기본'으로 돌리면 캘린더 색을 따라가요
                body.update(CalendarService._color_fields(payload["color"]))
        return body, ("all" if emails or guests else "none")

    @staticmethod
    def _color_fields(color: str) -> dict:
        """정확한 색은 비공개 속성(widgetColor)에, Google 화면에는 같거나 가장 비슷한 예전 일정 색으로"""
        if color:
            return {"colorId": CLASSIC_ID_BY_HEX.get(color) or nearest_classic_color_id(color),
                    "extendedProperties": {"private": {"widgetColor": color}}}
        return {"colorId": None, "extendedProperties": {"private": {"widgetColor": None}}}

    def recolor_events(self, calendar_id: str, plan: list, progress) -> dict:
        """[(일정 ID, 새 색, 원래 라벨)] 대로 색만 바꿔요."""
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 색을 바꿀 수 있어요.")
        done, failed, streak = 0, [], 0
        for n, (eid, color, old_label) in enumerate(plan, 1):
            try:
                for wait in (2, 5, 10, 20, None):
                    try:
                        api.patch_event(calendar_id, eid, self._color_fields(color))
                        self._apply_label(api, calendar_id, eid, color, old_label)
                        break
                    except RateLimited:
                        if wait is None:
                            raise
                        time.sleep(wait)
                done += 1
                streak = 0
            except SyncError as exc:
                failed.append(str(exc))
                streak += 1
                if streak >= 3:
                    break
            progress(n, len(plan))
            time.sleep(0.05)
        return {"done": done, "failed": failed}

    @staticmethod
    def _apply_label(api, cid: str, eid: str, color: str, old_label: str) -> None:
        """그 캘린더에 같은 색 라벨이 있으면 붙여서 Google 화면에서도 정확한 색으로 보이게 해요."""
        labels = api.calendar_labels(cid)
        target = next((lid for lid, hx in labels.items() if color and hx == color), "")
        if target != old_label and (target or old_label):
            api.patch_event(cid, eid, {"eventLabelId": target}, "none", label_version=True)

    def update_event(self, ref: dict, payload: dict) -> None:
        """Google 일정 고치기. 다른 Google 캘린더로 옮길 수도 있어요."""
        api = self._google_api()
        if api is None or not ref.get("event_id"):
            raise SyncError("Google 계정으로 로그인해야 일정을 고칠 수 있어요.")
        cid, eid = ref["calendar_id"], ref["event_id"]
        self._upload_new_files(payload, payload.pop("progress", None))
        body, send = self._google_body(payload, ref)
        if payload["calendar_id"] != cid:
            if ref.get("recurring"):
                raise SyncError("반복 일정은 다른 캘린더로 옮길 수 없어요. Google 캘린더에서 옮겨 주세요.")
            api.move_event(cid, eid, payload["calendar_id"], send)
            cid = payload["calendar_id"]
        api.patch_event(cid, eid, body, send)
        if "color" in payload and payload["color"] != ref.get("event_color", ""):
            self._apply_label(api, cid, eid, payload["color"],
                              ref.get("label_id", "") if cid == ref["calendar_id"] else "")

    def delete_google_event(self, ref: dict) -> None:
        api = self._google_api()
        if api is None or not ref.get("event_id"):
            raise SyncError("Google 계정으로 로그인해야 일정을 지울 수 있어요.")
        guests = [a for a in ref.get("attendees_raw") or [] if not (a.get("self") or a.get("organizer"))]
        api.delete_event(ref["calendar_id"], ref["event_id"], "all" if guests else "none")

    def _upload_new_files(self, payload: dict, progress=None) -> None:
        files = payload.pop("new_files", None) or []
        if not files:
            return
        api = self._google_api()
        if api is None:
            raise SyncError("파일을 붙이려면 Google 계정으로 로그인해야 해요.")
        folder = api.drive_folder()
        for n, path in enumerate(files, 1):
            if progress:
                progress(n, len(files), os.path.basename(path))
            payload.setdefault("attachments", []).append(api.upload_file(path, folder))

    def upload_attachments(self, paths: list, progress=None) -> list:
        """파일들을 드라이브에 올리고 붙일 정보를 돌려줘요 (할 일 창에서 써요)."""
        api = self._google_api()
        if api is None:
            raise SyncError("파일을 붙이려면 Google 계정으로 로그인해야 해요.")
        folder, out = api.drive_folder(), []
        for n, path in enumerate(paths, 1):
            if progress:
                progress(n, len(paths), os.path.basename(path))
            out.append(api.upload_file(path, folder))
        return out

    def create_calendar(self, name: str) -> dict:
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 캘린더를 만들 수 있어요.")
        return api.create_calendar(name)

    def delete_calendar(self, calendar_id: str) -> None:
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 캘린더를 지울 수 있어요.")
        api.delete_calendar(calendar_id)

    def mirror_todos(self, calendar_id: str, items: list) -> dict:
        """끝내지 않은 날짜 있는 할 일을 캘린더에 일정으로 복사해요. 위젯이 만든 일정만 고치고 지워요."""
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 아이폰 캘린더에 할 일을 보여 줄 수 있어요.")
        today = date.today()
        raw = api.events(calendar_id, local_midnight(today - timedelta(days=120)).astimezone(timezone.utc),
                         local_midnight(today + timedelta(days=550)).astimezone(timezone.utc))
        cal = RemoteCalendar("", calendar_id, "#000000", True, "Google")
        have: dict = {}
        for r in raw:
            ev = google_api_event(r, cal, False)
            if ev and ev.ref.get("todo_id") and not ev.ref.get("recurring"):
                have.setdefault(ev.ref["todo_id"], []).append(ev)
        made = changed = removed = 0
        for item in items:
            evs = have.pop(item["id"], [])
            if not evs:
                api.insert_event(calendar_id, todo_event_body(item, creating=True, note=MIRROR_NOTE))
                made += 1
                continue
            ev = evs[0]
            now = {**todo_remote_state(ev), "end": "" if ev.all_day else f"{ev.end:%H:%M}",
                   "color": ev.ref.get("event_color", "")}
            if now != mirror_expected(item):
                api.patch_event(calendar_id, ev.ref["event_id"], todo_event_body(item, creating=False, note=MIRROR_NOTE))
                changed += 1
            for extra in evs[1:]:
                api.delete_event(calendar_id, extra.ref["event_id"])
                removed += 1
        for evs in have.values():  # 끝냈거나 지운 할 일의 복사본
            for ev in evs:
                api.delete_event(calendar_id, ev.ref["event_id"])
                removed += 1
        return {"made": made, "changed": changed, "removed": removed}

    # ── Google Tasks ──
    def _tasks_api(self):
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 Google Tasks와 맞출 수 있어요.")
        return api

    def tasks_fetch(self, list_id: str) -> dict:
        """모든 목록의 할 일을 받아요. {"default": 기본 목록 ID, "lists": [...], "tasks": [(목록 ID, 할 일)]}"""
        api = self._tasks_api()
        lists = api.task_lists()
        default = api.default_task_list()
        tasks = []
        for tl in lists:
            tasks += [(tl["id"], t) for t in api.tasks_all(tl["id"])]
        return {"default": default, "lists": lists, "tasks": tasks}

    def task_upsert(self, list_id: str, item: dict, parent_tid: str | None) -> dict:
        """할 일 하나를 Tasks에 넣거나 고쳐요. 상위 할 일이 바뀌었으면 옮겨요."""
        api = self._tasks_api()
        tid = item.get("task_id")
        if tid:
            try:
                res = api.task_patch(list_id, tid, task_body(item, creating=False))
            except SyncError as exc:
                if "찾지 못했어요" not in str(exc):
                    raise
            else:
                if (res.get("parent") or None) != (parent_tid or None):
                    res = api.task_move(list_id, tid, parent_tid)
                return res
        return api.task_insert(list_id, task_body(item, creating=True), parent_tid)

    def task_remove(self, list_id: str, task_id: str) -> None:
        self._tasks_api().task_delete(list_id, task_id)

    def add_event(self, payload: dict) -> str:
        if payload["source"] == "Google" and self._google_api() is not None:
            self._upload_new_files(payload, payload.pop("progress", None))
            body, send = self._google_body(payload)
            created = self._google_api().insert_event(payload["calendar_id"], body, send)
            if payload.get("color") and created.get("id"):
                self._apply_label(self._google_api(), payload["calendar_id"], str(created["id"]), payload["color"], "")
            return {"source": "Google", "calendar_id": payload["calendar_id"], "id": str(created.get("id") or ""),
                    "uid": str(created.get("iCalUID") or "")}
        if payload["source"] == "Google":
            google = self._google()
            if google is None:
                raise SyncError("먼저 설정에서 Google을 연결해 주세요.")
            data = google.call("add", calendarId=payload["calendar_id"], title=payload["title"],
                               start=payload["start"].isoformat(), end=payload["end"].isoformat(),
                               allDay=payload["all_day"], location=payload.get("location", ""),
                               description=payload.get("description", ""))
            return {"source": "Google", "calendar_id": payload["calendar_id"], "id": "", "uid": str(data.get("uid", ""))}
        if not self._icloud_ready():
            raise SyncError("먼저 설정에서 iCloud를 연결해 주세요.")
        uid = str(uuid.uuid4()).upper()
        ics = build_event_ics(uid, payload["title"], payload["start"], payload["end"],
                              payload["all_day"], payload.get("location", ""), payload.get("description", ""))
        url = self.client.put_event(payload["calendar_id"], uid, ics)
        return {"source": "iCloud", "url": url, "uid": uid}

    def delete_event(self, ref: dict) -> None:
        if ref.get("source") == "Google":
            api = self._google_api()
            if api is None or not ref.get("id"):
                raise SyncError("예전 연결 방식에서는 넣은 일정을 되돌릴 수 없어요.")
            api.delete_event(ref["calendar_id"], ref["id"])
        elif ref.get("source") == "iCloud" and ref.get("url"):
            if not self._icloud_ready():
                raise SyncError("먼저 설정에서 iCloud를 연결해 주세요.")
            self.client.delete(ref["url"])

    def google_event_ids(self, calendar_id: str, start: date, end: date) -> dict:
        """Google 캘린더의 일정을 {(날짜, 제목): [일정 ID …]} 로 모아요. (옮길 일정을 찾을 때)"""
        api = self._google_api()
        found: dict = {}
        if api is None:
            return found
        s_utc = local_midnight(start).astimezone(timezone.utc)
        e_utc = local_midnight(end).astimezone(timezone.utc)
        cal = RemoteCalendar("", calendar_id, "#000000", True, "Google")
        labels = api.calendar_labels(calendar_id)
        for raw in api.events(calendar_id, s_utc, e_utc):
            ev = google_api_event(raw, cal, False, labels)
            if ev and ev.ref.get("event_id") and not ev.ref.get("recurring"):
                found.setdefault((ev.start if ev.all_day else ev.start.date(), norm_title(ev.title)), []).append(
                    (ev.ref["event_id"], ev.ref.get("event_color", ""), ev.ref.get("label_id", "")))
        return found

    def move_events(self, src_id: str, dest_id: str, event_ids: list, progress) -> dict:
        """Google 일정을 다른 Google 캘린더로 옮겨요. 일정은 그대로이고 캘린더만 바뀌어요."""
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 일정을 옮길 수 있어요.")
        moved, failed, streak = 0, [], 0
        for n, eid in enumerate(event_ids, 1):
            try:
                for wait in (2, 5, 10, 20, None):
                    try:
                        api.move_event(src_id, eid, dest_id)
                        break
                    except RateLimited:
                        if wait is None:
                            raise
                        time.sleep(wait)
                moved += 1
                streak = 0
            except SyncError as exc:
                failed.append(str(exc))
                streak += 1
                if streak >= 3:
                    break
            progress(n, len(event_ids))
            time.sleep(0.05)
        return {"moved": moved, "failed": failed}

    def todo_upsert(self, calendar_id: str, item: dict) -> str:
        """할 일을 Google 일정으로 넣거나 고쳐요. 일정 ID를 돌려줘요."""
        api = self._google_api()
        if api is None:
            raise SyncError("Google 계정으로 로그인해야 할 일을 아이폰 캘린더에 넣을 수 있어요.")
        eid = item.get("event_id")
        if eid:
            try:
                api.patch_event(calendar_id, eid, todo_event_body(item, creating=False))
                return eid
            except SyncError as exc:
                if "찾지 못했어요" not in str(exc):
                    raise
        created = api.insert_event(calendar_id, todo_event_body(item, creating=True))
        return str(created.get("id") or "")

    def todo_delete(self, calendar_id: str, event_id: str) -> None:
        api = self._google_api()
        if api is not None and event_id:
            api.delete_event(calendar_id, event_id)

    def existing_keys(self, source: str, calendar_id: str, start: date, end: date) -> set:
        """그 캘린더에 이미 있는 일정의 (날짜, 제목) 묶음 — 같은 파일을 두 번 넣지 않게"""
        keys: set = set()
        s_utc = local_midnight(start).astimezone(timezone.utc)
        e_utc = local_midnight(end).astimezone(timezone.utc)

        def add(day, title):
            keys.add((day, norm_title(title)))

        if source == "Google" and self._google_api() is not None:
            cal = RemoteCalendar("", calendar_id, "#000000", True, "Google")
            for raw in self._google_api().events(calendar_id, s_utc, e_utc):
                ev = google_api_event(raw, cal, False)
                if ev:
                    add(ev.start if ev.all_day else ev.start.date(), ev.title)
        elif source == "Google" and self._google() is not None:
            data = self._google().call("list", start=local_midnight(start).isoformat(),
                                       end=local_midnight(end).isoformat())
            for item in data.get("events") or []:
                if item.get("cal") == calendar_id:
                    day = (date.fromisoformat(str(item["start"])[:10]) if item.get("allDay")
                           else parse_iso(str(item["start"])).astimezone().date())
                    add(day, str(item.get("title") or ""))
        elif source == "iCloud" and self._icloud_ready():
            for data in self.client.calendar_query(calendar_id, s_utc, e_utc):
                try:
                    ical = icalendar.Calendar.from_ical(data)
                except Exception:
                    continue
                for ev in parse_events(ical, start, end, cal_name="", color="#000000", source=""):
                    add(ev.start if ev.all_day else ev.start.date(), ev.title)
        return keys

    def import_events(self, cal: RemoteCalendar, items: list, progress) -> dict:
        """여러 일정을 차례로 넣어요. 되돌릴 수 있게 넣은 일정 표시를 모아 둬요."""
        refs, failed, streak = [], [], 0
        for n, it in enumerate(items, 1):
            end = it["end"] + timedelta(days=1) if it["all_day"] else it["end"]
            payload = {"source": cal.source, "calendar_id": cal.url, "title": it["title"], "start": it["start"],
                       "end": end, "all_day": it["all_day"], "location": ""}
            if it.get("color") and cal.source == "Google":
                payload["color"] = it["color"]
            try:
                for wait in (2, 5, 10, 20, None):  # 속도 제한에 걸리면 조금씩 더 기다렸다가 다시 넣어요
                    try:
                        refs.append(self.add_event(payload))
                        break
                    except RateLimited:
                        if wait is None:
                            raise
                        time.sleep(wait)
                streak = 0
            except SyncError as exc:
                failed.append((it["title"], str(exc)))
                streak += 1
                if streak >= 3:  # 연속으로 실패하면 연결 문제라서 멈춰요
                    break
            progress(n, len(items))
            time.sleep(0.05)
        return {"refs": refs, "failed": failed}

    @staticmethod
    def test_sources(google_refresh: str, google_url: str, google_token: str, apple_id: str, password: str,
                     urls: list, caldav_url: str) -> tuple[bool, list]:
        ok, lines = True, []
        if google_refresh:
            try:
                cals = GoogleCalendarAPI(google_refresh).calendar_list()
                primary = next((c.get("id", "") for c in cals if c.get("primary")), "")
                lines.append(f"Google 연결됨 — {primary}, 캘린더 {len(cals)}개")
            except SyncError as exc:
                ok = False
                lines.append(str(exc))
        if google_url:
            try:
                data = GoogleScriptClient(google_url, google_token).call("ping")
                lines.append(f"Google 연결됨 — 기본 캘린더 '{data.get('primary', '')}', "
                             f"캘린더 {data.get('calendars', 0)}개")
            except SyncError as exc:
                ok = False
                lines.append(str(exc))
        if apple_id and password:
            try:
                cals = CalDAVClient(apple_id, password, caldav_url or ICLOUD_CALDAV).discover()
                names = ", ".join(c.name for c in cals) or "없음"
                lines.append(f"iCloud 연결됨 — 캘린더 {len(cals)}개 ({names})")
            except SyncError as exc:
                ok = False
                lines.append(str(exc))
        for url in urls:
            label, _ = ics_label(url)
            try:
                ical = icalendar.Calendar.from_ical(fetch_ics(url, label))
                lines.append(f"{label} 연결됨 — {calendar_name(ical, label)}")
            except SyncError as exc:
                ok = False
                lines.append(str(exc))
            except Exception:
                ok = False
                lines.append(f"{label} 내용을 읽지 못했어요.")
        if not lines:
            ok = False
            lines.append("연결할 캘린더를 먼저 입력해 주세요.")
        return ok, lines


class Worker(threading.Thread):
    """네트워크 작업을 차례로 처리하는 스레드. 결과는 화면 스레드가 꺼내 가요."""

    def __init__(self):
        super().__init__(daemon=True)
        self.jobs: queue.Queue = queue.Queue()
        self.results: queue.Queue = queue.Queue()

    def submit(self, fn, *args, callback=None) -> None:
        self.jobs.put((fn, args, callback))

    def run(self) -> None:
        while True:
            fn, args, callback = self.jobs.get()
            try:
                result, error = fn(*args), None
            except Exception as exc:
                if not isinstance(exc, SyncError):
                    log_error("작업 오류\n" + traceback.format_exc())
                result, error = None, exc
            self.results.put((callback, result, error))


# ───────────────────────── 학사일정 파일 가져오기 ─────────────────────────
# 한글(hwp, hwpx), PDF, 엑셀(xlsx), 워드(docx), 텍스트, 캘린더 파일(ics)에서 날짜와 일정을 찾아내요.

IMPORT_TYPES = [("학사일정 파일", "*.hwp *.hwpx *.pdf *.xlsx *.xlsm *.docx *.txt *.csv *.ics"),
                ("모든 파일", "*.*")]


def _xml_local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def hwp_para_text(payload: bytes) -> str:
    """한글 5.0 문단 글자(HWPTAG_PARA_TEXT)를 문자열로 바꿔요. 표 · 그림 같은 조종 문자는 건너뛰어요."""
    count = len(payload) // 2
    chars = struct.unpack_from(f"<{count}H", payload, 0) if count else ()
    out, i = [], 0
    while i < count:
        c = chars[i]
        if 0xD800 <= c < 0xDC00 and i + 1 < count and 0xDC00 <= chars[i + 1] < 0xE000:
            out.append(chr(0x10000 + ((c - 0xD800) << 10) + (chars[i + 1] - 0xDC00)))
            i += 2
        elif c >= 32:
            out.append(chr(c))
            i += 1
        elif c in (10, 13):
            out.append("\n")
            i += 1
        elif c in (30, 31):
            out.append(" ")
            i += 1
        elif c in (0, 24, 25, 26, 27, 28, 29):
            i += 1
        elif c == 9:
            out.append("\t")
            i += 8
        else:
            i += 8  # 인라인 · 확장 조종 문자는 8글자 크기예요
    return "".join(out)


def hwp_section_lines(data: bytes) -> list[str]:
    """본문 구역(레코드 묶음)에서 문단 글자만 뽑아 줄 목록으로 만들어요. 표 칸의 글자도 순서대로 나와요."""
    lines, pos, size_all = [], 0, len(data)
    while pos + 4 <= size_all:
        header = struct.unpack_from("<I", data, pos)[0]
        pos += 4
        tag, size = header & 0x3FF, (header >> 20) & 0xFFF
        if size == 0xFFF:
            if pos + 4 > size_all:
                break
            size = struct.unpack_from("<I", data, pos)[0]
            pos += 4
        payload = data[pos:pos + size]
        pos += size
        if tag == 67:  # HWPTAG_PARA_TEXT
            lines += [part.strip() for part in hwp_para_text(payload).split("\n") if part.strip()]
    return lines


def hwp_lines(path: str) -> tuple[list[str], str]:
    import olefile
    if not olefile.isOleFile(path):
        raise SyncError("한글 파일을 열지 못했어요. 파일이 손상됐거나 hwp 파일이 아닌 것 같아요.")
    with olefile.OleFileIO(path) as ole:
        header = ole.openstream("FileHeader").read() if ole.exists("FileHeader") else b""
        if not header.startswith(b"HWP Document File"):
            raise SyncError("한글 5.0 이상에서 만든 파일만 읽을 수 있어요.")
        flags = struct.unpack_from("<I", header, 36)[0]
        if flags & 0x2:
            raise SyncError("암호가 걸린 한글 파일이에요. 한글에서 암호를 풀고 저장한 뒤 넣어 주세요.")
        sections = sorted((e for e in ole.listdir() if len(e) == 2 and e[0] == "BodyText"
                           and e[1].startswith("Section")), key=lambda e: int(e[1][7:] or 0))
        if flags & 0x4 or not sections:
            # 배포용 문서는 본문이 잠겨 있어서 미리 보기 글자(앞부분)만 읽을 수 있어요
            preview = ole.openstream("PrvText").read().decode("utf-16-le", "ignore") if ole.exists("PrvText") else ""
            lines = [x.strip() for x in re.split(r"[\r\n]+|<|>", preview) if x.strip()]
            return lines, "배포용 한글 문서라서 앞부분만 읽었어요. 한글에서 PDF로 저장해서 넣으면 전부 읽을 수 있어요."
        lines = []
        for entry in sections:
            data = ole.openstream(entry).read()
            if flags & 0x1:
                try:
                    data = zlib.decompress(data, -15)
                except zlib.error as exc:
                    raise SyncError("한글 파일의 본문을 풀지 못했어요.") from exc
            lines += hwp_section_lines(data)
    return lines, ""


def hwpx_lines(path: str) -> list[str]:
    try:
        with zipfile.ZipFile(path) as zf:
            names = sorted((n for n in zf.namelist() if re.fullmatch(r"Contents/section\d+\.xml", n)),
                           key=lambda n: int(re.findall(r"\d+", n)[-1]))
            sections = [zf.read(n) for n in names]
    except zipfile.BadZipFile as exc:
        raise SyncError("hwpx 파일을 열지 못했어요. 파일이 손상된 것 같아요.") from exc
    lines: list[str] = []

    def paragraph(p) -> None:
        parts: list[str] = []

        def walk(node) -> None:
            for child in node:
                name = _xml_local(child.tag)
                if name == "p":
                    paragraph(child)  # 표 칸 안의 문단은 따로 한 줄로
                elif name == "t":
                    parts.append("".join(child.itertext()))
                else:
                    walk(child)

        walk(p)
        text = "".join(parts).strip()
        if text:
            lines.append(text)

    def root_walk(node) -> None:
        for child in node:
            if _xml_local(child.tag) == "p":
                paragraph(child)
            else:
                root_walk(child)

    for data in sections:
        root_walk(ET.fromstring(data))
    return lines


def docx_lines(path: str) -> list[str]:
    try:
        with zipfile.ZipFile(path) as zf:
            root = ET.fromstring(zf.read("word/document.xml"))
    except (zipfile.BadZipFile, KeyError) as exc:
        raise SyncError("워드 파일을 열지 못했어요.") from exc
    lines = []
    for p in root.iter():
        if _xml_local(p.tag) == "p":
            text = "".join(t.text or "" for t in p.iter() if _xml_local(t.tag) == "t").strip()
            if text:
                lines.append(text)
    return lines


def pdf_lines(path: str) -> list[str]:
    from pypdf import PdfReader
    try:
        reader = PdfReader(path)
        if reader.is_encrypted and not reader.decrypt(""):
            raise SyncError("암호가 걸린 PDF예요. 암호를 풀고 저장한 뒤 넣어 주세요.")
        lines = []
        for page in reader.pages:
            lines += [x.strip() for x in (page.extract_text() or "").splitlines() if x.strip()]
    except SyncError:
        raise
    except Exception as exc:
        raise SyncError("PDF 파일을 읽지 못했어요.") from exc
    if not lines:
        raise SyncError("PDF에 글자가 없어요. 스캔한 그림 PDF라면 한글이나 엑셀 원본 파일을 넣어 주세요.")
    return lines


def xlsx_lines(path: str) -> list[str]:
    from openpyxl import load_workbook

    def cell_text(v) -> str:
        if isinstance(v, datetime):
            return f"{v.year}. {v.month}. {v.day}."
        if isinstance(v, date):
            return f"{v.year}. {v.month}. {v.day}."
        if isinstance(v, float) and v.is_integer():
            return str(int(v))
        return str(v).strip()

    try:
        wb = load_workbook(path, read_only=True, data_only=True)
    except Exception as exc:
        raise SyncError("엑셀 파일을 열지 못했어요.") from exc
    lines = []
    try:
        for ws in wb.worksheets:
            for row in ws.iter_rows(values_only=True):
                cells = [cell_text(v) for v in row if v is not None and str(v).strip()]
                if cells:
                    lines.append("  ".join(cells))
    finally:
        wb.close()
    return lines


def text_lines(path: str) -> list[str]:
    raw = open(path, "rb").read()
    for enc in ("utf-8-sig", "cp949"):
        try:
            text = raw.decode(enc)
            break
        except UnicodeDecodeError:
            continue
    else:
        text = raw.decode("latin-1")
    return [x.strip() for x in text.splitlines() if x.strip()]


def read_schedule_file(path: str) -> tuple[list[str], str]:
    """파일에서 글자 줄을 읽어요. (줄 목록, 알림 문구)"""
    ext = os.path.splitext(path)[1].lower()
    if ext == ".hwp":
        return hwp_lines(path)
    if ext == ".hwpx":
        return hwpx_lines(path), ""
    if ext == ".pdf":
        return pdf_lines(path), ""
    if ext in (".xlsx", ".xlsm"):
        return xlsx_lines(path), ""
    if ext == ".docx":
        return docx_lines(path), ""
    if ext in (".txt", ".csv"):
        return text_lines(path), ""
    if ext == ".xls":
        raise SyncError("엑셀 97-2003 파일(.xls)은 읽을 수 없어요. 엑셀에서 .xlsx로 저장한 뒤 넣어 주세요.")
    if ext == ".doc":
        raise SyncError("예전 워드 파일(.doc)은 읽을 수 없어요. 워드에서 .docx로 저장한 뒤 넣어 주세요.")
    raise SyncError("이 파일은 읽을 수 없어요. 한글(hwp, hwpx), PDF, 엑셀(xlsx), 워드(docx), 텍스트 파일을 넣어 주세요.")


# ── 날짜 찾기 ──
_WD = "월화수목금토일"
_DATE_RE = re.compile(
    r"(?<![\d.])"
    r"(?:(?P<y>(?:19|20)\d{2})\s*(?:[./\-]|년)\s*)?"
    r"(?P<m>1[0-2]|0?[1-9])\s*(?P<sep>[./\-]|월)\s*"
    r"(?P<d>3[01]|[12]\d|0?[1-9])(?!\d)\s*(?P<dend>일|\.)?"
    r"(?:\s*\(\s*(?P<wd>[월화수목금토일])\s*\))?")
_RANGE_RE = re.compile(
    r"\s*(?:~|∼|〜|～|–|-|부터)\s*"
    r"(?:(?P<y>(?:19|20)\d{2})\s*(?:[./\-]|년)\s*)?"
    r"(?:(?P<m>1[0-2]|0?[1-9])\s*(?:[./\-]|월)\s*)?"
    r"(?P<d>3[01]|[12]\d|0?[1-9])(?!\d)\s*(?:일|\.)?"
    r"(?:\s*\(\s*(?P<wd>[월화수목금토일])\s*\))?"
    r"(?:\s*까지)?")
_TITLE_END_RE = re.compile(  # '1학기 지필평가 (~4.30)'처럼 제목 안에 적힌 끝나는 날
    r"\(\s*[~∼～]\s*(?:(?P<m>1[0-2]|0?[1-9])\s*[./월]\s*)?(?P<d>3[01]|[12]\d|0?[1-9])\s*(?:일|\.)?"
    r"\s*(?:\(\s*[월화수목금토일]\s*\))?\s*\)")
_MONTH_ONLY_RE = re.compile(r"^(1[0-2]|0?[1-9])\s*월$")
_NUM_ONLY_RE = re.compile(r"^(3[01]|[12]\d|0?[1-9])$")
_WD_ONLY_RE = re.compile(r"^\(?\s*([월화수목금토일])\s*\)?(?:요일)?$")
_DAY_ROW_RE = re.compile(r"^(3[01]|[12]\d|0?[1-9])\s*\(?\s*([월화수목금토일])\s*\)?(?:요일)?(?:\s+(.*))?$")
_MONTH_DAY_ROW_RE = re.compile(
    r"^(1[0-2]|0?[1-9])\s+(3[01]|[12]\d|0?[1-9])\s*\(?\s*([월화수목금토일])\s*\)?(?:요일)?(?:\s+(.*))?$")
_SCHOOL_YEAR_RE = re.compile(r"((?:19|20)\d{2})\s*학년도")
_DAY_EVENT_RE = re.compile(  # '3일(화):개학식', '16일(월)~27일(금):상담주간', '29일(수)~5.1일(금):야영', '6.30일(화)~3일(금):기말고사'
    r"^(?:(?P<m>1[0-2]|0?[1-9])\s*\.\s*)?(?P<d>3[01]|[12]\d|0?[1-9])\s*일\s*\(\s*(?P<wd>[월화수목금토일])\s*\)"
    r"(?:\s*[~∼～]\s*(?:(?P<m2>1[0-2]|0?[1-9])\s*\.\s*)?(?P<d2>3[01]|[12]\d|0?[1-9])\s*일?\s*"
    r"(?:\(\s*(?P<wd2>[월화수목금토일])\s*\))?)?"
    r"\s*[:：]\s*(?P<title>.+)$")
SCHOOL_MONTHS = (3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 2)


def clean_title(text: str) -> str:
    t = re.sub(r"\(\s*[월화수목금토일]\s*\)", " ", text)
    t = re.sub(r"^\s*[월화수목금토일](?:요일)?(?=\s|$)", "", t)
    t = re.sub(r"\s+", " ", t).strip(" \t|·•○●◎◇◆□■▶▷►-–—:;,/*※~∼")
    while t.count("(") > t.count(")") and "(" in t:
        cut = t.rfind("(")
        t = (t[:cut] + t[cut + 1:]).strip(" \t-–—:;,~∼")
    if not re.search(r"[가-힣A-Za-z]", t):
        return ""  # 숫자나 기호만 남았으면 제목이 아니에요
    return t[:80]


def _strong(match) -> bool:
    return bool(match.group("wd") or match.group("y") or match.group("sep") == "월" or match.group("dend"))


def _line_dates(line: str, allow_weak: bool) -> list:
    """한 줄에서 날짜(기간 포함)를 찾아요. [(시작, 끝, 날짜 정보, 끝 날짜 정보)]"""
    found = []
    for m in _DATE_RE.finditer(line):
        if found and m.start() < found[-1][1]:
            continue  # 앞 날짜의 기간 부분과 겹치면 건너뛰어요
        if line[:m.start()].rstrip().endswith(("~", "∼", "～", "〜")):
            continue  # '(~3.6)'처럼 끝나는 날만 적은 부분이에요
        if m.group("sep") == "월" and m.group("dend") != "일":
            # '월'은 달(3월)도 되고 요일(월요일)도 돼요. '6  월  1학기'처럼 띄어 쓴 '월'은 요일 칸이에요
            after_day = line[m.end("d"):m.end("d") + 1]
            if line[m.end("m"):m.start("sep")] or (after_day and "가" <= after_day <= "힣"):
                continue
        strong = _strong(m)
        if not strong:
            if not allow_weak or m.group("sep") == "-":
                continue
            nxt = line[m.end():m.end() + 1]
            if nxt and (nxt.isdigit() or "가" <= nxt <= "힣" or nxt in "%"):
                continue  # '2-1반', '1.5배', '3.1절'처럼 숫자 뒤에 글자가 바로 붙으면 날짜가 아니에요
        info = {k: m.group(k) for k in ("y", "m", "d", "wd")}
        end, end_info = m.end(), None
        r = _RANGE_RE.match(line, m.end())
        if r and (r.group("m") or r.group("wd") or int(r.group("d")) >= int(m.group("d"))
                  or line[r.start():r.end()].strip().startswith(("~", "∼", "～", "부터"))):
            end_info = {k: r.group(k) for k in ("y", "m", "d", "wd")}
            end = r.end()
        found.append((m.start(), end, info, end_info))
    return found


def _raw(info: dict, end_info: dict | None, title: str, line: str, group: int | None = None) -> dict:
    return {"y": info.get("y"), "m": int(info["m"]) if info.get("m") else None, "d": int(info["d"]),
            "wd": info.get("wd"), "end": end_info, "title": title, "line": line, "group": group}


def scan_schedule(lines: list[str]) -> list[dict]:
    """줄 목록에서 (아직 연도를 정하지 않은) 일정 후보를 찾아요."""
    strong_count = sum(1 for line in lines for m in _DATE_RE.finditer(line) if _strong(m))
    allow_weak = strong_count < 3  # 요일 · '월' · '일'이 붙은 날짜가 충분하면 애매한 숫자는 무시해요
    raws, month_ctx, i, n = [], None, 0, len(lines)
    group, in_group = 0, False  # 달력 모양 문서에서 한 달 치 행사 줄 묶음

    def title_after(j: int) -> tuple[str, int]:
        """j번째 줄부터 날짜가 아닌 첫 줄을 제목으로 써요. (제목, 다음 위치)"""
        while j < n:
            cand = lines[j]
            if (_line_dates(_TITLE_END_RE.sub("", cand), allow_weak) or _MONTH_ONLY_RE.match(cand) or _NUM_ONLY_RE.match(cand)
                    or _WD_ONLY_RE.match(cand) or _DAY_ROW_RE.match(cand)):
                return "", j
            title = clean_title(cand)
            if title:
                return title, j + 1
            j += 1
        return "", j

    while i < n:
        line = lines[i]
        if line.isdigit():
            in_group = False  # 달력 칸의 숫자가 나오면 한 달 치 행사 묶음이 끝나요
        de = _DAY_EVENT_RE.match(line)
        if de and clean_title(de.group("title")):
            if not in_group:
                group, in_group = group + 1, True
            end_info = ({"y": None, "m": de.group("m2"), "d": de.group("d2"), "wd": de.group("wd2")}
                        if de.group("d2") else None)
            raws.append(_raw({"m": de.group("m"), "d": de.group("d"), "wd": de.group("wd")}, end_info,
                             clean_title(de.group("title")), line, group))
            i += 1
            continue
        dates = _line_dates(line, allow_weak)
        if dates:
            i += 1
            for k, (s, e, info, end_info) in enumerate(dates):
                nxt = dates[k + 1][0] if k + 1 < len(dates) else len(line)
                title = clean_title(line[e:nxt])
                if not title and k == 0:
                    title = clean_title(line[:s])  # '여름방학: 7.19 ~ 8.17'처럼 제목이 앞에 오는 경우
                if not title and k == len(dates) - 1:
                    title, i = title_after(i)
                raws.append(_raw(info, end_info, title, line))
                month_ctx = int((end_info or {}).get("m") or info["m"])
            continue
        mo = _MONTH_ONLY_RE.match(line)
        if mo:
            month_ctx = int(mo.group(1))
            i += 1
            continue
        md = _MONTH_DAY_ROW_RE.match(line)
        if md:  # 엑셀 행: '3  2  월  입학식'
            month_ctx = int(md.group(1))
            title = clean_title(md.group(4) or "")
            i += 1
            if not title:
                title, i = title_after(i)
            raws.append(_raw({"m": md.group(1), "d": md.group(2), "wd": md.group(3)}, None, title, line))
            continue
        if month_ctx:
            dr = _DAY_ROW_RE.match(line)
            if dr:  # 표에서 '2 (월) 입학식' 또는 '2 월'
                title = clean_title(dr.group(3) or "")
                i += 1
                if not title:
                    title, i = title_after(i)
                raws.append(_raw({"m": month_ctx, "d": dr.group(1), "wd": dr.group(2)}, None, title, line))
                continue
        num = _NUM_ONLY_RE.match(line)
        if num and i + 1 < n:
            nxt = lines[i + 1]
            if _NUM_ONLY_RE.match(nxt) and int(line) <= 12 and i + 2 < n and _WD_ONLY_RE.match(lines[i + 2]):
                month_ctx = int(line)  # 합쳐진 '월' 칸 다음에 '일' 칸이 오는 표
                i += 1
                continue
            wd = _WD_ONLY_RE.match(nxt)
            if wd and month_ctx:  # 칸마다 한 줄: '2' / '월' / '입학식'
                title, i = title_after(i + 2)
                raws.append(_raw({"m": month_ctx, "d": line, "wd": wd.group(1)}, None, title, line))
                continue
        i += 1
    return raws


def _weekday_ok(school_year: int, m: int, d: int, wd: str) -> bool:
    try:
        return WEEKDAY_SHORT[date(school_year if m >= 3 else school_year + 1, m, d).weekday()] == wd
    except ValueError:
        return False


def assign_months(raws: list[dict], school_year: int) -> list[dict]:
    """달이 적혀 있지 않은 'D일(요일)' 행사 묶음마다, 요일이 가장 잘 맞는 달을 3월부터 순서대로 정해요."""
    out = [dict(r) for r in raws]
    groups = []
    for r in out:
        if r["m"] is None and r.get("group") and r["group"] not in groups:
            groups.append(r["group"])
    pos = 0
    for g in groups:
        members = [r for r in out if r.get("group") == g and r["m"] is None and r["wd"]]
        if not members:
            continue
        scores = []
        for k in range(pos, len(SCHOOL_MONTHS)):
            hit = sum(_weekday_ok(school_year, SCHOOL_MONTHS[k], r["d"], r["wd"]) for r in members)
            scores.append((hit, -k))
            if hit == len(members):
                break  # 처음으로 모두 맞는 달
        hit, neg_k = max(scores)
        if hit == 0:
            continue
        for r in members:
            r["m"] = SCHOOL_MONTHS[-neg_k]
        pos = -neg_k
    return out


def guess_school_year(lines: list[str], raws: list[dict], today: date) -> int:
    """'2026학년도'라고 적혀 있으면 그 해, 아니면 적힌 요일이 가장 잘 맞는 학년도를 골라요."""
    for line in lines[:80]:
        m = _SCHOOL_YEAR_RE.search(line)
        if m:
            return int(m.group(1))
    current = today.year if today.month >= 3 else today.year - 1
    best, best_score = current, -1
    for year in (current - 1, current, current + 1):
        score = sum(_weekday_ok(year, r["m"], r["d"], r["wd"])
                    for r in assign_months(raws, year) if r["wd"] and not r["y"] and r["m"])
        if score > best_score or (score == best_score and year == current):
            best, best_score = year, score
    return best


def resolve_schedule(raws: list[dict], school_year: int) -> list[dict]:
    """학년도를 기준으로 날짜를 정해요. 3~12월은 그 해, 1~2월은 다음 해예요."""
    items, seen = [], set()
    for r in assign_months(raws, school_year):
        title = r["title"]
        if not title or not r["m"]:
            continue
        try:
            y = int(r["y"]) if r["y"] else (school_year if r["m"] >= 3 else school_year + 1)
            start = date(y, r["m"], r["d"])
        except ValueError:
            continue
        end, end_wd = start, None
        tail = _TITLE_END_RE.search(title)
        end_info = r["end"] or ({"m": tail.group("m"), "d": tail.group("d"), "y": None, "wd": None} if tail else None)
        if tail:
            title = clean_title(title[:tail.start()] + title[tail.end():]) or title
        if end_info:
            em = int(end_info["m"]) if end_info.get("m") else start.month
            ed = int(end_info["d"])
            if not end_info.get("m") and ed < start.day:
                em = em % 12 + 1  # '3.30 ~ 2' → 다음 달 2일
            ey = int(end_info["y"]) if end_info.get("y") else (school_year if em >= 3 else school_year + 1)
            try:
                cand = date(ey, em, ed)
                if start <= cand <= start + timedelta(days=200):
                    end, end_wd = cand, end_info.get("wd")
            except ValueError:
                pass
        wd_ok = None
        if r["wd"]:
            wd_ok = WEEKDAY_SHORT[start.weekday()] == r["wd"] and \
                (not end_wd or WEEKDAY_SHORT[end.weekday()] == end_wd)
        key = (start, end, re.sub(r"\W", "", title))
        if key in seen:
            continue
        seen.add(key)
        items.append({"start": start, "end": end, "all_day": True, "title": title, "wd_ok": wd_ok,
                      "line": r["line"]})
    items.sort(key=lambda it: (it["start"], it["title"]))
    return items


def ics_items(path: str, school_year: int) -> list[dict]:
    """캘린더 파일(.ics)의 일정을 그대로 가져와요. 반복 일정은 그 학년도 안에서 펼쳐요."""
    try:
        cal = icalendar.Calendar.from_ical(open(path, "rb").read())
    except Exception as exc:
        raise SyncError("캘린더 파일(.ics)을 읽지 못했어요.") from exc
    start, end = date(school_year, 3, 1), date(school_year + 1, 3, 1)
    items = []
    for ev in parse_events(cal, start, end, cal_name="", color="#000000", source=""):
        if ev.all_day:
            items.append({"start": ev.start, "end": ev.end - timedelta(days=1), "all_day": True, "title": ev.title,
                          "wd_ok": None, "line": ""})
        else:
            items.append({"start": ev.start, "end": ev.end, "all_day": False, "title": ev.title, "wd_ok": None,
                          "line": ""})
    items.sort(key=lambda it: (it["start"] if isinstance(it["start"], date) and not isinstance(it["start"], datetime)
                               else it["start"].date(), it["title"]))
    return items


# ── 방과후 시간표: 달마다 날짜 줄(1, 2, 3 …)이 있고 그 아래 칸에 '특', '전1' 같은 표시가 있는 표 ──
def parse_time_range(text: str) -> tuple[dt_time, dt_time] | None:
    """'18:20~21:00', '8:30-15:10' → (시작, 끝)"""
    m = re.fullmatch(r"\s*(\d{1,2})\s*[:시.]\s*(\d{2})\s*[~∼～\-–]\s*(\d{1,2})\s*[:시.]\s*(\d{2})\s*", text or "")
    if not m:
        return None
    h1, m1, h2, m2 = map(int, m.groups())
    if not (h1 < 24 and h2 < 24 and m1 < 60 and m2 < 60) or (h2, m2) <= (h1, m1):
        return None
    return dt_time(h1, m1), dt_time(h2, m2)


def _cell_int(v) -> int | None:
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)) and float(v).is_integer():
        return int(v)
    if isinstance(v, str) and v.strip().isdigit():
        return int(v.strip())
    return None


def read_code_grid(path: str) -> tuple[list, list]:
    """엑셀에서 (달, 날, 표시, 줄 이름) 목록과, 학년도를 찾을 글자 줄을 돌려줘요."""
    from openpyxl import load_workbook
    try:
        wb = load_workbook(path, read_only=True, data_only=True)
    except Exception as exc:
        raise SyncError("엑셀 파일을 열지 못했어요.") from exc
    entries, texts = [], []
    try:
        for ws in wb.worksheets:
            rows = [list(r) for r in ws.iter_rows(values_only=True)]
            texts += [" ".join(str(v) for v in r if v not in (None, "")) for r in rows[:6]]
            month, r = None, 0
            while r < len(rows):
                daymap = _day_header(rows[r])
                if not daymap:
                    r += 1
                    continue
                for back in range(1, 4):  # 날짜 줄 바로 위쪽의 '3월'
                    found = next((int(m.group(1)) for v in (rows[r - back] if r - back >= 0 else [])
                                  for m in [re.fullmatch(r"\s*(1[0-2]|[1-9])\s*월\s*", str(v or ""))] if m), None)
                    if found:
                        month = found
                        break
                k, group = r + 1, ""
                first_day_col = min(daymap)
                while k < len(rows) and not _day_header(rows[k]):
                    row = rows[k]
                    heads = [str(v).strip() for v in row[:first_day_col] if v not in (None, "")]
                    if len(heads) >= 2 or (heads and not re.fullmatch(r"\d학년", heads[0])):
                        group = heads[0]
                    label = " ".join(dict.fromkeys([group] + heads)).strip()
                    if month and not label.startswith("행사"):
                        for c, d in daymap.items():
                            v = row[c] if c < len(row) else None
                            if v not in (None, ""):
                                entries.append((month, d, re.sub(r"\s+", "", str(v)), label))
                    k += 1
                r = k
    finally:
        wb.close()
    return entries, texts


def _day_header(row: list) -> dict | None:
    """1, 2, 3 … 처럼 날짜가 28개 넘게 이어진 줄이면 {열: 날} 을 돌려줘요."""
    for c0, v in enumerate(row):
        if _cell_int(v) != 1:
            continue
        found, d, c = {}, 1, c0
        while c < len(row) and _cell_int(row[c]) == d:
            found[c], d, c = d, d + 1, c + 1
        if len(found) >= 28:
            return found
    return None


def afterschool_items(entries: list, settings: dict, school_year: int) -> tuple[list, Counter]:
    """표시를 규칙대로 일정으로 바꿔요. (일정 목록, 규칙에 없는 짧은 표시 개수)"""
    rules = {}
    for rule in settings.get("rules") or []:
        code = re.sub(r"\s+", "", str(rule.get("code") or ""))
        normal = parse_time_range(rule.get("time", ""))
        if code and normal and str(rule.get("title") or "").strip():
            rules[code] = (str(rule["title"]).strip(), normal, parse_time_range(rule.get("vacation", "")) or normal,
                           _clean_color(rule.get("color")))
    vacation_months = {int(m) for m in settings.get("vacation_months") or [] if str(m).isdigit()}
    items, unknown = [], Counter()
    for month, day, code, label in entries:
        if code not in rules:
            if len(code) <= 3:
                unknown[code] += 1
            continue
        title, normal, vacation, color = rules[code]
        on_vacation = month in vacation_months
        t1, t2 = vacation if on_vacation else normal
        try:
            d = date(school_year if month >= 3 else school_year + 1, month, day)
        except ValueError:
            continue
        items.append({"start": datetime.combine(d, t1).astimezone(), "end": datetime.combine(d, t2).astimezone(),
                      "all_day": False, "title": title, "wd_ok": None, "line": label, "color": color,
                      "vacation": on_vacation and vacation != normal})
    items.sort(key=lambda it: (it["start"], it["title"]))
    return items, unknown


# ── 급식: 나이스 교육정보 개방 포털 (open.neis.go.kr) ──
NEIS_URL = os.environ.get("CW_NEIS_URL") or "https://open.neis.go.kr/hub"


def neis_rows(endpoint: str, params: dict, key: str = "") -> list:
    """나이스 Open API를 불러 row 목록을 돌려줘요. 인증키가 없으면 결과가 5개까지만 와요."""
    query = {"Type": "json", "pIndex": 1, "pSize": 100 if key else 5, **params}
    if key:
        query["KEY"] = key
    try:
        resp = requests.get(f"{NEIS_URL}/{endpoint}", params=query, timeout=12)
        data = resp.json()
    except requests.RequestException as exc:
        raise network_error("나이스", exc) from exc
    except ValueError as exc:
        raise SyncError("나이스에서 받은 내용을 읽지 못했어요. 잠시 뒤 다시 해 주세요.") from exc
    if endpoint in data:
        return next((part["row"] for part in data[endpoint] if isinstance(part, dict) and "row" in part), [])
    result = data.get("RESULT") or {}
    if result.get("CODE") == "INFO-200":  # 해당하는 데이터가 없어요
        return []
    raise SyncError(f"나이스에서 정보를 받지 못했어요: {result.get('MESSAGE') or result.get('CODE') or resp.status_code}")


def search_schools(name: str, key: str = "") -> list:
    rows = neis_rows("schoolInfo", {"SCHUL_NM": name.strip()}, key)
    return [{"name": str(r.get("SCHUL_NM") or ""), "office_code": str(r.get("ATPT_OFCDC_SC_CODE") or ""),
             "office_name": str(r.get("ATPT_OFCDC_SC_NM") or ""), "school_code": str(r.get("SD_SCHUL_CODE") or ""),
             "address": str(r.get("ORG_RDNMA") or "").strip()}
            for r in rows if r.get("SD_SCHUL_CODE")]


def clean_dish(text: str) -> str:
    """'자장소스(구리고)2.5.6.10.' · '현미밥 (5.6)' 같은 알레르기 번호와 표시를 빼요."""
    s = html.unescape(str(text))
    s = re.sub(r"\(\s*[\d.,\s]+\)", "", s)
    s = re.sub(r"(?:\s*\d{1,2}\.)+\s*\d{0,2}\s*$", "", s)
    s = re.sub(r"[*#&@]+", "", s)
    return re.sub(r"\s+", " ", s).strip()


def fetch_meals(school: dict, day: date, key: str = "") -> list:
    rows = neis_rows("mealServiceDietInfo", {"ATPT_OFCDC_SC_CODE": school["office_code"],
                                             "SD_SCHUL_CODE": school["school_code"],
                                             "MLSV_YMD": day.strftime("%Y%m%d")}, key)
    meals = []
    for r in rows:
        dishes = [clean_dish(x) for x in re.split(r"<br\s*/?>", str(r.get("DDISH_NM") or ""), flags=re.I)]
        meals.append({"name": str(r.get("MMEAL_SC_NM") or "급식"), "code": str(r.get("MMEAL_SC_CODE") or "9"),
                      "dishes": [d for d in dishes if d], "cal": str(r.get("CAL_INFO") or "").strip()})
    meals.sort(key=lambda m: m["code"])
    return meals


def norm_title(text: str) -> str:
    return re.sub(r"[\W_]+", "", text or "").lower()


# ───────────────────────── 화면 ─────────────────────────

try:
    from korean_lunar_calendar import KoreanLunarCalendar
except Exception:
    KoreanLunarCalendar = None

ICONS_NATIVE = {"import": "\uE8B5", "add": "\uE710", "refresh": "\uE72C", "settings": "\uE713", "lock": "\uE72E",
                "unlock": "\uE785", "close": "\uE711", "prev": "\uE76B", "next": "\uE76C", "box": "\uE739",
                "box_done": "\uE73A"}
ICONS_TEXT = {"import": "⇩", "add": "+", "refresh": "↻", "settings": "⚙", "lock": "■", "unlock": "□",
              "close": "✕", "prev": "‹", "next": "›", "box": "□", "box_done": "▣"}

ERROR_RED, LINK_BLUE, HINT_GRAY = "#D93A3E", "#2F6BD8", "#6B7078"

# 색 묶음. tint는 일정 막대에 캘린더 색을 얼마나 옅게 깔지 정해요(1에 가까울수록 옅어요).
THEMES = {
    "paper": {"bg": "#E8E2D6", "panel": "#EEE9DF", "cell": "#F7F3EC", "weekend": "#F3EEE5",
              "line": "#DDD4C4", "text": "#38332D", "muted": "#8C8374", "sun": "#C0473A",
              "sat": "#3B6CB0", "holiday": "#C0473A", "today_cell": "#F1DDD3", "today_ring": "#E07A5F", "accent": "#21385A",
              "accent_text": "#FFFFFF", "now": "#D2453B", "tint": 0.70},
    "night": {"bg": "#0B161C", "panel": "#0F1E26", "cell": "#12303A", "weekend": "#2B221B",
              "line": "#1C3540", "text": "#E3EBED", "muted": "#8DA5AC", "sun": "#FF8A80",
              "sat": "#8DB9FF", "holiday": "#F2C94C", "today_cell": "#1D4552", "today_ring": "#F4B860", "accent": "#F2E4A0",
              "accent_text": "#12303A", "now": "#FF6B6B", "tint": 0.55},
    "light": {"bg": "#ECEEF1", "panel": "#F6F7F9", "cell": "#FFFFFF", "weekend": "#FAFAFB",
              "line": "#E1E4E8", "text": "#1D1F22", "muted": "#858B94", "sun": "#E03A3E",
              "sat": "#2F6BD8", "holiday": "#E03A3E", "today_cell": "#FDEBEB", "today_ring": "#F07167", "accent": "#E03A3E",
              "accent_text": "#FFFFFF", "now": "#E03A3E", "tint": 0.72},
    "dark": {"bg": "#141518", "panel": "#1B1C20", "cell": "#222327", "weekend": "#26272C",
             "line": "#2E3036", "text": "#ECEDEF", "muted": "#8D929B", "sun": "#FF6B6F",
             "sat": "#7AA7FF", "holiday": "#FF6B6F", "today_cell": "#3A2528", "today_ring": "#FF8A80", "accent": "#FF5C61",
             "accent_text": "#FFFFFF", "now": "#FF5C61", "tint": 0.55},
}
THEME_CHOICES = [("paper", "종이"), ("night", "밤바다"), ("light", "밝게"), ("dark", "어둡게"),
                 ("system", "윈도우 설정 따르기")]
COLOR_KEYS = [("bg", "바탕"), ("cell", "날짜 칸"), ("weekend", "주말 칸"), ("today_cell", "오늘 칸"),
              ("today_ring", "오늘 테두리"),
              ("text", "글자"), ("muted", "흐린 글자"), ("sun", "일요일, 공휴일"), ("sat", "토요일"),
              ("accent", "강조"), ("panel", "오른쪽 패널")]
TODO_DONE_CHOICES = [("strike", "취소줄을 긋고 계속 보여 주기"), ("today", "취소줄을 긋고 오늘까지만 보여 주기"),
                     ("hide", "바로 숨기기")]
TODO_KEEP_DAYS = 365  # 끝낸 할 일을 보관하는 날 수
TODO_COLORS = [("green", "#2F9E44", "초록"), ("orange", "#F08C00", "주황"), ("red", "#E03131", "빨강"),
               ("blue", "#1C7ED6", "파랑"), ("purple", "#9E69AF", "보라")]
TODO_COLOR_HEX = {key: hex_ for key, hex_, _ in TODO_COLORS}
SOON_ORANGE = "#E8590C"
TODO_CHIP = "__todo__"  # 위 막대의 '할 일' 단추
TASK_BLUE = "#9E69AF"   # 색을 고르지 않은 할 일 (Google 캘린더의 할 일처럼 보라)
CAL_COLORS = ["#D50000", "#E67C73", "#F4511E", "#F6BF26", "#33B679", "#0B8043",
              "#039BE5", "#3F51B5", "#7986CB", "#8E24AA", "#616161", "#795548"]  # Google 캘린더와 같은 색 12개


def round_rect(cv: tk.Canvas, x0: float, y0: float, x1: float, y1: float, r: float, **kw) -> int:
    """모서리가 둥근 사각형"""
    r = max(0.0, min(r, (x1 - x0) / 2, (y1 - y0) / 2))
    if r < 1:
        return cv.create_rectangle(x0, y0, x1, y1, **kw)
    pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1,
           x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
    return cv.create_polygon(pts, smooth=True, splinesteps=10, **kw)


def round_outline(cv: tk.Canvas, x0: float, y0: float, x1: float, y1: float, r: float, color: str,
                  width: float, **kw) -> None:
    """모서리가 둥근 테두리를 직선과 호로 정확하게 그려요 (곡선 다각형은 굵게 그리면 선이 울퉁불퉁해져요)."""
    r = max(0.0, min(r, (x1 - x0) / 2, (y1 - y0) / 2))
    d = 2 * r
    for ax0, ay0, start in ((x0, y0, 90), (x1 - d, y0, 0), (x1 - d, y1 - d, 270), (x0, y1 - d, 180)):
        cv.create_arc(ax0, ay0, ax0 + d, ay0 + d, start=start, extent=90, style="arc", outline=color, width=width, **kw)
    for lx0, ly0, lx1, ly1 in ((x0 + r, y0, x1 - r, y0), (x1, y0 + r, x1, y1 - r),
                               (x0 + r, y1, x1 - r, y1), (x0, y0 + r, x0, y1 - r)):
        cv.create_line(lx0, ly0, lx1, ly1, fill=color, width=width, **kw)


def parse_attachment_block(text: str) -> list:
    """'[첨부 파일]' 부분에서 [[이름, 링크] …] 를 읽어요."""
    cut = (text or "").find(ATTACH_MARK)
    if cut < 0:
        return []
    out, title = [], None
    for line in text[cut + len(ATTACH_MARK):].splitlines():
        line = line.strip()
        if line.startswith("• "):
            title = line[2:].strip()
        elif line.startswith("http") and title is not None:
            out.append([title, line])
            title = None
    return out


def split_attachment_block(description: str) -> str:
    """설명에서 위젯이 붙인 '[첨부 파일]' 부분을 떼고 사용자가 적은 설명만 돌려줘요."""
    text = description or ""
    cut = text.find(ATTACH_MARK)
    return text[:cut].rstrip() if cut >= 0 else text


def attachment_block(attachments: list) -> str:
    lines = [ATTACH_MARK] + [f"• {a.get('title') or '파일'}\n  {a['fileUrl']}" for a in attachments if a.get("fileUrl")]
    return "\n".join(lines) if len(lines) > 1 else ""


def todo_hex(value) -> str:
    """할 일의 색 값(초록 같은 이름이나 #RRGGBB) → 화면에 쓸 색"""
    return TODO_COLOR_HEX.get(value or "") or _clean_color(value)


def task_body(item: dict, creating: bool) -> dict:
    """위젯 할 일 → Tasks 할 일. 첫 줄은 제목, 나머지는 메모, 시간은 메모 끝 '[시간] 15:30'으로."""
    lines = (item.get("text") or "").splitlines() or [""]
    notes = "\n".join(lines[1:]).strip()
    block = attachment_block(item.get("attachments") or [])
    if block:  # 첨부 파일 링크 (Tasks API에는 첨부 칸이 없어서 메모에 적어요)
        notes = (notes + "\n\n" if notes else "") + block
    marks = []
    if item.get("due") and item.get("time"):
        marks.append(TIME_MARK + str(item["time"]) + (f"-{item['end_time']}" if item.get("end_time") else ""))
    if item.get("deadline"):
        marks.append(DEADLINE_MARK + str(item["deadline"]))
    if marks:
        notes = "\n".join(([notes] if notes else []) + marks)
    body = {"title": lines[0].strip(), "notes": notes, "status": "completed" if item.get("done") else "needsAction"}
    if item.get("due"):
        body["due"] = f"{item['due']}T00:00:00.000Z"
    elif not creating:
        body["due"] = None
    if not item.get("done") and not creating:
        body["completed"] = None
    return body


def split_task_notes(notes: str) -> tuple[str, str, str, str]:
    """Tasks 메모 → (메모, 시작 'HH:MM', 끝 'HH:MM', 기한 'YYYY-MM-DD'). 메모 끝의 '[시간]' · '[기한]' 줄을 읽어요."""
    lines = (notes or "").rstrip().splitlines()
    at = end = deadline = ""
    while lines:
        last = lines[-1].strip()
        if last.startswith(TIME_MARK.strip()):
            parts = last[len(TIME_MARK.strip()):].strip().split("-")
            t1 = parse_time(parts[0].strip())
            t2 = parse_time(parts[1].strip()) if len(parts) > 1 else None
            at = f"{t1.hour:02d}:{t1.minute:02d}" if t1 else ""
            end = f"{t2.hour:02d}:{t2.minute:02d}" if t1 and t2 else ""
        elif last.startswith(DEADLINE_MARK.strip()):
            try:
                deadline = date.fromisoformat(last[len(DEADLINE_MARK.strip()):].strip()).isoformat()
            except ValueError:
                break
        else:
            break
        lines.pop()
    return "\n".join(lines).strip(), at, end, deadline


def item_task_state(item: dict) -> dict:
    lines = (item.get("text") or "").splitlines() or [""]
    timed = bool(item.get("due") and item.get("time"))
    return {"title": lines[0].strip(), "notes": "\n".join(lines[1:]).strip(), "due": str(item.get("due") or ""),
            "time": str(item.get("time") or "") if item.get("due") else "", "done": bool(item.get("done")),
            "parent": str(item.get("parent") or ""), "end": str(item.get("end_time") or "") if timed else "",
            "deadline": str(item.get("deadline") or ""),
            "files": [[a.get("title") or "파일", a["fileUrl"]] for a in item.get("attachments") or [] if a.get("fileUrl")]}


def remote_task_state(task: dict, parent_local: str) -> dict:
    notes, at, end, deadline = split_task_notes(task.get("notes") or "")
    files = parse_attachment_block(notes)
    notes = split_attachment_block(notes)
    due = str(task.get("due") or "")[:10]
    return {"title": str(task.get("title") or "").strip(), "notes": notes, "due": due, "time": at if due else "",
            "done": task.get("status") == "completed", "parent": parent_local or "",
            "end": end if due and at else "", "deadline": deadline, "files": files}


def todo_signature(item: dict) -> dict:
    """할 일을 Google 일정과 비교할 때 쓰는 값"""
    return {"title": (item.get("text") or "").splitlines()[0] if item.get("text") else "",
            "due": str(item.get("due") or ""), "time": str(item.get("time") or "")}


def todo_remote_state(ev: "Event") -> dict:
    day = ev.start if ev.all_day else ev.start.date()
    return {"title": ev.title, "due": day.isoformat(), "time": "" if ev.all_day else f"{ev.start:%H:%M}"}


def todo_event_body(item: dict, creating: bool, note: str | None = None) -> dict:
    """날짜 있는 할 일을 Google 일정 내용으로 바꿔요. 시간이 있으면 30분짜리, 없으면 종일 일정이에요."""
    lines = (item.get("text") or "").splitlines() or [""]
    due = date.fromisoformat(item["due"])
    at = parse_time(str(item.get("time") or ""))
    if at:
        start = datetime.combine(due, at).astimezone()
        until = parse_time(str(item.get("end_time") or ""))
        stop = datetime.combine(due, until).astimezone() if until and until > at else start + timedelta(minutes=30)
        when = {"start": {"dateTime": start.isoformat()}, "end": {"dateTime": stop.isoformat()}}
    else:
        when = {"start": {"date": due.isoformat()}, "end": {"date": (due + timedelta(days=1)).isoformat()}}
    note = note or "캘린더 위젯의 할 일이에요. 여기서 지우면 위젯에서 끝낸 할 일이 돼요."
    atts = [a for a in item.get("attachments") or [] if a.get("fileUrl")]
    block = attachment_block(atts)
    body = {"summary": lines[0], "description": "\n".join(lines[1:] + ([""] if len(lines) > 1 else []) +
                                                          ([block, ""] if block else []) + [note]),
            **when}
    if atts or not creating:
        body["attachments"] = [{k: a[k] for k in ("fileUrl", "title", "mimeType", "fileId", "iconLink") if a.get(k)}
                               for a in atts][:25]
    private = {"widgetTodo": item["id"]}
    color = todo_hex(item.get("color", ""))
    if color:
        body["colorId"] = CLASSIC_ID_BY_HEX.get(color) or nearest_classic_color_id(color)
        private["widgetColor"] = color
    elif not creating:
        body["colorId"] = None
        private["widgetColor"] = None
    body["extendedProperties"] = {"private": private}
    return body


MIRROR_NOTE = ("Google Tasks의 할 일을 아이폰 기본 캘린더에서 보이게 복사한 일정이에요. 여기서 고치거나 지워도 위젯이 "
               "다시 맞춰 놓아요. 끝내거나 고치는 건 위젯이나 Google Tasks 앱에서 해 주세요.")


def mirror_expected(item: dict) -> dict:
    """복사본 일정이 가져야 할 모습 (비교용)"""
    at, until = parse_time(str(item.get("time") or "")), parse_time(str(item.get("end_time") or ""))
    end = ""
    if at:
        stop = until if until and until > at else (datetime.combine(date.today(), at) + timedelta(minutes=30)).time()
        end = f"{stop.hour:02d}:{stop.minute:02d}"
    return {**todo_signature(item), "end": end, "color": todo_hex(item.get("color", ""))}


def todo_due_label(item: dict, today: date) -> tuple[str, str] | None:
    """할 일 날짜를 'D-3 · 11/23(월) 오후 2:00–오후 3:00 · 기한 11/30(월)'처럼 바꿔요. (글자, 느낌: late|soon|normal|done)"""
    def md(d: date) -> str:
        text = f"{d.month}/{d.day}({WEEKDAY_SHORT[d.weekday()]})"
        return f"{d.year}/{text}" if d.year != today.year else text

    def day_of(key: str) -> date | None:
        try:
            return date.fromisoformat(str(item.get(key) or ""))
        except ValueError:
            return None

    due, deadline = day_of("due"), day_of("deadline")
    if not due and not deadline:
        return None
    parts, rank = [], 0  # 0 보통 · 1 곧 · 2 지남
    if due:
        when = md(due)
        at, end = parse_time(str(item.get("time") or "")), parse_time(str(item.get("end_time") or ""))
        if at:
            when += " " + fmt_time(datetime.combine(due, at))
            if end:
                when += "~" + fmt_time(datetime.combine(due, end))
        diff = (due - today).days
        if item.get("done"):
            parts.append(when)
        elif diff == 0:
            parts.append(f"D-day · {when}")
            rank = 2
        elif diff > 0:
            parts.append(f"D-{diff} · {when}")
            rank = 1 if diff <= 3 else 0
        else:
            parts.append(f"{-diff}일 지남 · {when}")
            rank = 2
    if deadline:
        left = (deadline - today).days
        if due:
            parts.append(f"기한 {md(deadline)}" + (" 지남" if left < 0 and not item.get("done") else ""))
        else:
            parts.append(("기한 지남" if left < 0 else "기한 D-day" if left == 0 else f"기한 D-{left}") + f" · {md(deadline)}")
        if not item.get("done"):
            rank = max(rank, 2 if left < 0 else 1 if left <= 1 else 0)
    if item.get("done"):
        return " · ".join(parts), "done"
    return " · ".join(parts), ("normal", "soon", "late")[rank]


NOTIFY_CHOICES = [(0, "끄기"), (5, "5분 전"), (10, "10분 전"), (30, "30분 전"), (60, "1시간 전")]
WEEKDAY_FULL_SUN = [WEEKDAY_FULL[6]] + WEEKDAY_FULL[:6]

_LUNAR_CACHE: dict = {}


def lunar_label(d: date) -> str:
    """음력 날짜를 '10.11'처럼 돌려줘요. 윤달이면 앞에 '윤'을 붙여요."""
    if KoreanLunarCalendar is None:
        return ""
    if d not in _LUNAR_CACHE:
        text = ""
        try:
            cal = KoreanLunarCalendar()
            if cal.setSolarDate(d.year, d.month, d.day):
                text = f"{'윤' if cal.isIntercalation else ''}{cal.lunarMonth}.{cal.lunarDay}"
        except Exception:
            pass
        _LUNAR_CACHE[d] = text
    return _LUNAR_CACHE[d]


def hour_label(h: int) -> str:
    if h == 0:
        return "오전 12시"
    if h == 24:
        return "자정"
    if h == 12:
        return "낮 12시"
    return f"오전 {h}시" if h < 12 else f"오후 {h - 12}시"


def event_when(ev: Event) -> str:
    if ev.all_day:
        last = ev.end - timedelta(days=1)
        return f"{fmt_day(ev.start)} 종일" if last == ev.start else f"{fmt_day(ev.start)} ~ {fmt_day(last)}"
    if ev.start.date() == ev.end.date():
        return f"{fmt_day(ev.start.date())} {fmt_time(ev.start)} ~ {fmt_time(ev.end)}"
    return f"{fmt_day(ev.start.date())} {fmt_time(ev.start)} ~ {fmt_day(ev.end.date())} {fmt_time(ev.end)}"


def is_long(ev: Event) -> bool:
    """하루 넘게 이어지는 시간 일정은 달력에서 막대로 보여 줘요."""
    return not ev.all_day and ev.end - ev.start >= timedelta(hours=24)


def uptime_minutes() -> float:
    try:
        if IS_WINDOWS:
            kernel32.GetTickCount64.restype = ctypes.c_ulonglong
            return kernel32.GetTickCount64() / 60000
        with open("/proc/uptime") as f:
            return float(f.read().split()[0]) / 60
    except Exception:
        return 1e9


def play_alert(root: tk.Misc) -> None:
    if IS_WINDOWS:
        try:
            import winsound
            winsound.MessageBeep(winsound.MB_ICONASTERISK)
            return
        except Exception:
            pass
    root.bell()


def work_area(root: tk.Misc, hwnd: int | None = None) -> tuple[int, int, int, int]:
    """작업 표시줄을 뺀 화면 범위 (왼쪽, 위, 너비, 높이)."""
    if IS_WINDOWS:
        try:
            if hwnd:
                monitor = user32.MonitorFromWindow(hwnd, 2)  # MONITOR_DEFAULTTONEAREST
                info = MONITORINFO()
                info.cbSize = ctypes.sizeof(MONITORINFO)
                if monitor and user32.GetMonitorInfoW(monitor, ctypes.byref(info)):
                    r = info.rcWork
                    return r.left, r.top, r.right - r.left, r.bottom - r.top
            rect = RECT()
            if user32.SystemParametersInfoW(0x0030, 0, ctypes.byref(rect), 0):  # SPI_GETWORKAREA
                return rect.left, rect.top, rect.right - rect.left, rect.bottom - rect.top
        except Exception:
            pass
    return 0, 0, root.winfo_screenwidth(), root.winfo_screenheight()


def layout_columns(items: list) -> list:
    """겹치는 일정을 나란히 놓을 칸을 정해요. items: (시작 분, 끝 분, 일정)"""
    items = sorted(items, key=lambda it: (it[0], -(it[1] - it[0])))
    clusters, current, current_end = [], [], -1.0
    for item in items:
        if current and item[0] >= current_end:
            clusters.append(current)
            current, current_end = [], -1.0
        current.append(item)
        current_end = max(current_end, item[1])
    if current:
        clusters.append(current)
    placed = []
    for cluster in clusters:
        ends, assigned = [], []
        for start, end, ev in cluster:
            for i, last in enumerate(ends):
                if start >= last:
                    ends[i] = end
                    assigned.append((i, start, end, ev))
                    break
            else:
                ends.append(end)
                assigned.append((len(ends) - 1, start, end, ev))
        placed += [(i, len(ends), s, e, ev) for i, s, e, ev in assigned]
    return placed


def pick_family(root: tk.Misc, candidates: list, fallback: str | None) -> str | None:
    available = {f.lower(): f for f in tkfont.families(root)}
    for name in candidates:
        if name.lower() in available:
            return available[name.lower()]
    return fallback


class Tooltip:
    def __init__(self, widget: tk.Widget, text, app: "App"):
        self.widget, self.text, self.app = widget, text, app
        self.tip = None
        self.job = None
        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def _enter(self, _e=None):
        self.job = self.widget.after(550, self._show)

    def _hide(self, _e=None):
        if self.job:
            self.widget.after_cancel(self.job)
            self.job = None
        if self.tip:
            self.tip.destroy()
            self.tip = None

    def _show(self):
        self.job = None
        t = self.app.t
        text = self.text() if callable(self.text) else self.text
        self.tip = tk.Toplevel(self.widget)
        self.tip.overrideredirect(True)
        self.tip.attributes("-topmost", True)
        tk.Label(self.tip, text=text, bg=t["text"], fg=t["cell"], font=self.app.fonts["small"],
                 padx=self.app.px(7), pady=self.app.px(3)).pack()
        self.tip.update_idletasks()
        x = self.widget.winfo_rootx() + self.widget.winfo_width() // 2 - self.tip.winfo_width() // 2
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + self.app.px(4)
        self.tip.geometry(f"+{x}+{y}")


def load_memo() -> str:
    try:
        with open(os.path.join(HOME, "memo.txt"), encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


def save_memo(text: str) -> None:
    path = os.path.join(HOME, "memo.txt")
    try:
        with open(path + ".tmp", "w", encoding="utf-8") as f:
            f.write(text)
        os.replace(path + ".tmp", path)
    except OSError as exc:
        log_error(f"메모 저장 실패: {exc}")


class TodoStore:
    """할 일 목록. %APPDATA%\\CalendarWidget\\todos.json 에 저장해요."""

    def __init__(self):
        self.path = os.path.join(HOME, "todos.json")
        self.items: list = []
        try:
            with open(self.path, encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                self.items = [i for i in data if isinstance(i, dict) and i.get("id") and i.get("text")]
        except FileNotFoundError:
            pass
        except Exception as exc:
            log_error(f"할 일 목록을 읽지 못함: {exc}")
        cutoff = (date.today() - timedelta(days=TODO_KEEP_DAYS)).isoformat()
        self.items = [i for i in self.items if not i.get("done") or (i.get("done_at") or "") >= cutoff]

    def save(self) -> None:
        try:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.items, f, ensure_ascii=False, indent=2)
            os.replace(tmp, self.path)
        except OSError as exc:
            log_error(f"할 일 저장 실패: {exc}")

    def open_items(self) -> list:
        """남은 할 일. 날짜가 있는 것은 가까운 날짜부터, 날짜 없는 것은 적은 순서대로 뒤에"""
        return sorted((i for i in self.items if not i.get("done")),
                      key=lambda i: (str(i.get("due") or "9999"), str(i.get("time") or "99:99")))

    def done_items(self) -> list:
        """끝낸 할 일, 최근에 끝낸 것부터"""
        return sorted((i for i in self.items if i.get("done")), key=lambda i: str(i.get("done_at") or ""),
                      reverse=True)

    def add(self, text: str, due: date | None = None, color: str | None = None,
            at: dt_time | None = None, parent: str | None = None, extra: dict | None = None) -> dict:
        item = {"id": uuid.uuid4().hex, "text": text.strip(), "done": False, "created": date.today().isoformat()}
        if parent:
            item["parent"] = parent
        for key, value in (extra or {}).items():  # end_time · deadline · task_list
            if value and (key != "end_time" or (due and at)):
                item[key] = value
        if due:
            item["due"] = due.isoformat()
            if at:
                item["time"] = f"{at.hour:02d}:{at.minute:02d}"
        if color in TODO_COLOR_HEX or _clean_color(color):
            item["color"] = color if color in TODO_COLOR_HEX else _clean_color(color)
        self.items.append(item)
        self.save()
        return item

    def get(self, item_id: str) -> dict | None:
        return next((i for i in self.items if i["id"] == item_id), None)

    def update(self, item_id: str, text: str, due: date | None, color: str | None,
               at: dt_time | None = None, extra: dict | None = None) -> dict | None:
        item = self.get(item_id)
        if item is not None and extra is not None:
            for key in ("end_time", "deadline"):
                value = extra.get(key)
                if value and (key != "end_time" or (due and at)):
                    item[key] = value
                else:
                    item.pop(key, None)
            if "attachments" in extra:
                if extra["attachments"]:
                    item["attachments"] = list(extra["attachments"])
                else:
                    item.pop("attachments", None)
        if item is not None:
            item["text"] = text.strip()
            if due:
                item["due"] = due.isoformat()
            else:
                item.pop("due", None)
            if due and at:
                item["time"] = f"{at.hour:02d}:{at.minute:02d}"
            else:
                item.pop("time", None)
            if color in TODO_COLOR_HEX or _clean_color(color):
                item["color"] = color if color in TODO_COLOR_HEX else _clean_color(color)
            else:
                item.pop("color", None)
        self.save()
        return item

    def complete(self, item_id: str) -> None:
        for item in self.items:
            if item["id"] == item_id:
                item["done"], item["done_at"] = True, datetime.now().strftime("%Y-%m-%dT%H:%M")
        self.save()

    def reopen(self, item_id: str) -> None:
        for item in self.items:
            if item["id"] == item_id:
                item["done"] = False
                item.pop("done_at", None)
        self.save()

    def clear_done(self) -> int:
        before = len(self.items)
        self.items = [i for i in self.items if not i.get("done")]
        self.save()
        return before - len(self.items)

    def delete(self, item_id: str) -> None:
        self.items = [i for i in self.items if i["id"] != item_id]
        self.save()


class App(tk.Tk):
    def __init__(self, cfg: dict):
        super().__init__(className=APP_NAME)
        self.cfg = cfg
        if not BUILT_IN_GOOGLE_CLIENT and cfg.get("google_client_id"):
            use_google_client(cfg["google_client_id"], unprotect(cfg.get("google_client_secret", "")))
        self.withdraw()
        if is_frozen():
            fix_autostart_path()  # 파이썬으로 쓰다가 설치 파일로 옮겨 와도 자동 실행이 새 프로그램을 켜게
        icon = resource_path("assets", "icon.ico")
        if IS_WINDOWS and os.path.exists(icon):
            try:
                self.iconbitmap(default=icon)  # 설정 창 같은 작은 창들의 아이콘
            except tk.TclError:
                pass
        self.title(APP_TITLE)
        self.overrideredirect(True)
        self.scale = max(1.0, self.winfo_fpixels("1i") / 96.0)
        self._fit_cache: dict = {}
        self._make_fonts()
        if not IS_WINDOWS:
            ttk.Style(self).theme_use("clam")

        self.today = date.today()
        self.anchor = self.today
        self.selected = self.today
        self.follow_today = True
        self.events: list[Event] = []
        self.by_day: dict = {}
        self.bar_events: list[Event] = []
        self.holidays: dict = {}
        self.observances: dict = {}
        self.calendars: list[RemoteCalendar] = []
        self.problems: list[str] = []
        self.loaded: list = []      # 받아 둔 날짜 구간들 [(시작, 끝)]
        self.last_sync: datetime | None = None
        self.syncing = False
        self.loaded_once = False
        self.flash = ""
        self.memo_text = load_memo()
        self.cache_gen = 0          # 연결이 바뀌면 올려서, 그전에 보낸 요청의 결과는 버려요
        self.pending_ranges: list = []
        self.fresh_months: dict = {}  # 달(1일) → 마지막으로 받은 때
        self._cache_save_job = None
        self._render_job = None
        self._save_job = None
        self._refresh_job = None
        self._images: dict = {}
        self._scrolled_for = None
        self._row_geom: list = []
        self._grid_cols = (0, 1.0)
        self._tag_n = 0
        self.event_card = None
        self.notified: set = set()
        self.toasts: list = []
        self.summary_win = None
        self.lock_var = tk.BooleanVar(value=bool(cfg.get("locked")))
        self.todos = TodoStore()

        self.service = CalendarService()
        self.worker = Worker()
        self.worker.start()
        self.layer = DesktopLayer(self) if IS_WINDOWS else None

        self._build()
        self._place_window()
        self.attributes("-alpha", cfg["opacity"] / 100)
        self.report_callback_exception = self._on_tk_error
        # 메시지 창과 메뉴의 주인 노릇을 하는 보이지 않는 작은 창.
        # 위젯 자신이 주인이 되면 메시지 창이 뜰 때 위젯까지 앞으로 끌려 나올 수 있어서 따로 둬요.
        self.host = tk.Toplevel(self)
        self.host.overrideredirect(True)
        try:
            self.host.attributes("-alpha", 0.0)
        except tk.TclError:
            pass
        hx, hy, hw, hh = work_area(self)
        self.host.geometry(f"1x1+{hx + hw // 2}+{hy + hh // 3}")
        self.bind("<Button-3>", self._context_menu)

        self.deiconify()
        self.after(60, self._after_map)
        self.after(120, self._poll_results)
        self.after(30_000, self._minute_tick)
        self.after(4_000, self._notify_tick)
        self._configure_service()
        self._load_cache()  # 지난번에 받아 둔 일정을 먼저 보여 주고, 뒤에서 새로 받아요
        self.ensure_data(force=True)
        self._schedule_refresh()
        self.summary_pending = bool(cfg.get("boot_summary")) and (
            "--summary" in sys.argv or uptime_minutes() < 15)
        if self.summary_pending:
            self.after(30_000, self._summary_fallback)
        if not self.has_sources():
            self.after(700, self.open_welcome)
        if UPDATE_REPO and is_frozen():
            self.after(secrets.randbelow(20 * 60_000) + 120_000, self._update_tick)  # 켠 뒤 2~22분 사이에 처음 확인

    # ── 기본 도구 ──
    def px(self, v: float) -> int:
        return int(round(v * self.scale))

    def _make_fonts(self) -> None:
        if not getattr(self, "_private_fonts_loaded", False):
            load_private_fonts()
            self._private_fonts_loaded = True
        ko = pick_family(self, ["Malgun Gothic", "맑은 고딕", "Apple SD Gothic Neo",
                                "Noto Sans CJK KR", "NanumGothic"], "TkDefaultFont")
        num = pick_family(self, ["Bahnschrift", "Segoe UI", "Noto Sans", "DejaVu Sans"], ko)
        icon = pick_family(self, ["Segoe Fluent Icons", "Segoe MDL2 Assets"], None)
        for named in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont"):
            try:
                tkfont.nametofont(named).configure(family=ko, size=9)
            except tk.TclError:
                pass

        def font(family, size, weight="normal", underline=False, overstrike=False):
            return tkfont.Font(self, family=family, size=size, weight=weight, underline=underline,
                               overstrike=overstrike)

        if self.cfg.get("font_style", "gyeonggi") == "gyeonggi":
            fams = set(tkfont.families(self))

            def has(*names):
                return next((n for n in names if n in fams), None)

            # 윈도우는 굵기마다 이름이 따로('GyeonggiTitle Bold', 한국어 윈도우는 '경기천년제목 Bold'),
            # 다른 곳은 가족 이름('GyeonggiTitle')에 굵기를 정해서 써요.
            bold, bw = has("GyeonggiTitle Bold", "경기천년제목 Bold"), "normal"
            if not bold and has("GyeonggiTitle", "경기천년제목"):
                bold, bw = has("GyeonggiTitle", "경기천년제목"), "bold"
            medium = has("GyeonggiTitle Medium", "경기천년제목 Medium")
            if not medium and bold:
                medium = has("GyeonggiTitle", "경기천년제목") or bold
            body = has("GyeonggiBatang Regular", "경기천년바탕 Regular", "GyeonggiBatang", "경기천년바탕")
            light = has("GyeonggiTitle Light", "경기천년제목 Light")
            if not light:  # 목록에 따로 없어도 이름으로 찾아지면 써요
                for name in ("GyeonggiTitle Light", "경기천년제목 Light"):
                    if "yeonggi" in tkfont.Font(self, family=name, size=9).actual("family"):
                        light = name
                        break
            light = light or medium  # 일정 · 할 일 · 메모 글씨는 굵지 않게
            if bold and body:
                self.fonts = {
                    "title": font(bold, 16, bw), "sub": font(body, 10), "sub_bold": font(bold, 9, bw),
                    "dow": font(bold, 9, bw), "day": font(bold, 11, bw), "day_month": font(bold, 10, bw),
                    "day_small": font(body, 8), "event": font(light, 9), "event_bold": font(light, 9),
                    "event_done": font(light, 9, overstrike=True), "side_title": font(bold, 16, bw),
                    "side_head": font(bold, 13, bw), "small": font(body, 9), "link": font(body, 9, underline=True),
                    "icon": font(icon, 11) if icon else font(ko, 12),
                    "icon_small": font(icon, 10) if icon else font(ko, 10),
                    "big": font(bold, 18, bw), "big_text": font(body, 11), "big_bold": font(bold, 11, bw),
                }
                self.icons = ICONS_NATIVE if icon else ICONS_TEXT
                self._apply_font_scale()
                return
        self.fonts = {
            "title": font(ko, 16, "bold"),
            "sub": font(ko, 10),
            "sub_bold": font(ko, 9, "bold"),
            "dow": font(ko, 9, "bold"),
            "day": font(num, 11, "bold"),
            "day_month": font(ko, 10, "bold"),
            "day_small": font(ko, 8),
            "event": font(ko, 9),
            "event_bold": font(ko, 9, "bold"),
            "event_done": font(ko, 9, overstrike=True),
            "side_title": font(ko, 16, "bold"),
            "side_head": font(ko, 13, "bold"),
            "small": font(ko, 9),
            "link": font(ko, 9, underline=True),
            "icon": font(icon, 11) if icon else font(ko, 12),
            "icon_small": font(icon, 10) if icon else font(ko, 10),
            "big": font(ko, 18, "bold"),
            "big_text": font(ko, 11),
            "big_bold": font(ko, 11, "bold"),
        }
        self.icons = ICONS_NATIVE if icon else ICONS_TEXT
        self._apply_font_scale()

    def _apply_font_scale(self) -> None:
        """일정 글자 크기(80~150%)를 반영해요."""
        size = -max(9, round(14 * self.scale * self.cfg.get("event_scale", 100) / 100))
        self.fonts["event"].configure(size=size)
        self.fonts["event_bold"].configure(size=size)
        self.fonts["event_done"].configure(size=size)
        self._fit_cache.clear()

    def _resolve_theme(self) -> dict:
        name = self.cfg.get("theme", "paper")
        if name == "system":
            name = "dark" if windows_dark_mode() else "light"
        palette = dict(THEMES.get(name, THEMES["paper"]))
        overrides = (self.cfg.get("colors") or {}).get(self.cfg.get("theme", "paper"), {})
        palette.update({k: v for k, v in overrides.items() if k in palette and isinstance(v, str)})
        return palette

    @property
    def t(self) -> dict:
        return self._theme

    def tone(self, d: date) -> str:
        if d.weekday() == 6 or d in self.holidays:
            return "sun"
        return "sat" if d.weekday() == 5 else "text"

    def fit(self, text: str, font: tkfont.Font, width: float) -> str:
        """글자가 칸을 넘치면 뒤를 '…'로 줄여요."""
        width = int(width)
        if width <= 0:
            return ""
        key = (text, str(font), width)
        if key not in self._fit_cache:
            if font.measure(text) <= width:
                result = text
            else:
                lo, hi = 0, len(text)
                while lo < hi:
                    mid = (lo + hi + 1) // 2
                    if font.measure(text[:mid] + "…") <= width:
                        lo = mid
                    else:
                        hi = mid - 1
                result = text[:lo] + "…" if lo else ""
            self._fit_cache[key] = result
        return self._fit_cache[key]

    def circle(self, diameter: int, fill: str, bg: str) -> tk.PhotoImage:
        """가장자리가 매끄러운 원 이미지 (캔버스의 원은 계단 현상이 생겨서 직접 그려요)."""
        diameter = max(2, int(diameter))
        key = (diameter, fill, bg)
        if key not in self._images:
            img = tk.PhotoImage(width=diameter, height=diameter)
            f, b = hex_rgb(fill), hex_rgb(bg)
            r = diameter / 2
            rows = []
            for y in range(diameter):
                row = []
                for x in range(diameter):
                    a = min(1.0, max(0.0, r - ((x + 0.5 - r) ** 2 + (y + 0.5 - r) ** 2) ** 0.5 + 0.5))
                    row.append("#%02x%02x%02x" % tuple(round(bb + (ff - bb) * a) for ff, bb in zip(f, b)))
                rows.append("{" + " ".join(row) + "}")
            img.put(" ".join(rows))
            self._images[key] = img
        return self._images[key]

    def has_google(self) -> bool:
        return bool(self.cfg.get("google_refresh")) or bool(self.cfg["google_url"] and self.cfg["google_token"])

    def has_icloud(self) -> bool:
        return bool(self.cfg["apple_id"] and self.cfg["app_password"])

    def has_sources(self) -> bool:
        return self.has_google() or self.has_icloud() or bool(self.cfg["ics_urls"])

    def writable_calendars(self) -> list[RemoteCalendar]:
        """일정을 넣을 수 있는 캘린더. Google 기본 캘린더가 맨 앞이에요."""
        cals = [c for c in self.calendars if c.writable]
        return sorted(cals, key=lambda c: (c.source != "Google", not c.primary))

    SCHOOL_WORDS = re.compile(r"학교|학사|직장|회사|업무|교무|근무|work|school|office", re.I)

    def todo_cal_keys(self) -> set:
        """할 일을 담는 캘린더 (할 일 맞추기 캘린더, Tasks를 아이폰에 보여 주는 복사본 캘린더)"""
        keys = {self.cfg.get("todo_sync") or ""}
        if self.tasks_mode():
            keys.add(self.cfg.get("todo_mirror") or "")
        keys.discard("")
        return keys

    def event_calendars(self) -> list:
        """일정을 넣을 수 있는 캘린더 (할 일 캘린더는 빼요: 거기 넣은 일정은 할 일이 되니까요)"""
        removed = set(self.cfg.get("removed_cals") or [])
        return [c for c in self.writable_calendars() if c.key not in self.todo_cal_keys() and c.key not in removed]

    def slot_calendar(self, index: int, auto: bool = False) -> RemoteCalendar | None:
        """빠른 선택 버튼(0: 학사일정, 1: 개인)이 가리키는 캘린더. 정하지 않았으면 이름을 보고 짐작해요."""
        cals = self.event_calendars()
        key = "" if auto else self.cfg["quick_slots"][index]["key"]
        if key:
            return next((c for c in cals if c.key == key), None)
        if index == 0:
            return next((c for c in cals if self.SCHOOL_WORDS.search(c.name)), None)
        default = self.cfg.get("default_calendar", "")
        return next((c for c in cals if c.key == default), None) or (cals[0] if cals else None)

    def google_token(self, create: bool = False) -> str:
        token = unprotect(self.cfg.get("google_token", ""))
        if not token and create:
            token = secrets.token_urlsafe(24)
            self.cfg["google_token"] = protect(token)
            self.save()
        return token

    # ── 화면 구성 ──
    def _icon(self, parent, key: str, tip, command, bg: str | None = None) -> tk.Label:
        t = self.t
        bg = bg or t["bg"]
        lbl = tk.Label(parent, text=self.icons[key], font=self.fonts["icon"], bg=bg, fg=t["muted"],
                       cursor="hand2", padx=self.px(5), pady=self.px(2), bd=0)
        lbl.bind("<Enter>", lambda e: lbl.config(fg=t["text"]))
        lbl.bind("<Leave>", lambda e: lbl.config(fg=self._icon_color(key)))
        lbl.bind("<Button-1>", lambda e: command())
        Tooltip(lbl, tip, self)
        return lbl

    def _tray_icon(self, parent) -> tk.Canvas:
        """급식 단추: 김이 나는 밥그릇을 직접 그려요."""
        t, px = self.t, self.px
        size = max(self.fonts["icon"].metrics("linespace"), px(16))
        w, h = size + px(10), size + px(4)
        cv = tk.Canvas(parent, width=w, height=h, bg=t["bg"], highlightthickness=0, bd=0, cursor="hand2")

        def draw(color: str) -> None:
            cv.delete("all")
            sz = size * 0.92
            cx, top = w / 2, (h - sz) / 2
            lw = max(1, px(1.4))
            cv.create_arc(cx - sz * 0.5, top + sz * 0.16, cx + sz * 0.5, top + sz * 1.0, start=180, extent=180,
                          style="chord", outline=color, width=lw)                       # 그릇
            cv.create_line(cx - sz * 0.22, top + sz * 0.95, cx + sz * 0.22, top + sz * 0.95, fill=color, width=lw)
            for dx in (-0.2, 0.0, 0.2):                                                  # 김
                cv.create_line(cx + sz * dx, top + sz * 0.5, cx + sz * dx + sz * 0.1, top + sz * 0.33,
                               cx + sz * dx, top + sz * 0.17, smooth=True, fill=color, width=max(1, px(1.2)))

        draw(t["muted"])
        cv.bind("<Enter>", lambda e: draw(t["text"]))
        cv.bind("<Leave>", lambda e: draw(t["muted"]))
        cv.bind("<Button-1>", lambda e: self.open_meal(cv))
        Tooltip(cv, "급식 메뉴", self)
        return cv

    def _timetable_icon(self, parent) -> tk.Canvas:
        """시간표 단추: 칸이 나뉜 표 모양을 직접 그려요."""
        t, px = self.t, self.px
        size = max(self.fonts["icon"].metrics("linespace"), px(16))
        w, h = size + px(10), size + px(4)
        cv = tk.Canvas(parent, width=w, height=h, bg=t["bg"], highlightthickness=0, bd=0, cursor="hand2")

        def draw(color: str) -> None:
            cv.delete("all")
            lw = max(1, px(1.3))
            sz = size * 0.84
            x0, x1 = (w - sz) / 2, (w + sz) / 2
            y0, y1 = h / 2 - sz * 0.42, h / 2 + sz * 0.42
            round_rect(cv, x0, y0, x1, y1, sz * 0.14, outline=color, fill="", width=lw)
            head = y0 + (y1 - y0) * 0.3
            cv.create_rectangle(x0 + lw, y0 + lw, x1 - lw, head, fill=color, outline="")   # 요일 줄
            for k in (1, 2):                                                               # 칸
                x = x0 + (x1 - x0) * k / 3
                cv.create_line(x, head, x, y1 - lw, fill=color, width=lw)
            mid = head + (y1 - head) / 2
            cv.create_line(x0 + lw, mid, x1 - lw, mid, fill=color, width=lw)

        draw(t["muted"])
        cv.bind("<Enter>", lambda e: draw(t["text"]))
        cv.bind("<Leave>", lambda e: draw(t["muted"]))
        cv.bind("<Button-1>", lambda e: self.open_timetable())
        Tooltip(cv, "시간표", self)
        return cv

    def open_timetable(self) -> None:
        url = (self.cfg.get("timetable_url") or "").strip()
        if not url.lower().startswith(("https://", "http://")):
            if messagebox.askyesno(APP_TITLE, "열 시간표 주소가 없어요. 설정 → 급식 · 시간표에서 주소를 넣을까요?",
                                   parent=self.host):
                self.open_settings("meal")
            return
        webbrowser.open(url)

    def open_meal(self, anchor=None) -> None:
        card = getattr(self, "meal_card", None)
        if card is not None and card.winfo_exists():
            card.destroy()  # 한 번 더 누르면 닫혀요
            return
        if not (self.cfg.get("school") or {}).get("school_code"):
            SchoolDialog(self, on_done=lambda: self.open_meal(anchor))
            return
        day = self.selected if self.selected >= self.today - timedelta(days=60) else self.today
        if day.weekday() >= 5:  # 주말이면 다음 월요일
            day += timedelta(days=7 - day.weekday())
        self.meal_card = MealCard(self, day, anchor)

    def meals_for(self, day: date, callback) -> None:
        school = self.cfg.get("school") or {}
        key = (school.get("school_code"), day.isoformat())
        cache = self.__dict__.setdefault("_meal_cache", {})
        if key in cache and time.time() - cache[key][0] < 3600:
            callback(cache[key][1], None)
            return

        def done(meals, error) -> None:
            if error is None:
                cache[key] = (time.time(), meals)
            callback(meals, error)

        self.worker.submit(fetch_meals, school, day, self.cfg.get("neis_key", "").strip(), callback=done)

    def _icon_color(self, key: str) -> str:
        if key in ("lock", "unlock") and self.cfg.get("locked"):
            return self.t["accent"]
        return self.t["muted"]

    def _text_button(self, parent, text: str, command, bg: str | None = None) -> tk.Label:
        t = self.t
        lbl = tk.Label(parent, text=text, font=self.fonts["sub_bold"], bg=bg or t["bg"], fg=t["muted"],
                       cursor="hand2", padx=self.px(8), pady=self.px(2))
        lbl.bind("<Enter>", lambda e: lbl.config(fg=t["text"]))
        lbl.bind("<Leave>", lambda e: lbl.config(fg=t["muted"]))
        lbl.bind("<Button-1>", lambda e: command())
        return lbl

    def _build(self) -> None:
        self._theme = self._resolve_theme()
        t, f, px = self.t, self.fonts, self.px
        self._images.clear()
        self._fit_cache.clear()
        self._scrolled_for = None
        self.configure(bg=t["bg"])

        # 바깥 테두리: 여기를 끌면 창 크기가 바뀌어요
        self.border = tk.Frame(self, bg=t["bg"])
        self.border.pack(fill="both", expand=True)
        for seq, fn in (("<Motion>", self._edge_motion), ("<ButtonPress-1>", self._edge_press),
                        ("<B1-Motion>", self._edge_drag), ("<ButtonRelease-1>", self._edge_release)):
            self.border.bind(seq, fn)
        self.border.bind("<Leave>", lambda e: self.border.config(cursor=""))
        body = tk.Frame(self.border, bg=t["bg"])
        body.pack(fill="both", expand=True, padx=px(7), pady=px(7))

        # 위쪽 막대
        bar = tk.Frame(body, bg=t["bg"])
        bar.pack(fill="x", pady=(0, px(6)))
        left = tk.Frame(bar, bg=t["bg"])
        left.pack(side="left")
        self._icon(left, "prev", "이전", lambda: self.shift_weeks(-self.page_weeks())).pack(side="left")
        self._icon(left, "next", "다음", lambda: self.shift_weeks(self.page_weeks())).pack(side="left")
        self._text_button(left, "오늘", self.go_today).pack(side="left", padx=(px(2), px(10)))
        self.title_lbl = tk.Label(left, font=f["title"], bg=t["bg"], fg=t["text"], bd=0)
        self.title_lbl.pack(side="left")
        self.title_sub = tk.Label(left, font=f["sub"], bg=t["bg"], fg=t["muted"], bd=0)
        self.title_sub.pack(side="left", padx=(px(10), 0), pady=(px(3), 0))
        right = tk.Frame(bar, bg=t["bg"])
        right.pack(side="right")
        self._icon(right, "add", "일정 추가", self.open_add).pack(side="left")
        self._icon(right, "import", "학사일정 · 방과후 시간표 가져오기", self.open_import).pack(side="left")
        self._tray_icon(right).pack(side="left")
        self._timetable_icon(right).pack(side="left")
        self._icon(right, "refresh", "새로고침", lambda: self.ensure_data(force=True)).pack(side="left")
        self._icon(right, "settings", "설정", self.open_settings).pack(side="left")
        self.lock_btn = self._icon(right, "lock", lambda: "고정 풀기" if self.cfg.get("locked")
                                   else "위치와 크기 고정", self.toggle_lock)
        self.lock_btn.pack(side="left")
        self._icon(right, "close", "닫기", self.confirm_quit).pack(side="left")
        self._update_lock_icon()
        self.status_lbl = tk.Label(bar, font=f["small"], bg=t["bg"], fg=t["muted"], bd=0, anchor="e")
        self.status_lbl.pack(side="right", padx=(0, px(12)))
        self.status_lbl.bind("<Button-1>", self._show_problems)
        self.chips = tk.Frame(bar, bg=t["bg"])  # 캘린더마다 눌러서 보이기 · 숨기기
        self.chips.pack(side="left", fill="x", expand=True, padx=(px(18), px(8)))
        self.chips.bind("<Configure>", lambda e: self.after_idle(self.render_chips))
        self._chips_sig = None
        for w in (bar, left, self.title_lbl, self.title_sub):
            w.bind("<ButtonPress-1>", self._drag_start)
            w.bind("<B1-Motion>", self._drag_move)
            w.bind("<ButtonRelease-1>", lambda e: self._save_geometry_soon())

        # 달력 | 오른쪽 패널
        self.paned = tk.PanedWindow(body, orient="horizontal", bg=t["bg"], bd=0, sashwidth=px(10),
                                    sashrelief="flat", showhandle=False, opaqueresize=False)
        self.paned.pack(fill="both", expand=True)
        self.paned.bind("<Button-1>", lambda e: "break" if self.cfg.get("locked") else None)
        self.paned.bind("<ButtonRelease-1>", lambda e: self.after(80, self._save_side_width))
        self.grid_cv = tk.Canvas(self.paned, bg=t["bg"], highlightthickness=0, bd=0)
        self.paned.add(self.grid_cv, stretch="always", minsize=px(320))
        self.grid_cv.bind("<Configure>", lambda e: self.render_soon(60))
        self.grid_cv.bind("<Button-1>", self._grid_click)
        self.grid_cv.bind("<Double-Button-1>", self._grid_double)
        self.grid_cv.bind("<MouseWheel>", lambda e: self.shift_weeks(-1 if e.delta > 0 else 1))
        self.grid_cv.bind("<Button-4>", lambda e: self.shift_weeks(-1))
        self.grid_cv.bind("<Button-5>", lambda e: self.shift_weeks(1))

        self.side = tk.Frame(self.paned, bg=t["panel"])
        if self.cfg["show_timeline"]:
            self.paned.add(self.side, stretch="never", minsize=px(380), width=self._side_width())
            self._build_side()

    def _side_width(self) -> int:
        saved = int(self.cfg.get("side_width") or 0)
        if saved > 0:
            return saved
        g = self.cfg.get("geometry")
        width = g[2] if isinstance(g, list) and len(g) == 4 else self.winfo_screenwidth()
        return int(min(max(width * 0.36, self.px(480)), self.px(820)))

    def _save_side_width(self) -> None:
        if self.cfg["show_timeline"] and self.side.winfo_ismapped():
            self.cfg["side_width"] = self.side.winfo_width()
            self.save()
            self.render_soon()

    def _build_side(self) -> None:
        t, f, px = self.t, self.fonts, self.px
        side, bg = self.side, t["panel"]
        head = tk.Frame(side, bg=bg)
        head.pack(fill="x", padx=px(10), pady=(px(10), 0))
        self._icon(head, "prev", "전날", lambda: self.select_date(self.selected - timedelta(days=1)),
                   bg=bg).pack(side="left")
        self.side_title = tk.Label(head, font=f["side_title"], bg=bg, fg=t["text"])
        self.side_title.pack(side="left", padx=px(2))
        self._icon(head, "next", "다음날", lambda: self.select_date(self.selected + timedelta(days=1)),
                   bg=bg).pack(side="left")
        self.side_sub = tk.Label(side, font=f["small"], bg=bg, fg=t["muted"], anchor="w")
        self.side_sub.pack(fill="x", padx=px(16), pady=(px(2), px(6)))
        body = tk.Frame(side, bg=bg)
        body.pack(fill="both", expand=True)
        body.columnconfigure(0, weight=1, uniform="col")
        body.columnconfigure(2, weight=1, uniform="col")
        body.rowconfigure(0, weight=2, uniform="row")
        body.rowconfigure(2, weight=1, uniform="row")
        left = tk.Frame(body, bg=bg)  # 왼쪽: 시간표
        left.grid(row=0, column=0, sticky="nsew")
        self.allday_cv = tk.Canvas(left, bg=bg, highlightthickness=0, bd=0, height=1)
        self.allday_cv.pack(fill="x", padx=(px(14), px(8)))
        self.allday_cv.bind("<Configure>", lambda e: self.render_soon(60))
        self.time_cv = tk.Canvas(left, bg=bg, highlightthickness=0, bd=0, height=1)
        self.time_cv.pack(fill="both", expand=True, padx=(px(4), px(6)), pady=(px(6), px(6)))
        self.time_cv.bind("<Configure>", lambda e: self.render_soon(60))
        self.time_cv.bind("<MouseWheel>",
                          lambda e: self.time_cv.yview_scroll(-1 if e.delta > 0 else 1, "units"))
        self.time_cv.bind("<Button-4>", lambda e: self.time_cv.yview_scroll(-1, "units"))
        self.time_cv.bind("<Button-5>", lambda e: self.time_cv.yview_scroll(1, "units"))
        self.time_cv.bind("<Double-Button-1>", self._timeline_double)
        tk.Frame(body, bg=t["line"], width=1).grid(row=0, column=1, sticky="ns", pady=(px(6), px(8)))
        self.todo_box = tk.Frame(body, bg=bg)  # 오른쪽: 할 일
        self.todo_box.grid(row=0, column=2, sticky="nsew", padx=(px(12), px(14)), pady=(0, px(8)))
        tk.Frame(body, bg=t["line"], height=1).grid(row=1, column=0, columnspan=3, sticky="ew", padx=px(14))
        self.memo_box = tk.Frame(body, bg=bg)  # 아래: 두 열을 합친 메모
        self.memo_box.grid(row=2, column=0, columnspan=3, sticky="nsew", padx=px(14), pady=(px(4), px(12)))
        self._build_todo()
        self._build_memo()

    def _build_todo(self) -> None:
        t, f, px = self.t, self.fonts, self.px
        bg = t["panel"]
        head = tk.Frame(self.todo_box, bg=bg)
        head.pack(fill="x", pady=(px(6), 0))
        tk.Label(head, text="할 일", font=f["side_head"], bg=bg, fg=t["text"]).pack(side="left")
        self.todo_count = tk.Label(head, font=f["sub"], bg=bg, fg=t["muted"])
        self.todo_count.pack(side="left", padx=px(6))
        self.todo_sync_lbl = tk.Label(head, font=f["small"], bg=bg, fg=t["muted"], cursor="hand2")
        self.todo_sync_lbl.pack(side="right")
        self.todo_sync_lbl.bind("<Button-1>", lambda e: self._todo_sync_info())
        Tooltip(self.todo_sync_lbl, "아이폰 캘린더와 할 일을 맞추는 상태예요. 누르면 자세히 볼 수 있어요", self)
        add_bg = blend(bg, t["text"], 0.07)
        add = tk.Label(self.todo_box, text="+ 할 일 추가", font=f["event"], bg=add_bg, fg=t["muted"],
                       anchor="w", padx=px(10), pady=px(6), cursor="hand2")
        add.pack(side="bottom", fill="x", pady=(px(6), 0))
        self.todo_cv = tk.Canvas(self.todo_box, bg=bg, highlightthickness=0, bd=0, height=1)
        self.todo_cv.pack(fill="both", expand=True, pady=(px(4), 0))
        self.todo_rows = tk.Frame(self.todo_cv, bg=bg)
        self._todo_win = self.todo_cv.create_window(0, 0, window=self.todo_rows, anchor="nw")
        self.todo_rows.bind("<Configure>", lambda e: self.todo_cv.configure(
            scrollregion=(0, 0, e.width, e.height)))
        self.todo_cv.bind("<Configure>", self._todo_resize)
        for w in (self.todo_cv, self.todo_rows):
            self._wheel_scrolls_todo(w)
        add.bind("<Button-1>", lambda e: self.open_todo())
        add.bind("<Enter>", lambda e: add.config(fg=t["text"]))
        add.bind("<Leave>", lambda e: add.config(fg=t["muted"]))
        self.render_todos()

    # ── 캘린더 보이기 · 색 ──
    def cal_entries(self) -> list:
        """(key, 이름, 색) — 위 막대에 보여 줄 캘린더"""
        colors = self.cfg.get("cal_colors") or {}
        removed = set(self.cfg.get("removed_cals") or [])  # '목록에서 숨기기'를 한 캘린더
        seen, out = set(), []
        for c in sorted(self.calendars, key=lambda c: (c.source != "Google", not c.primary, c.name)):
            if c.key in self.todo_cal_keys() or c.key in removed:
                continue  # 할 일 캘린더는 할 일로 보이고, 목록에서 숨긴 캘린더는 빼요
            if c.key not in seen:
                seen.add(c.key)
                out.append((c.key, c.name, colors.get(c.key, c.color)))
        for ev in self.events:
            if ev.cal_key and ev.cal_key not in seen and ev.cal_key not in self.todo_cal_keys() and ev.cal_key not in removed:
                seen.add(ev.cal_key)
                out.append((ev.cal_key, ev.cal_name or "캘린더", colors.get(ev.cal_key, ev.__dict__.get("_orig_color",
                                                                                                         ev.color))))
        # '할 일': 날짜 있는 할 일을 달력에서 보이거나 숨겨요 (할 일 맞추기를 켠 캘린더의 일정이 여기로 와요)
        order = {k: i for i, k in enumerate(self.cfg.get("cal_order") or [])}
        sync_key = self.cfg.get("todo_sync")
        if TODO_CHIP not in removed and (sync_key or self.tasks_mode()
                                         or any(i.get("due") and not i.get("done") for i in self.todos.items)):
            name = "할 일"
            if not sync_key and any(self._chip_name(n) == "할 일" for _k, n, _c in out):
                name = "위젯 할 일"  # 같은 이름의 캘린더가 따로 보일 때는 구분해요
            out.append((TODO_CHIP, name, TASK_BLUE))  # 할 일 단추는 어느 방식이든 할 일 색(보라)
        if order:  # 사용자가 정한 순서 (새로 생긴 캘린더는 뒤에)
            out = [e for _, e in sorted(enumerate(out), key=lambda p: (order.get(p[1][0], len(order) + p[0]), p[0]))]
        return out

    @staticmethod
    def _chip_name(name: str) -> str:
        return name.split("@")[0] if "@" in name else name

    def render_chips(self) -> None:
        if not hasattr(self, "chips") or not self.chips.winfo_exists():
            return
        t, px = self.t, self.px
        entries = self.cal_entries()
        hidden = set(self.cfg.get("hidden_cals") or [])
        width = self.chips.winfo_width()
        sig = (tuple(entries), tuple(sorted(hidden)), width, self._theme)
        if sig == self._chips_sig:
            return
        self._chips_sig = sig
        for w in self.chips.winfo_children():
            w.destroy()
        self._chip_widgets = []
        if not entries:
            return
        used, overflow = 0, []
        for key, name, color in entries:
            chip = self._make_chip(key, self._chip_name(name), color, key not in hidden, name)
            need = chip.winfo_reqwidth() + px(6)
            if width > 1 and used + need > width - px(56):
                chip.destroy()
                overflow.append((key, name, color))
                continue
            chip.pack(side="left", padx=(0, px(6)))
            used += need
        if overflow:
            more = self._make_chip(None, f"+{len(overflow)}", t["muted"], True, "다른 캘린더")
            more.pack(side="left")
            more.bind("<Button-1>", lambda e, items=overflow: self._overflow_menu(e, items))

    def _make_chip(self, key, label: str, color: str, shown: bool, full_name: str) -> tk.Canvas:
        t, f, px = self.t, self.fonts, self.px
        font = f["sub"]  # 캘린더 단추 글씨 (조금 크게)
        tw = font.measure(label)
        h = font.metrics("linespace") + px(10)
        w = tw + px(30)
        bg = t["bg"]
        cv = tk.Canvas(self.chips, width=w, height=h, bg=bg, highlightthickness=0, bd=0, cursor="hand2")
        fill = blend(color, bg, 0.82) if shown else bg
        edge = blend(color, bg, 0.55) if shown else blend(t["muted"], bg, 0.5)
        round_rect(cv, 1, 1, w - 1, h - 1, h / 2, fill=fill, outline=edge)
        r = px(4)
        cy = h / 2
        if shown:
            cv.create_oval(px(10) - r, cy - r, px(10) + r, cy + r, fill=color, outline="")
        else:
            cv.create_oval(px(10) - r, cy - r, px(10) + r, cy + r, outline=t["muted"], width=max(1, px(1.2)))
        cv.create_text(px(19), cy, text=label, anchor="w", font=font, fill=t["text"] if shown else t["muted"])
        if key is not None:
            self._chip_widgets.append((key, cv))
            cv.bind("<B1-Motion>", self._chip_drag_move)
            cv.bind("<ButtonRelease-1>", self._chip_drag_end)
        if key == TODO_CHIP:
            cv.bind("<Button-1>", lambda e: self._chip_press(e, TODO_CHIP))
            cv.bind("<Button-3>", lambda e: (self._todo_sync_info(), "break")[1])
            Tooltip(cv, f"할 일 (날짜를 넣은 할 일)\n누르면 달력에서 {'숨기고' if shown else '보여 주고'}, "
                        "오른쪽 클릭하면 아이폰 연결 상태를 봐요", self)
        elif key is not None:
            cv.bind("<Button-1>", lambda e, k=key: self._chip_press(e, k))
            cv.bind("<Button-3>", lambda e, k=key, n=full_name, c=color:
                    (self.open_color_popup(k, n, c, e), "break")[1])
            Tooltip(cv, f"{full_name}\n누르면 {'숨기고' if shown else '보여 주고'}, 오른쪽 클릭하면 색을 바꿔요.\n"
                        "Alt를 누른 채 끌면 순서를 바꿔요", self)
        return cv

    def toggle_cal(self, key: str, only: bool = False, show_all: bool = False) -> None:
        if show_all:
            hidden = []
        elif only:
            hidden = [k for k, _n, _c in self.cal_entries() if k != key]
        else:
            hidden = list(self.cfg.get("hidden_cals") or [])
            if key in hidden:
                hidden.remove(key)
            else:
                hidden.append(key)
        self.cfg["hidden_cals"] = hidden
        self.save()
        self._index_events()
        self.render()

    def set_cal_color(self, key: str, color: str | None) -> None:
        colors = dict(self.cfg.get("cal_colors") or {})
        if color:
            colors[key] = color
        else:
            colors.pop(key, None)
        self.cfg["cal_colors"] = colors
        self.save()
        self._index_events()
        self.render()

    def open_color_popup(self, key: str, name: str, color: str, e) -> None:
        old = getattr(self, "_color_popup", None)
        if old is not None and old.winfo_exists():
            old.destroy()
        self._color_popup = ColorPopup(self, key, name, color, e.x_root, e.y_root + self.px(14))

    # ── 캘린더 지우기 · 목록에서 숨기기 ──
    def confirm_delete_calendar(self, cal: RemoteCalendar, parent=None, on_done=None) -> None:
        """'예'를 한 번 누르면 바로 지워요. 그 안의 일정도 함께 지워지고 되돌릴 수 없어요."""
        count = sum(1 for ev in self.events if ev.cal_key == cal.key)
        extra = ("\n할 일을 아이폰에 보여 주던 캘린더라서 '할 일 맞추기'가 꺼져요."
                 if cal.key == self.cfg.get("todo_sync") else "")
        if not messagebox.askyesno(APP_TITLE, f"'{cal.name}' 캘린더를 지울까요?\n그 안의 일정"
                                              f"{f'(불러온 기간에만 {count}개)' if count else ''}도 모두 지워지고 "
                                              f"되돌릴 수 없어요.{extra}", parent=parent or self.host):
            return

        def done(_res, error) -> None:
            if error is not None:
                messagebox.showerror(APP_TITLE, str(error) if isinstance(error, SyncError) else "캘린더를 지우지 못했어요.",
                                     parent=self.host)
                return
            self._calendar_gone(cal.key)
            self.show_flash(f"'{cal.name}' 캘린더를 지웠어요")
            if on_done:
                on_done()

        self.show_flash(f"'{cal.name}' 캘린더를 지우는 중…")
        self.worker.submit(self.service.delete_calendar, cal.url, callback=done)

    def _calendar_gone(self, key: str) -> None:
        cfg = self.cfg
        for name in ("hidden_cals", "cal_order", "removed_cals"):
            cfg[name] = [k for k in cfg.get(name) or [] if k != key]
        (cfg.get("cal_colors") or {}).pop(key, None)
        if cfg.get("last_calendar") == key:
            cfg["last_calendar"] = ""
        if cfg.get("todo_sync") == key:
            cfg["todo_sync"] = ""
            for item in self.todos.items:
                for k in ("event_id", "pushed", "event_cal"):
                    item.pop(k, None)
            self.todos.save()
        self.save()
        self.calendars = [c for c in self.calendars if c.key != key]
        self.events = [ev for ev in self.events if ev.cal_key != key]
        self._index_events()
        self.render()
        self.refresh_all()

    def remove_from_list(self, key: str, name: str) -> None:
        """위젯의 목록에서 숨겨요. 캘린더는 그대로 있고, 다시 보이게 할 수 있어요."""
        removed = [k for k in self.cfg.get("removed_cals") or [] if k != key] + [key]
        self.cfg["removed_cals"] = removed
        self.cfg["hidden_cals"] = [k for k in self.cfg.get("hidden_cals") or [] if k != key]
        self.save()
        self._index_events()
        self.render()
        self.show_flash(f"'{name}'을 목록에서 숨겼어요")

    def restore_to_list(self, key: str) -> None:
        self.cfg["removed_cals"] = [k for k in self.cfg.get("removed_cals") or [] if k != key]
        self.save()
        self._index_events()
        self.render()

    def removed_entries(self) -> list:
        """목록에서 숨긴 캘린더 [(키, 이름)]"""
        names = {c.key: c.name for c in self.calendars}
        names[TODO_CHIP] = "할 일"
        removed = self.cfg.get("removed_cals") or []
        if self.loaded_once and self.calendars:  # 그사이 없어진 캘린더는 목록에서 정리해요
            kept = [k for k in removed if k in names]
            if kept != removed:
                self.cfg["removed_cals"] = removed = kept
                self.save()
        return [(k, names.get(k, "(찾지 못한 캘린더)")) for k in removed]

    @staticmethod
    def _alt_down(e) -> bool:
        """Alt를 누르고 있나요? 위젯 창은 포커스를 받지 않아서 윈도우에서는 키보드 상태를 직접 물어봐요."""
        if IS_WINDOWS:
            try:
                return bool(ctypes.windll.user32.GetAsyncKeyState(0x12) & 0x8000)
            except Exception:
                pass
        return bool(e.state & 0x0008) or bool(e.state & 0x20000)

    def _chip_press(self, e, key: str) -> None:
        if self._alt_down(e):
            self._chip_drag = {"key": key, "moved": False}
            e.widget.config(cursor="fleur")
            return
        self._chip_drag = None
        self.toggle_cal(key)

    def _chip_drop_index(self, x_root: int) -> int:
        widgets = [cv for _k, cv in self._chip_widgets if cv.winfo_exists()]
        for i, cv in enumerate(widgets):
            if x_root < cv.winfo_rootx() + cv.winfo_width() / 2:
                return i
        return len(widgets)

    def _chip_drag_move(self, e) -> None:
        drag = getattr(self, "_chip_drag", None)
        if not drag:
            return
        drag["moved"] = True
        widgets = [cv for _k, cv in self._chip_widgets if cv.winfo_exists()]
        if not widgets:
            return
        idx = self._chip_drop_index(e.x_root)
        if idx < len(widgets):
            x = widgets[idx].winfo_x() - self.px(3)
        else:
            x = widgets[-1].winfo_x() + widgets[-1].winfo_width() + self.px(1)
        marker = getattr(self, "_chip_marker", None)
        if marker is None or not marker.winfo_exists():
            marker = self._chip_marker = tk.Frame(self.chips, bg=self.t["accent"], width=max(2, self.px(2)))
        marker.place(x=max(0, x), y=0, relheight=1.0)
        marker.lift()

    def _chip_drag_end(self, e) -> None:
        drag, self._chip_drag = getattr(self, "_chip_drag", None), None
        marker = getattr(self, "_chip_marker", None)
        if marker is not None and marker.winfo_exists():
            marker.place_forget()
        if e.widget.winfo_exists():
            e.widget.config(cursor="hand2")
        if not drag or not drag["moved"]:
            return
        keys = [k for k, _n, _c in self.cal_entries()]
        shown = [k for k, cv in self._chip_widgets if cv.winfo_exists()]
        idx = self._chip_drop_index(e.x_root)
        keys.remove(drag["key"])
        target = shown[idx] if idx < len(shown) else None
        if target == drag["key"]:  # 제자리
            target = shown[idx + 1] if idx + 1 < len(shown) else None
        if target in keys:
            keys.insert(keys.index(target), drag["key"])
        else:
            last = next((k for k in reversed(shown) if k in keys), None)
            keys.insert(keys.index(last) + 1 if last else len(keys), drag["key"])
        self.cfg["cal_order"] = keys
        self.save()
        self.render_chips()

    def _overflow_menu(self, e, items: list) -> None:
        menu = tk.Menu(self, tearoff=0)
        hidden = set(self.cfg.get("hidden_cals") or [])
        for key, name, _color in items:
            menu.add_checkbutton(label=self._chip_name(name), onvalue=True, offvalue=False,
                                 variable=tk.BooleanVar(self, value=key not in hidden),
                                 command=lambda k=key: self.toggle_cal(k))
        menu.add_separator()
        menu.add_command(label="모든 캘린더 보기", command=lambda: self.toggle_cal("", show_all=True))
        self._popup(menu, e.x_root, e.y_root)

    def _todo_resize(self, e) -> None:
        self.todo_cv.itemconfigure(self._todo_win, width=e.width)
        if abs(e.width - getattr(self, "_todo_width", 0)) > 4:  # 폭이 바뀌면 줄바꿈을 다시 맞춰요
            self._todo_width = e.width
            self.after_idle(self.render_todos)

    def _wheel_scrolls_todo(self, w: tk.Widget) -> None:
        def scroll(e, step=None):
            if self.todo_rows.winfo_height() > self.todo_cv.winfo_height():
                self.todo_cv.yview_scroll(step or (-1 if e.delta > 0 else 1), "units")
            return "break"
        w.bind("<MouseWheel>", scroll)
        w.bind("<Button-4>", lambda e: scroll(e, -1))
        w.bind("<Button-5>", lambda e: scroll(e, 1))

    # ── 메모 ──
    def _build_memo(self) -> None:
        t, f, px = self.t, self.fonts, self.px
        bg = t["panel"]
        head = tk.Frame(self.memo_box, bg=bg)
        head.pack(fill="x", pady=(px(6), 0))
        tk.Label(head, text="메모", font=f["side_head"], bg=bg, fg=t["text"]).pack(side="left")
        edit = tk.Label(head, text="고치기", font=f["link"], bg=bg, fg=t["muted"], cursor="hand2")
        edit.pack(side="right")
        edit.bind("<Button-1>", lambda e: self.open_memo())
        self.memo_view = tk.Text(self.memo_box, bg=blend(bg, t["text"], 0.035), fg=t["text"], font=f["event"],
                                 wrap="word", relief="flat", bd=0, highlightthickness=0, height=2, cursor="hand2",
                                 padx=px(12), pady=px(9), spacing1=px(1), spacing3=px(2))
        self.memo_view.pack(fill="both", expand=True, pady=(px(4), 0))
        self.memo_view.tag_configure("hint", foreground=t["muted"], font=f["small"])
        self.memo_view.bind("<Button-1>", lambda e: (self.open_memo(), "break")[1])
        self.render_memo()

    def render_memo(self) -> None:
        if not hasattr(self, "memo_view") or not self.memo_view.winfo_exists():
            return
        view = self.memo_view
        view.configure(state="normal")
        view.delete("1.0", "end")
        if self.memo_text.strip():
            view.insert("1.0", self.memo_text)
        else:
            view.insert("1.0", "눌러서 메모를 적어 보세요. 수업 준비물, 연락할 곳처럼 날짜와 상관없는 것을 적어 두기 좋아요.",
                        "hint")
        view.configure(state="disabled")

    def open_memo(self) -> None:
        if getattr(self, "_memo_dlg", None) and self._memo_dlg.winfo_exists():
            self._memo_dlg.lift()
            self._memo_dlg.text.focus_set()
            return
        self._memo_dlg = MemoDialog(self)

    def set_memo(self, text: str) -> None:
        if text == self.memo_text:
            return
        self.memo_text = text
        save_memo(text)
        self.render_memo()

    def rebuild(self) -> None:
        self.border.destroy()
        self._build()
        self.attributes("-alpha", self.cfg["opacity"] / 100)
        self.render()

    def _place_window(self) -> None:
        left, top, vw, vh = virtual_screen(self)
        g = self.cfg.get("geometry")
        if isinstance(g, list) and len(g) == 4:
            x, y, w, h = (int(v) for v in g)
            w, h = max(w, self.px(480)), max(h, self.px(360))
            if not (left - w + 80 < x < left + vw - 80 and top - 40 <= y < top + vh - 80):
                g = None
        else:
            g = None
        if g is None:
            x, y, w, h = work_area(self)
        self.geometry(f"{w}x{h}+{x}+{y}")

    def fit_to_screen(self) -> None:
        hwnd = self.layer.hwnd() if self.layer else None
        x, y, w, h = work_area(self, hwnd)
        self.geometry(f"{w}x{h}+{x}+{y}")
        self.cfg["geometry"] = [x, y, w, h]
        self.save()

    def _after_map(self) -> None:
        if self.layer:
            self.layer.install()

    # ── 이동 · 크기 조절 · 고정 ──
    def _drag_start(self, e):
        self._drag = None if self.cfg.get("locked") else (e.x_root - self.winfo_x(), e.y_root - self.winfo_y())

    def _drag_move(self, e):
        if self._drag:
            self.geometry(f"+{e.x_root - self._drag[0]}+{e.y_root - self._drag[1]}")

    def _edge_at(self, e) -> str:
        x, y = e.x_root - self.winfo_rootx(), e.y_root - self.winfo_rooty()
        w, h, m = self.winfo_width(), self.winfo_height(), self.px(10)
        return ("n" if y < m else "s" if y > h - m else "") + ("w" if x < m else "e" if x > w - m else "")

    EDGE_CURSORS_WIN = {"n": "size_ns", "s": "size_ns", "e": "size_we", "w": "size_we",
                        "nw": "size_nw_se", "se": "size_nw_se", "ne": "size_ne_sw", "sw": "size_ne_sw"}
    EDGE_CURSORS_X11 = {"n": "top_side", "s": "bottom_side", "e": "right_side", "w": "left_side",
                        "nw": "top_left_corner", "se": "bottom_right_corner",
                        "ne": "top_right_corner", "sw": "bottom_left_corner"}

    def _edge_motion(self, e):
        if self.cfg.get("locked"):
            self.border.config(cursor="")
            return
        table = self.EDGE_CURSORS_WIN if IS_WINDOWS else self.EDGE_CURSORS_X11
        self.border.config(cursor=table.get(self._edge_at(e), ""))

    def _edge_press(self, e):
        edge = "" if self.cfg.get("locked") else self._edge_at(e)
        self._rz = (edge, e.x_root, e.y_root, self.winfo_x(), self.winfo_y(),
                    self.winfo_width(), self.winfo_height()) if edge else None

    def _edge_drag(self, e):
        if not getattr(self, "_rz", None):
            return
        edge, x0, y0, gx, gy, gw, gh = self._rz
        dx, dy = e.x_root - x0, e.y_root - y0
        min_w, min_h = self.px(480), self.px(360)
        x, y, w, h = gx, gy, gw, gh
        if "e" in edge:
            w = max(min_w, gw + dx)
        if "s" in edge:
            h = max(min_h, gh + dy)
        if "w" in edge:
            w = max(min_w, gw - dx)
            x = gx + gw - w
        if "n" in edge:
            h = max(min_h, gh - dy)
            y = gy + gh - h
        self.geometry(f"{w}x{h}+{x}+{y}")

    def _edge_release(self, e):
        if getattr(self, "_rz", None):
            self._rz = None
            self._save_geometry_soon()

    def toggle_lock(self, value: bool | None = None) -> None:
        self.cfg["locked"] = (not self.cfg.get("locked")) if value is None else bool(value)
        self.lock_var.set(self.cfg["locked"])
        self._update_lock_icon()
        self.save()
        self.show_flash("위치와 크기를 고정했어요" if self.cfg["locked"] else "이제 위치와 크기를 바꿀 수 있어요")

    def _update_lock_icon(self) -> None:
        locked = bool(self.cfg.get("locked"))
        self.lock_btn.config(text=self.icons["lock" if locked else "unlock"], fg=self._icon_color("lock"))

    def _save_geometry_soon(self) -> None:
        if self._save_job:
            self.after_cancel(self._save_job)
        self._save_job = self.after(600, self._save_geometry)

    def _save_geometry(self) -> None:
        self._save_job = None
        self.cfg["geometry"] = [self.winfo_x(), self.winfo_y(), self.winfo_width(), self.winfo_height()]
        self.save()

    def save(self) -> None:
        try:
            save_config(self.cfg)
        except OSError as exc:
            log_error(f"설정 저장 실패: {exc}")

    # ── 데이터 ──
    def _configure_service(self) -> None:
        settings = {
            "google_refresh": unprotect(self.cfg.get("google_refresh", "")),
            "google_can_write": bool(self.cfg.get("google_can_write", True)),
            "google_url": self.cfg["google_url"],
            "google_token": unprotect(self.cfg["google_token"]),
            "apple_id": self.cfg["apple_id"],
            "password": unprotect(self.cfg["app_password"]),
            "ics_urls": list(self.cfg["ics_urls"]),
            "show_holidays": self.cfg["show_holidays"],
            "caldav_url": self.cfg.get("caldav_url") or ICLOUD_CALDAV,
            "holiday_url": self.cfg.get("holiday_url") or KOREAN_HOLIDAYS_ICS,
        }
        self.worker.submit(self.service.configure, settings)

    def grid_first_day(self) -> date:
        first = self.anchor - timedelta(days=(self.anchor.weekday() + 1) % 7)
        if self.cfg.get("start_last_week") and self.cfg["weeks"] >= 3:
            first -= timedelta(days=7)
        return first

    def page_weeks(self) -> int:
        weeks = self.cfg["weeks"]
        return weeks if weeks <= 2 else weeks - 1

    WIDE_BEFORE_DAYS, WIDE_AFTER_DAYS = 92, 366  # 처음에 넉넉히 받아 두는 범위: 앞 3달, 뒤 1년
    GROW_DAYS, EDGE_DAYS = 122, 45                 # 받아 둔 곳의 끝이 45일 안에 보이면 그쪽으로 4달 더

    def _visible_span(self) -> tuple[date, date]:
        g0 = self.grid_first_day()
        return g0, g0 + timedelta(days=7 * self.cfg["weeks"])

    def _windows(self) -> list:
        """늘 받아 둘 곳: 보이는 달력, 고른 날(오른쪽 시간표), 그리고 알림을 위해 오늘 앞뒤. 서로 떨어져 있어도 따로 받아요."""
        a, b = self._visible_span()
        week = timedelta(days=7)
        return [(a - week, b + week), (self.selected - week, self.selected + week + timedelta(days=1)),
                (self.today - week, self.today + week + timedelta(days=1))]

    def ensure_data(self, force: bool = False) -> None:
        """보이는 곳의 일정이 있는지 확인해요. 받아 둔 곳은 바로 보여 주고, 빈 곳만 받아요."""
        if not self.has_sources() and not self.cfg["show_holidays"]:
            return
        a, b = self._visible_span()
        first_time = not self.loaded and not self.pending_ranges
        known = list(self.loaded)
        for ps, pe, _ in self.pending_ranges:
            known = add_interval(known, ps, pe)
        for ws, we in self._windows():  # 1) 보이는 곳과 오늘 앞뒤의 빈 곳부터
            for ms, me in missing_parts(known, month_floor(ws), month_ceil(we)):
                self._request(ms, me)
                known = add_interval(known, month_floor(ms), month_ceil(me))
        if first_time:  # 2) 처음에는 앞 3달 · 뒤 1년을 뒤에서 넉넉히
            self._request(a - timedelta(days=self.WIDE_BEFORE_DAYS), month_floor(a - timedelta(days=7)))
            self._request(month_ceil(b + timedelta(days=7)), b + timedelta(days=self.WIDE_AFTER_DAYS))
        else:  # 3) 받아 둔 곳의 끝이 가까우면 그쪽으로 미리
            edge = timedelta(days=self.EDGE_DAYS)
            for ms, me in missing_parts(known, month_floor(a - edge), month_ceil(b + edge)):
                if me <= a:
                    self._request(me - timedelta(days=self.GROW_DAYS), me)
                elif ms >= b:
                    self._request(ms, ms + timedelta(days=self.GROW_DAYS))
                else:
                    self._request(ms, me)
        for ws, we in self._windows():  # 4) 새로고침 때나 오래된 곳은 다시 받아요
            if force or self._stale(ws, we):
                self._request(ws, we)

    def _stale(self, a: date, b: date) -> bool:
        limit = datetime.now() - timedelta(minutes=self.cfg["refresh_minutes"])
        return any(self.fresh_months.get(m, datetime.min) < limit for m in month_starts(a, b))

    def refresh_all(self) -> None:
        """받아 둔 곳 전체를 다시 받아요 (학사일정을 넣거나 되돌린 뒤)"""
        if not self.loaded:
            self.ensure_data(force=True)
        for s_, e_ in self.loaded:
            self._request(s_, e_)
        self._sync_tasks()

    def reset_cache(self) -> None:
        """연결이 바뀌었을 때: 받아 둔 일정을 버리고 처음부터 받아요"""
        self.cache_gen += 1
        self.loaded = []
        self.fresh_months = {}
        self.events = []
        self._index_events()
        try:
            os.remove(os.path.join(HOME, "events_cache.json"))  # 예전 연결의 일정 사본도 지워요
        except OSError:
            pass

    def _view_waiting(self) -> bool:
        """보이는 곳에 아직 못 받은 날이 있는지 (그때만 '불러오는 중'을 보여요)"""
        a, b = self._visible_span()
        return bool(missing_parts(self.loaded, a, b)) and bool(self.pending_ranges)

    def _request(self, start: date, end: date) -> None:
        start, end = month_floor(start), month_ceil(end)
        if start >= end:
            return
        if any(ps <= start and end <= pe for ps, pe, _ in self.pending_ranges):
            return  # 이미 받는 중이에요
        gen = self.cache_gen
        self.pending_ranges.append((start, end, gen))
        self.syncing = self._view_waiting()

        def job():
            if gen != self.cache_gen:
                return None  # 연결이 바뀌어서 필요 없어진 요청이에요
            return self.service.fetch(start, end)

        self.worker.submit(job, callback=lambda res, err: self._fetched(gen, start, end, res, err))
        self.render_status()

    def _fetched(self, gen, start, end, res: FetchResult | None, err) -> None:
        if (start, end, gen) in self.pending_ranges:
            self.pending_ranges.remove((start, end, gen))
        if gen != self.cache_gen:
            self.syncing = self._view_waiting()
            self.render_status()
            return
        if err is not None:
            self.problems = [str(err) if isinstance(err, SyncError) else "일정을 불러오다가 문제가 생겼어요."]
        elif res is not None:
            def inside(ev) -> bool:
                first, after = event_span(ev)
                return first < end and after > start
            fresh = [ev for ev in res.events if inside(ev)]  # 받은 기간 안의 것만 써요
            keep = [ev for ev in self.events if not inside(ev)]
            self.events = dedupe_events(fresh + keep)  # 같은 일정이면 새로 받은 쪽이 남아요
            if not getattr(self, "_tasks_once", False):  # 처음 받아 올 때 Tasks도
                self._tasks_once = True
                self.after(500, self._sync_tasks)
            try:
                self._sync_todos_from(start, end, res)
            except Exception:
                log_error("할 일 맞추기 오류\n" + traceback.format_exc())
            self.loaded = add_interval(self.loaded, start, end)
            now = datetime.now()
            for m in month_starts(start, end):
                self.fresh_months[m] = now
            self.problems = res.problems
            if res.calendars:
                self.calendars = res.calendars
            if any(LOGIN_EXPIRED in p for p in res.problems):
                self._offer_relogin()
            self.last_sync = now
            self.loaded_once = True
            self._index_events()
            self._save_cache_soon()
        self.syncing = self._view_waiting()
        self.render()
        if self.summary_pending and self.loaded_once and not self.syncing:
            self.summary_pending = False
            self.after(600, self.show_summary)

    # ── 받아 둔 일정을 디스크에 (다음에 켤 때 바로 보이게) ──
    def _cache_signature(self) -> str:
        keys = ("google_email", "google_url", "apple_id", "caldav_url", "ics_urls", "show_holidays", "holiday_url")
        raw = json.dumps([self.cfg.get(k) for k in keys] + [bool(self.cfg.get("google_refresh"))],
                         ensure_ascii=False, sort_keys=True, default=str)
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]

    def _save_cache_soon(self) -> None:
        if self._cache_save_job:
            self.after_cancel(self._cache_save_job)
        self._cache_save_job = self.after(3000, self._save_cache)

    def _save_cache(self) -> None:
        self._cache_save_job = None
        if not self.loaded:
            return
        data = {"v": 2, "sig": self._cache_signature(), "saved": datetime.now().isoformat(timespec="seconds"),
                "loaded": [[a.isoformat(), b.isoformat()] for a, b in self.loaded],
                "events": [event_to_dict(ev) for ev in self.events],
                "calendars": [vars(c).copy() for c in self.calendars]}
        path = os.path.join(HOME, "events_cache.json")
        try:
            with open(path + ".tmp", "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False)
            os.replace(path + ".tmp", path)
        except OSError as exc:
            log_error(f"일정 임시 저장 실패: {exc}")

    def _load_cache(self) -> None:
        try:
            with open(os.path.join(HOME, "events_cache.json"), encoding="utf-8") as f:
                data = json.load(f)
            if data.get("v") != 2 or data.get("sig") != self._cache_signature():
                return  # 연결이 바뀌었으면 쓰지 않아요
            events = [event_from_dict(d) for d in data["events"]]
            calendars = [RemoteCalendar(**c) for c in data.get("calendars", [])]
            loaded: list = []
            for a, b in data["loaded"]:
                loaded = add_interval(loaded, date.fromisoformat(a), date.fromisoformat(b))
        except FileNotFoundError:
            return
        except Exception as exc:
            log_error(f"임시 저장한 일정을 읽지 못함: {exc}")
            return
        self.events, self.calendars, self.loaded = events, calendars, loaded
        self.fresh_months = {}  # 모두 오래된 것으로 보고, 보이는 곳부터 새로 받아요
        self.loaded_once = True
        self._index_events()

    def _index_events(self) -> None:
        by_day, holidays, observances = {}, {}, {}
        hidden = set(self.cfg.get("hidden_cals") or []) | set(self.cfg.get("removed_cals") or [])
        hidden |= self.todo_cal_keys()  # 할 일로 보이는 캘린더는 일정으로 또 그리지 않아요
        colors = self.cfg.get("cal_colors") or {}
        shown = []
        for ev in self.events:
            orig = ev.__dict__.setdefault("_orig_color", ev.color)
            ev.color = (ev.ref or {}).get("event_color") or colors.get(ev.cal_key, orig)  # 일정마다 고른 색이 먼저
            if not (ev.cal_key and ev.cal_key in hidden):
                shown.append(ev)
        for ev in shown:
            for d in ev.days():
                by_day.setdefault(d, []).append(ev)
                if ev.kind == "holiday":
                    holidays.setdefault(d, ev.title)
                elif ev.kind == "observance":
                    observances.setdefault(d, ev.title)
        for evs in by_day.values():
            evs.sort(key=lambda e: (not e.all_day, e.start if not e.all_day
                                    else datetime.min.replace(tzinfo=timezone.utc), e.title))
        self.by_day, self.holidays, self.observances = by_day, holidays, observances
        self.bar_events = [ev for ev in shown if ev.kind == "event" and (ev.all_day or is_long(ev))]

    def _poll_results(self) -> None:
        try:
            while True:
                callback, result, error = self.worker.results.get_nowait()
                if callback:
                    try:
                        callback(result, error)
                    except Exception:
                        log_error("화면 갱신 오류\n" + traceback.format_exc())
        except queue.Empty:
            pass
        self.after(120, self._poll_results)

    def _schedule_refresh(self) -> None:
        if self._refresh_job:
            self.after_cancel(self._refresh_job)
        self._refresh_job = self.after(self.cfg["refresh_minutes"] * 60_000, self._refresh_tick)

    def _refresh_tick(self) -> None:
        self._sync_tasks()  # Google Tasks도 같이 맞춰요
        self.ensure_data(force=True)
        self._schedule_refresh()

    def _minute_tick(self) -> None:
        today = date.today()
        if today != self.today:
            if self.selected == self.today:
                self.selected = today
            if self.follow_today:
                self.anchor = today
            self.today = today
            self.ensure_data(force=True)
        if self.cfg.get("theme") == "system" and self._resolve_theme() != self._theme:
            self.rebuild()  # 윈도우 밝게/어둡게 설정이 바뀌면 따라가요
        self.render()
        self.after(30_000, self._minute_tick)

    # ── 알림 ──
    def _notify_tick(self) -> None:
        try:
            lead = int(self.cfg.get("notify_minutes") or 0)
            if lead and self.loaded_once:
                now = datetime.now().astimezone()
                for d in (self.today, self.today + timedelta(days=1)):
                    for ev in self.by_day.get(d, []):
                        if ev.all_day or ev.kind != "event" or ev.start <= now:
                            continue
                        if ev.start - now <= timedelta(minutes=lead):
                            key = (ev.uid or ev.title, ev.start.isoformat())
                            if key not in self.notified:
                                self.notified.add(key)
                                self.show_toast(ev)
                for item in self.todos.open_items():
                    at = parse_time(str(item.get("time") or ""))
                    if not (at and item.get("due")):
                        continue
                    start = datetime.combine(date.fromisoformat(item["due"]), at).astimezone()
                    if now < start and start - now <= timedelta(minutes=lead):
                        key = ("todo:" + item["id"], start.isoformat())
                        if key not in self.notified:
                            self.notified.add(key)
                            title = (item.get("text") or "").splitlines()[0]
                            self.show_toast(Event(f"할 일: {title}", start, start + timedelta(minutes=30), False, "할 일",
                                                  todo_hex(item.get("color", "")) or self.t["accent"]))
        except Exception:
            log_error("알림 오류\n" + traceback.format_exc())
        self.after(20_000, self._notify_tick)

    def show_toast(self, ev: Event) -> None:
        self.toasts.append(Toast(self, ev))
        self.restack_toasts()
        play_alert(self)

    def _offer_relogin(self) -> None:
        if getattr(self, "_login_card_shown", False) or getattr(self, "_signing_in", False) or not GOOGLE_CLIENT_ID:
            return
        self._login_card_shown = True
        self.toasts.append(LoginCard(self))
        self.restack_toasts()

    def restack_toasts(self) -> None:
        self.toasts = [w for w in self.toasts if w.winfo_exists()]
        x, y, w, h = work_area(self)
        bottom = y + h - self.px(16)
        for toast in reversed(self.toasts):
            toast.update_idletasks()
            tw, th = toast.winfo_reqwidth(), toast.winfo_reqheight()
            bottom -= th
            toast.geometry(f"+{x + w - tw - self.px(16)}+{bottom}")
            bottom -= self.px(10)

    # ── 시작 화면 요약 ──
    def _summary_fallback(self) -> None:
        if self.summary_pending:
            self.summary_pending = False
            self.show_summary()

    def show_summary(self) -> None:
        if self.summary_win is not None and self.summary_win.winfo_exists():
            self.summary_win.refresh()
            self.summary_win.lift()
            return
        self.summary_win = SummaryWindow(self)

    def refresh_summary(self) -> None:
        if self.summary_win is not None and self.summary_win.winfo_exists():
            self.summary_win.refresh()

    # ── 할 일 ──
    def add_todo(self, text: str, due: date | None = None, color: str | None = None,
                 at: dt_time | None = None, parent: str | None = None, extra: dict | None = None) -> None:
        item = self.todos.add(text, due, color, at, parent, extra)
        self.render_todos()
        self.refresh_summary()
        self.render_grid()
        self._push_todo(item)

    def update_todo(self, item_id: str, text: str, due: date | None, color: str | None,
                    at: dt_time | None = None, extra: dict | None = None) -> None:
        item = self.todos.update(item_id, text, due, color, at, extra)
        self.render_todos()
        self.refresh_summary()
        self.render_grid()
        if item is not None:
            self._push_todo(item)

    # ── 할 일 ↔ 아이폰 캘린더 ──
    def todo_sync_problem(self) -> str:
        """할 일을 아이폰 캘린더에 넣지 못하는 까닭 (문제가 없으면 빈 글자)"""
        if self.tasks_mode():
            return self.tasks_problem()
        key = self.cfg.get("todo_sync") or ""
        if not key:
            return ""
        if self.service._google_api() is None:
            return ("Google 계정으로 로그인해야 할 일을 아이폰 캘린더에 넣을 수 있어요. 지금은 연결 코드 방식이라 넣지 못해요. "
                    "설정 → Google에서 'Google 계정으로 로그인'을 해 주세요.")
        cal = next((c for c in self.calendars if c.key == key), None)
        if cal is None:
            if not self.loaded_once:
                return ""
            return ("고른 할 일 캘린더를 찾지 못했어요. Google 캘린더에서 그 캘린더를 지웠거나 '목록에서 숨기기'를 했는지 "
                    "확인하고, 위젯에서 새로고침을 눌러 주세요.")
        if not cal.writable:
            return f"'{cal.name}' 캘린더에는 일정을 넣을 권한이 없어요. 내가 만든 캘린더를 골라 주세요."
        err = getattr(self, "_todo_sync_error", "")
        return f"할 일을 보내다가 문제가 생겼어요: {err}" if err else ""

    def _render_todo_sync_status(self) -> None:
        lbl = getattr(self, "todo_sync_lbl", None)
        if lbl is None or not lbl.winfo_exists():
            return
        t = self.t
        if self.tasks_mode():
            open_items = [i for i in self.todos.items if not i.get("done")]
            sent = sum(1 for i in open_items if i.get("task_id"))
            if self.tasks_problem():
                lbl.config(text="Tasks 연결 안 됨", fg=t["sun"])
            else:
                lbl.config(text=f"Tasks 연결됨 · {sent}개" if sent == len(open_items)
                           else f"Tasks에 보내는 중 {sent}/{len(open_items)}", fg=t["muted"])
            return
        dated = [i for i in self.todos.items if not i.get("done") and i.get("due")]
        if not self.cfg.get("todo_sync"):
            lbl.config(text="아이폰에 안 보여요 · 켜기" if dated else "", fg=t["muted"])
        elif self.todo_sync_problem():
            lbl.config(text="아이폰 연결 안 됨", fg=t["sun"])
        else:
            sent = sum(1 for i in dated if i.get("event_id"))
            lbl.config(text=f"아이폰 연결됨 · {sent}개" if sent == len(dated) else f"아이폰에 보내는 중 {sent}/{len(dated)}",
                       fg=t["muted"])

    def _todo_sync_info(self) -> None:
        if self.tasks_mode():
            problem = self.tasks_problem()
            if problem:
                if messagebox.askyesno(APP_TITLE, problem + "\n\n설정을 열까요?", parent=self.host):
                    self.open_settings("google" if self.service._google_api() is None else "screen")
                return
            count = sum(1 for i in self.todos.items if not i.get("done") and i.get("task_id"))
            last = getattr(self, "_tasks_last", None)
            lists = ", ".join(tl["title"] for tl in getattr(self, "_tasks_lists", []) if tl.get("title")) or "아직 못 읽었어요"
            mcal = self.mirror_cal()
            if mcal is not None:
                lists += f"\n아이폰 기본 캘린더: '{mcal.name}' 캘린더에 날짜 있는 할 일을 복사해 두고 있어요" + (
                    f" (문제: {self._mirror_error})" if getattr(self, "_mirror_error", "") else "")
            if messagebox.askyesno(APP_TITLE, f"할 일 {count}개가 Google Tasks와 맞춰져 있어요. 하위 할 일과 날짜 없는 할 일도 "
                                              f"함께 맞춰져요.\n\n읽는 목록: {lists}\n마지막으로 맞춘 시각: "
                                              f"{fmt_time(last) if last else '아직 없어요'} (1분마다 확인해요)\n\n"
                                              "지금 다시 맞출까요?", parent=self.host):
                self._sync_tasks()
                self.show_flash("Google Tasks와 할 일을 다시 맞추고 있어요")
            return
        if not self.cfg.get("todo_sync"):
            if messagebox.askyesno(APP_TITLE, "날짜 있는 할 일을 아이폰 캘린더에서도 보려면 설정 → 화면 → '할 일 맞추기'에서 "
                                              "할 일 캘린더를 골라요.\n\n설정을 열까요?", parent=self.host):
                self.open_settings("screen")
            return
        problem = self.todo_sync_problem()
        if problem:
            tab = "google" if self.service._google_api() is None else "screen"
            if messagebox.askyesno(APP_TITLE, problem + "\n\n설정을 열까요?", parent=self.host):
                self.open_settings(tab)
            return
        cal = self.todo_sync_cal()
        dated = [i for i in self.todos.items if not i.get("done") and i.get("due")]
        undated = sum(1 for i in self.todos.items if not i.get("done") and not i.get("due"))
        text = (f"날짜 있는 할 일 {sum(1 for i in dated if i.get('event_id'))}개가 '{cal.name}' 캘린더에 들어가 있어요.\n"
                f"아이폰에서 안 보이면 calendar.google.com/calendar/syncselect 에서 '{cal.name}'을 체크하고 저장해 주세요.")
        if undated:
            text += f"\n날짜 없는 할 일 {undated}개는 캘린더에 놓을 수 없어서 위젯에만 있어요."
        if messagebox.askyesno(APP_TITLE, text + "\n\n지금 다시 맞출까요?", parent=self.host):
            self._todo_sync_error = ""
            self._push_all_todos()
            self.refresh_all()
            self.show_flash("아이폰 캘린더와 할 일을 다시 맞추고 있어요")

    def todo_sync_cal(self) -> RemoteCalendar | None:
        key = self.cfg.get("todo_sync") or ""
        if not key or self.service._google_api() is None:
            return None
        return next((c for c in self.calendars if c.key == key and c.source == "Google" and c.writable), None)

    def _push_todo(self, item: dict) -> None:
        """할 일 하나를 Google 캘린더와 맞춰요. 끝냈거나 날짜가 없으면 일정을 지워요."""
        if self.tasks_mode():
            self._mirror_soon()  # 아이폰 캘린더 복사본도 맞춰요
            return self._push_task(item)
        cal = self.todo_sync_cal()
        if cal is None:
            return
        if item.get("done") or not item.get("due") or item.get("_deleted"):
            eid = item.pop("event_id", None)
            item.pop("pushed", None)
            item.pop("event_cal", None)
            if not item.get("_deleted"):
                self.todos.save()
            if eid:
                self.worker.submit(self.service.todo_delete, cal.url, eid,
                                   callback=lambda r, e: e and log_error(f"할 일 일정 지우기 실패: {e}"))
            return
        snapshot = json.loads(json.dumps(item))
        pushing = self.__dict__.setdefault("_todo_pushing", set())
        pushing.add(snapshot["id"])

        def done(eid, err) -> None:
            pushing.discard(snapshot["id"])
            if err is not None:
                log_error(f"할 일을 아이폰 캘린더에 보내지 못함 (다음 새로고침 때 다시 해요): {err}")
                self._todo_sync_error = str(err) if isinstance(err, SyncError) else "연결 문제"
                self._render_todo_sync_status()
                return
            self._todo_sync_error = ""
            live = self.todos.get(snapshot["id"])
            if live is None or live.get("done"):  # 그사이 지웠거나 끝냈어요
                self.worker.submit(self.service.todo_delete, cal.url, eid, callback=lambda r, e: None)
                return
            live["event_id"], live["event_cal"] = eid, cal.key
            live["pushed"] = todo_signature(snapshot)
            self.todos.save()
            self._render_todo_sync_status()

        self.worker.submit(self.service.todo_upsert, cal.url, snapshot, callback=done)

    # ── 할 일 ↔ Google Tasks ──
    def tasks_mode(self) -> bool:
        return bool(self.cfg.get("todo_tasks"))

    def tasks_problem(self) -> str:
        if self.service._google_api() is None:
            return "Google 계정으로 로그인해야 Google Tasks와 맞출 수 있어요. 설정 → Google에서 로그인해 주세요."
        err = getattr(self, "_tasks_error", "")
        return f"Google Tasks와 맞추다가 문제가 생겼어요: {err}" if err else ""

    def _push_task(self, item: dict) -> None:
        if not self.tasks_mode() or self.service._google_api() is None:
            return
        list_id = item.get("task_list") or getattr(self, "_tasks_default", "") or "@default"
        if item.get("_deleted"):
            if item.get("task_id"):
                self.worker.submit(self.service.task_remove, list_id, item["task_id"],
                                   callback=lambda r, e: e and log_error(f"Tasks 할 일 지우기 실패: {e}"))
            return
        parent_tid = None
        if item.get("parent"):
            parent = self.todos.get(item["parent"])
            if parent is not None:
                parent_tid = parent.get("task_id")
                list_id = parent.get("task_list") or list_id  # 하위 할 일은 상위와 같은 목록에
                if not parent_tid:  # 상위 할 일부터 보내고, 그다음 하위를 보내요
                    self._push_task(parent)
                    return
        pushing = self.__dict__.setdefault("_task_pushing", set())
        if item["id"] in pushing:
            return
        pushing.add(item["id"])
        snapshot = json.loads(json.dumps(item))

        def done(res, err) -> None:
            pushing.discard(snapshot["id"])
            if err is not None:
                log_error(f"Google Tasks로 보내지 못함 (다음 새로고침 때 다시 해요): {err}")
                self._tasks_error = str(err) if isinstance(err, SyncError) else "연결 문제"
                self._render_todo_sync_status()
                return
            self._tasks_error = ""
            live = self.todos.get(snapshot["id"])
            if live is None:  # 그사이 지웠어요
                self.worker.submit(self.service.task_remove, list_id, str(res.get("id")), callback=lambda r, e: None)
                return
            live["task_id"], live["task_list"] = str(res.get("id") or ""), list_id
            live["tpushed"] = item_task_state(snapshot)
            self.todos.save()
            for child in [i for i in self.todos.items if i.get("parent") == live["id"] and not i.get("task_id")]:
                self._push_task(child)
            if item_task_state(live) != live["tpushed"]:  # 보내는 사이 또 고쳤어요
                self._push_task(live)
            self._render_todo_sync_status()

        self.worker.submit(self.service.task_upsert, list_id, snapshot, parent_tid, callback=done)

    def _sync_tasks(self) -> None:
        """Google Tasks에서 받아 와서 양쪽을 맞춰요 (새로고침할 때마다)."""
        if not self.tasks_mode() or getattr(self, "_tasks_busy", False) or self.service._google_api() is None:
            return
        self._tasks_busy = True
        job = getattr(self, "_tasks_job", None)
        if job:
            self.after_cancel(job)
        self._tasks_job = self.after(TASKS_POLL_MS, self._sync_tasks)  # Tasks는 1분마다 따로 확인해요

        def done(result, err) -> None:
            self._tasks_busy = False
            if err is not None:
                self._tasks_error = str(err) if isinstance(err, SyncError) else "연결 문제"
                log_error(f"Google Tasks 받기 실패: {err}")
                self._render_todo_sync_status()
                return
            self._tasks_error = ""
            self._tasks_default = result["default"]
            self._tasks_lists = result["lists"]
            self._tasks_last = datetime.now()
            try:
                self._reconcile_tasks(result["tasks"], result["default"])
            except Exception:
                log_error("Tasks 맞추기 오류\n" + traceback.format_exc())

        self.worker.submit(self.service.tasks_fetch, "@default", callback=done)

    def _reconcile_tasks(self, tasks: list, default_list: str) -> None:
        where = {str(t["id"]): lid for lid, t in tasks if t.get("id")}
        live = {str(t["id"]): t for _lid, t in tasks if t.get("id") and not t.get("deleted")}
        list_id = default_list
        linked = [i for i in self.todos.items if i.get("task_id")]
        for item in linked:  # 기본 목록은 '@default'로 보냈어도 실제 ID로 맞춰 둬요
            if item.get("task_id") in where:
                item["task_list"] = where[item["task_id"]]
        by_tid = {i["task_id"]: i for i in linked}
        changed = False
        safe_to_delete = bool(live) or len(linked) < 3  # 목록이 통째로 비어 오면 지우지 않아요
        now = datetime.now().strftime("%Y-%m-%dT%H:%M")
        for item in list(linked):  # Tasks 앱(다른 컴퓨터)에서 고친 것 · 지운 것
            t = live.get(item["task_id"])
            if t is None:
                if safe_to_delete:
                    self.todos.items.remove(item)
                    changed = True
                continue
            parent_local = (by_tid.get(str(t.get("parent") or "")) or {}).get("id", "")
            remote, pushed = remote_task_state(t, parent_local), item.get("tpushed") or {}
            if remote != pushed:
                item["text"] = remote["title"] + ("\n" + remote["notes"] if remote["notes"] else "")
                for key, rkey in (("due", "due"), ("time", "time"), ("parent", "parent"), ("end_time", "end"),
                                  ("deadline", "deadline")):
                    if remote.get(rkey):
                        item[key] = remote[rkey]
                    else:
                        item.pop(key, None)
                if remote.get("files"):
                    item["attachments"] = [{"title": t_, "fileUrl": u} for t_, u in remote["files"]]
                else:
                    item.pop("attachments", None)
                if remote["done"] and not item.get("done"):
                    item["done"], item["done_at"] = True, str(t.get("completed") or now)[:16]
                elif not remote["done"] and item.get("done"):
                    item["done"] = False
                    item.pop("done_at", None)
                item["tpushed"] = remote
                changed = True
            elif item_task_state(item) != pushed:
                self._push_task(item)
        recent = (self.today - timedelta(days=30)).isoformat()
        fresh = sorted((t for tid, t in live.items() if tid not in by_tid), key=lambda t: (bool(t.get("parent")),
                                                                                           str(t.get("position", ""))))
        for t in fresh:  # Tasks 앱에서 새로 넣은 할 일 (상위부터)
            if t.get("status") == "completed" and str(t.get("completed") or "")[:10] < recent:
                continue
            parent_local = (by_tid.get(str(t.get("parent") or "")) or {}).get("id", "")
            if t.get("parent") and not parent_local:
                continue
            remote = remote_task_state(t, parent_local)
            item = {"id": uuid.uuid4().hex, "text": remote["title"] + ("\n" + remote["notes"] if remote["notes"] else ""),
                    "done": remote["done"], "created": self.today.isoformat(), "task_id": str(t["id"]),
                    "task_list": where.get(str(t["id"]), list_id), "tpushed": remote}
            for key, rkey in (("due", "due"), ("time", "time"), ("parent", "parent"), ("end_time", "end"),
                              ("deadline", "deadline")):
                if remote.get(rkey):
                    item[key] = remote[rkey]
            if remote.get("files"):
                item["attachments"] = [{"title": t_, "fileUrl": u} for t_, u in remote["files"]]
            if remote["done"]:
                item["done_at"] = str(t.get("completed") or now)[:16]
            self.todos.items.append(item)
            by_tid[item["task_id"]] = item
            changed = True
        pushing = self.__dict__.setdefault("_task_pushing", set())
        for item in list(self.todos.items):  # 아직 못 보낸 할 일
            if not item.get("task_id") and not item.get("done") and item["id"] not in pushing:
                self._push_task(item)
        if changed:
            self.todos.save()
            self.render_todos()
            self.refresh_summary()
            self.render_grid()
        self._render_todo_sync_status()
        self._mirror_soon(500)

    def mirror_cal(self) -> RemoteCalendar | None:
        key = self.cfg.get("todo_mirror") or ""
        if not key or not self.tasks_mode() or self.service._google_api() is None:
            return None
        return next((c for c in self.calendars if c.key == key and c.source == "Google" and c.writable), None)

    def _mirror_soon(self, delay: int = 1500) -> None:
        if self.mirror_cal() is None:
            return
        job = getattr(self, "_mirror_job", None)
        if job:
            self.after_cancel(job)
        self._mirror_job = self.after(delay, self._mirror_todos)

    def _mirror_todos(self) -> None:
        self._mirror_job = None
        cal = self.mirror_cal()
        if cal is None:
            return
        if getattr(self, "_mirror_busy", False):
            self._mirror_soon(3000)
            return
        self._mirror_busy = True
        items = [json.loads(json.dumps(i)) for i in self.todos.items if not i.get("done") and i.get("due")]

        def done(res, err) -> None:
            self._mirror_busy = False
            if err is not None:
                self._mirror_error = str(err) if isinstance(err, SyncError) else "연결 문제"
                log_error(f"아이폰 캘린더에 할 일 복사 실패: {err}")
            else:
                self._mirror_error = ""

        self.worker.submit(self.service.mirror_todos, cal.url, items, callback=done)

    def _mirror_changed(self, old_key: str, new_key: str) -> None:
        old_cal = next((c for c in self.calendars if c.key == old_key), None)
        if old_key and old_cal is not None:  # 예전 복사본은 정리해요 (할 일은 Tasks에 그대로 있어요)
            self.worker.submit(self.service.mirror_todos, old_cal.url, [], callback=lambda r, e: None)
        if new_key:
            cal = next((c for c in self.calendars if c.key == new_key), None)
            others = [ev for ev in self.events if ev.cal_key == new_key and not (ev.ref or {}).get("todo_id")]
            if cal is not None and len(others) >= 5 and not messagebox.askyesno(
                    APP_TITLE, f"'{cal.name}' 캘린더에는 이미 일정이 {len(others)}개 있어요.\n할 일을 보여 주는 캘린더로 쓰면 "
                               "위젯 화면에서는 이 캘린더의 일정이 보이지 않아요. '할 일' 캘린더를 따로 쓰는 걸 권해요.\n\n"
                               "그래도 이 캘린더를 쓸까요?", parent=self.host):
                self.cfg["todo_mirror"] = old_key
                self.save()
                return
            self._mirror_soon(200)
            self.show_flash("할 일을 아이폰 캘린더에도 보이게 하고 있어요")
        self._index_events()
        self.render()

    def _tasks_mode_changed(self, on: bool) -> None:
        if on:
            self._tasks_error = ""
            self._sync_tasks()
            self.show_flash("Google Tasks와 할 일을 맞추고 있어요")
        else:
            for item in self.todos.items:
                for k in ("task_id", "tpushed", "task_list"):
                    item.pop(k, None)
            self.todos.save()
        self.render_todos()

    def _todo_sync_changed(self, old_key: str, new_key: str) -> None:
        """할 일 캘린더를 바꾸거나 끌 때: 예전 캘린더의 할 일 일정을 정리하고, 새 캘린더로 보내요."""
        if new_key:
            cal = next((c for c in self.calendars if c.key == new_key), None)
            others = [ev for ev in self.events if ev.cal_key == new_key and not (ev.ref or {}).get("todo_id")]
            if cal is not None and len(others) >= 5 and not messagebox.askyesno(
                    APP_TITLE, f"'{cal.name}' 캘린더에는 이미 일정이 {len(others)}개 있어요.\n"
                               "할 일 캘린더로 쓰면 이 일정들이 모두 할 일로 바뀌어요. "
                               "'할 일' 캘린더를 새로 만들어 고르는 걸 권해요.\n\n그래도 이 캘린더를 쓸까요?",
                    parent=self.host):
                self.cfg["todo_sync"] = old_key  # 원래대로
                self.save()
                self._index_events()
                self.render()
                return
        mirrored = [i for i in self.todos.items if i.get("event_id") and i.get("event_cal") == old_key]
        old_cal = next((c for c in self.calendars if c.key == old_key), None)
        if old_key and mirrored and old_cal is not None:
            remove = True
            if not new_key:  # 끌 때는 물어봐요
                remove = messagebox.askyesno(APP_TITLE, f"아이폰 캘린더('{old_cal.name}')에 넣어 둔 할 일 일정 "
                                                        f"{len(mirrored)}개를 지울까요?\n지우지 않으면 보통 일정으로 남아요.",
                                             parent=self.host)
            for item in mirrored:
                eid = item.pop("event_id")
                item.pop("pushed", None)
                item.pop("event_cal", None)
                if remove:
                    self.worker.submit(self.service.todo_delete, old_cal.url, eid, callback=lambda r, e: None)
            self.todos.save()
        if new_key:
            count = self._push_all_todos()
            if count:
                self.show_flash(f"날짜 있는 할 일 {count}개를 아이폰 캘린더에 넣고 있어요")
        self._index_events()
        self.render()

    def _push_all_todos(self) -> int:
        cal = self.todo_sync_cal()
        if cal is None:
            return 0
        items = [i for i in self.todos.items if not i.get("done") and i.get("due")]
        for item in items:
            if item.get("event_cal") != cal.key:  # 다른 캘린더에 있던 표시는 버리고 새로 넣어요
                for k in ("event_id", "pushed", "event_cal"):
                    item.pop(k, None)
            self._push_todo(item)
        return len(items)

    def _sync_todos_from(self, start: date, end: date, res: FetchResult) -> None:
        """받아 온 '할 일' 캘린더 일정으로 아이폰에서 고친 것 · 지운 것 · 새로 넣은 것을 위젯 할 일에 반영해요."""
        cal = self.todo_sync_cal()
        if cal is None:
            return
        fetched_ok = any(c.key == cal.key for c in res.calendars) and not res.problems
        mine = [ev for ev in res.events if ev.cal_key == cal.key and (ev.ref or {}).get("event_id")
                and not ev.ref.get("recurring")]
        by_todo = {ev.ref.get("todo_id"): ev for ev in mine if ev.ref.get("todo_id")}
        by_eid = {ev.ref["event_id"]: ev for ev in mine}
        changed = False
        now = datetime.now().strftime("%Y-%m-%dT%H:%M")
        for item in self.todos.items:
            if item.get("done") or not item.get("event_id") or item.get("event_cal") != cal.key:
                continue
            ev = by_todo.get(item["id"]) or by_eid.get(item["event_id"])
            pushed = item.get("pushed") or {}
            if ev is None:
                due = pushed.get("due") or item.get("due")
                if fetched_ok and due and start <= date.fromisoformat(due) < end:
                    item["done"], item["done_at"] = True, now  # 아이폰에서 지웠어요 → 끝낸 할 일
                    for k in ("event_id", "pushed", "event_cal"):
                        item.pop(k, None)
                    changed = True
                continue
            remote = todo_remote_state(ev)
            if remote != pushed:  # 아이폰에서 고쳤어요
                lines = (item.get("text") or "").splitlines()
                item["text"] = "\n".join([remote["title"]] + lines[1:])
                item["due"] = remote["due"]
                if remote["time"]:
                    item["time"] = remote["time"]
                else:
                    item.pop("time", None)
                item["pushed"] = remote
                changed = True
            elif todo_signature(item) != pushed:  # 위젯에서 고친 게 아직 못 갔어요
                self._push_todo(item)
        pushing = self.__dict__.setdefault("_todo_pushing", set())
        for item in self.todos.items:  # 연결이 안 돼서 아직 못 보낸 할 일
            if not item.get("done") and item.get("due") and not item.get("event_id") and item["id"] not in pushing:
                self._push_todo(item)
        known_ids = {i["id"] for i in self.todos.items}
        known_eids = {i.get("event_id") for i in self.todos.items if i.get("event_id")}
        for ev in mine:  # 아이폰(또는 다른 컴퓨터)에서 새로 넣은 할 일
            tid = ev.ref.get("todo_id")
            if (tid and tid in known_ids) or ev.ref["event_id"] in known_eids:
                continue
            remote = todo_remote_state(ev)
            item = {"id": tid or uuid.uuid4().hex, "text": remote["title"], "done": False,
                    "created": date.today().isoformat(), "due": remote["due"],
                    "event_id": ev.ref["event_id"], "event_cal": cal.key, "pushed": remote}
            if remote["time"]:
                item["time"] = remote["time"]
            self.todos.items.append(item)
            changed = True
            if not tid:  # 위젯의 할 일 표시를 붙여 둬요
                self._push_todo(item)
        if changed:
            self.todos.save()
            self.render_todos()
            self.refresh_summary()

    def open_todo(self, item: dict | None = None, parent: dict | None = None, prefill: dict | None = None) -> None:
        old = getattr(self, "_todo_dlg", None)
        if old is not None and old.winfo_exists():
            if item is None and old.item is None and parent is None and old.parent is None and not prefill:
                old.lift()
                return
            old.destroy()
        self._todo_dlg = TodoDialog(self, item, parent, prefill)

    def complete_todo(self, item_id: str) -> None:
        for child in [i for i in self.todos.items if i.get("parent") == item_id and not i.get("done")]:
            self.complete_todo(child["id"])  # 하위 할 일도 함께 끝내요
        self.todos.complete(item_id)
        item = self.todos.get(item_id)
        if item is not None:
            self._push_todo(item)  # 끝낸 할 일은 아이폰 캘린더에서 빠지고, Tasks에서는 체크돼요
        self.render_todos()
        self.refresh_summary()
        self.render_grid()
        self.show_flash("할 일을 끝냈어요" if self.cfg["todo_done"] != "hide"
                        else "할 일을 끝냈어요. '끝낸 할 일 보기'에서 다시 볼 수 있어요")

    def reopen_todo(self, item_id: str) -> None:
        self.todos.reopen(item_id)
        item = self.todos.get(item_id)
        if item is not None:
            self._push_todo(item)
        self.render_todos()
        self.refresh_summary()
        self.render_grid()
        self.show_flash("다시 할 일로 돌렸어요")

    def open_todo_history(self) -> None:
        if getattr(self, "_history_dlg", None) and self._history_dlg.winfo_exists():
            self._history_dlg.lift()
            return
        self._history_dlg = TodoHistoryDialog(self)

    def delete_todo(self, item_id: str) -> None:
        for child in [i for i in self.todos.items if i.get("parent") == item_id]:
            self.delete_todo(child["id"])  # 하위 할 일도 함께 지워요
        item = self.todos.get(item_id)
        if item is not None and (item.get("event_id") or item.get("task_id")):
            self._push_todo(dict(item, _deleted=True))
        self.todos.delete(item_id)
        self.render_todos()
        self.refresh_summary()
        self.render_grid()

    def _todo_menu(self, e, item_id: str, done: bool = False):
        menu = tk.Menu(self, tearoff=0)
        if done:
            menu.add_command(label="다시 할 일로", command=lambda: self.reopen_todo(item_id))
        else:
            menu.add_command(label="끝냄으로 표시", command=lambda: self.complete_todo(item_id))
        item = next((i for i in self.todos.items if i["id"] == item_id), None)
        if item is not None:
            menu.add_command(label="고치기 (날짜 · 색)…", command=lambda: self.open_todo(item))
            if not done and not item.get("parent"):
                menu.add_command(label="하위 할 일 추가…", command=lambda: self.open_todo(parent=item))
        menu.add_command(label="지우기", command=lambda: self.delete_todo(item_id))
        menu.add_separator()
        menu.add_command(label="끝낸 할 일 보기…", command=self.open_todo_history)
        self._popup(menu, e.x_root, e.y_root)
        return "break"

    def _shown_done(self) -> tuple[list, list]:
        """(끝낸 할 일 전부, 그중 패널에 보여 줄 것)"""
        done_all = self.todos.done_items()
        mode = self.cfg.get("todo_done", "strike")
        if mode == "strike":
            return done_all, done_all
        if mode == "today":
            today = self.today.isoformat()
            return done_all, [i for i in done_all if str(i.get("done_at") or "")[:10] == today]
        return done_all, []

    def _todo_row(self, item: dict, done: bool, wrap: int, indent: int = 0) -> None:
        t, f, px = self.t, self.fonts, self.px
        bg = t["panel"]
        row = tk.Frame(self.todo_rows, bg=bg)
        row.pack(fill="x", pady=px(1), padx=(px(20) * indent, 0))
        color = todo_hex(item.get("color", "")) or TASK_BLUE
        widgets = [row]
        size = max(14, px(18))
        box = tk.Canvas(row, width=size, height=size, bg=bg, highlightthickness=0, cursor="hand2")
        box.pack(side="left", anchor="n", padx=(0, px(6)), pady=(px(1), 0))

        def paint(hover: bool = False, b=box, c=color) -> None:
            b.delete("all")
            shade = t["accent"] if hover and not done else (blend(c, bg, 0.35) if done else c)
            self._task_circle(b, size / 2, size / 2, size / 2 - px(2), shade, done, bg, ())

        paint()
        action = self.reopen_todo if done else self.complete_todo
        box.bind("<Button-1>", lambda e, i=item["id"]: action(i))
        box.bind("<Enter>", lambda e: paint(True))
        box.bind("<Leave>", lambda e: paint(False))
        Tooltip(box, "다시 할 일로" if done else "끝냄으로 표시", self)
        col = tk.Frame(row, bg=bg)
        col.pack(side="left", fill="x", expand=True)
        lines = (item.get("text") or "").splitlines() or [""]
        lbl = tk.Label(col, text=lines[0], font=f["event_done" if done else "event"], bg=bg,
                       fg=t["muted"] if done else t["text"], anchor="w", justify="left", wraplength=wrap)
        lbl.pack(fill="x")
        widgets += [col, lbl]
        desc = "\n".join(lines[1:]).strip()
        if desc:  # 설명은 제목 아래에 작은 검정 글씨로
            note = tk.Label(col, text=desc, font=f["small"], bg=bg, fg=t["muted"] if done else t["text"],
                            anchor="w", justify="left", wraplength=wrap)
            note.pack(fill="x", pady=(px(1), 0))
            widgets.append(note)
            if not done:
                note.bind("<Double-Button-1>", lambda e, it=item: self.open_todo(it))
        due = todo_due_label(item, self.today)
        files = len(item.get("attachments") or [])
        if due or files:
            tone = {"late": t["sun"], "soon": SOON_ORANGE}.get(due[1], t["muted"]) if due else t["muted"]
            line = " · ".join(x for x in ((due[0] if due else ""), (f"첨부 {files}" if files else "")) if x)
            sub = tk.Label(col, text=line, font=f["small"], bg=bg, fg=tone, anchor="w")
            sub.pack(fill="x")
            widgets.append(sub)
        for w in widgets:
            w.bind("<Button-3>", lambda e, i=item["id"]: self._todo_menu(e, i, done))
        if not done:
            lbl.bind("<Double-Button-1>", lambda e, it=item: self.open_todo(it))

    def render_todos(self) -> None:
        if not self.cfg["show_timeline"] or not hasattr(self, "todo_rows") or not self.todo_rows.winfo_exists():
            return
        t, f, px = self.t, self.fonts, self.px
        bg = t["panel"]
        for w in self.todo_rows.winfo_children():
            w.destroy()
        items = self.todos.open_items()
        done_all, done_shown = self._shown_done()
        self.todo_count.config(text=f"{len(items)}개" if items else "")
        col_w = self.todo_cv.winfo_width() if hasattr(self, "todo_cv") else 0
        wrap = max(px(100), (col_w if col_w > 10 else self._side_width() // 2) - px(48))
        if not items and not done_shown:
            text = "남은 할 일이 없어요." if done_all else "아래 '+ 할 일 추가'로 적어 두면 여기와 시작 화면에 보여요."
            tk.Label(self.todo_rows, text=text, font=f["small"], bg=bg, fg=t["muted"], anchor="w",
                     justify="left", wraplength=wrap).pack(fill="x")
        open_ids = {i["id"] for i in items}
        for item in items:  # 목록이 길면 마우스 휠로 내려 봐요 (하위 할 일은 상위 아래에 들여 써요)
            if item.get("parent") in open_ids:
                continue
            self._todo_row(item, False, wrap)
            for child in [i for i in items if i.get("parent") == item["id"]]:
                self._todo_row(child, False, wrap - px(20), indent=1)
        for item in done_shown[:8]:
            self._todo_row(item, True, wrap)
        links = tk.Frame(self.todo_rows, bg=bg)
        if done_all:
            past = tk.Label(links, text=f"끝낸 할 일 {len(done_all)}개 보기", font=f["link"], bg=bg,
                            fg=t["muted"], cursor="hand2")
            past.pack(side="left")
            past.bind("<Button-1>", lambda e: self.open_todo_history())
        if links.winfo_children():
            links.pack(fill="x", pady=(px(2), 0))
        self._render_todo_sync_status()
        self.render_chips()
        self.render_side()
        for w in [self.todo_rows] + list(self.todo_rows.winfo_children()):
            for child in [w] + list(w.winfo_children()):
                for grand in [child] + list(child.winfo_children()):
                    self._wheel_scrolls_todo(grand)

    # ── 사용자 동작 ──
    def select_date(self, d: date) -> None:
        self.selected = d
        g0 = self.grid_first_day()
        if not g0 <= d < g0 + timedelta(days=7 * self.cfg["weeks"]):
            self.anchor = d
            self.follow_today = False
        self.render()
        self.ensure_data()

    def shift_weeks(self, n: int) -> None:
        self.anchor += timedelta(days=7 * n)
        self.follow_today = False
        self.render()
        self.ensure_data()

    def go_today(self) -> None:
        self.anchor = self.selected = self.today
        self.follow_today = True
        self._scrolled_for = None
        self.render()
        self.ensure_data()

    def _cell_at(self, x: float, y: float) -> date | None:
        wk_w, col_w = self._grid_cols
        if x < wk_w:
            return None
        c = int((x - wk_w) // col_w)
        if not 0 <= c < 7:
            return None
        for y0, y1, kind, payload in self._row_geom:
            if y0 <= y < y1:
                return payload[c] if kind == "week" else None
        return None

    def _grid_click(self, e) -> None:
        d = self._cell_at(e.x, e.y)
        if d:
            self.select_date(d)

    def _event_double(self, ev: Event) -> None:
        self._event_dbl = True  # 칸을 두 번 누른 것(새 일정)으로 처리되지 않게
        self.after(1, lambda: self.edit_event(ev))

    def edit_event(self, ev: Event) -> None:
        if self.event_card is not None and self.event_card.winfo_exists():
            self.event_card.destroy()
        if ev.kind != "event":
            return
        ref = ev.ref or {}
        if ev.source == "Google" and ref.get("event_id"):
            if not ref.get("editable"):
                messagebox.showinfo(APP_TITLE, "다른 사람이 초대한 일정이라 고칠 수 없어요.\n"
                                               "주최자가 '일정 수정' 권한을 주면 고칠 수 있어요.", parent=self.host)
                return
            self.open_add(ev.start if ev.all_day else ev.start.date(), event=ev)
        elif ev.source == "Google":
            messagebox.showinfo(APP_TITLE, "연결 코드 방식에서는 일정을 고칠 수 없어요.\n"
                                           "설정 → Google에서 Google 계정으로 로그인하면 위젯에서 바로 고칠 수 있어요.",
                                parent=self.host)
        elif ev.source == "iCloud":
            messagebox.showinfo(APP_TITLE, "iCloud 일정은 아이폰이나 Mac의 캘린더에서 고쳐 주세요.", parent=self.host)
        else:
            messagebox.showinfo(APP_TITLE, "구독한 캘린더의 일정은 고칠 수 없어요.", parent=self.host)

    def _grid_double(self, e) -> None:
        if getattr(self, "_event_dbl", False):
            self._event_dbl = False
            return
        d = self._cell_at(e.x, e.y)
        if d:
            self.open_add(d)

    def _timeline_double(self, e) -> None:
        if getattr(self, "_event_dbl", False):
            self._event_dbl = False
            return
        hour_h = getattr(self, "_hour_h", 0)
        if not hour_h:
            return
        minutes = int(self.time_cv.canvasy(e.y) / hour_h * 60)
        minutes = max(0, min(23 * 60 + 30, minutes // 30 * 30))
        self.open_add(self.selected, dt_time(minutes // 60, minutes % 60))

    def _context_menu(self, e) -> None:
        if getattr(self, "_menu_handled", False):  # 할 일처럼 자기 메뉴가 이미 뜬 곳이에요
            self._menu_handled = False
            return
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(label="일정 추가", command=self.open_add)
        menu.add_command(label="학사일정 · 방과후 파일 가져오기…", command=self.open_import)
        menu.add_command(label="새 캘린더 만들기…", command=lambda: NewCalendarDialog(self))
        menu.add_command(label="캘린더 지우기…", command=lambda: DeleteCalendarDialog(self))
        removed = self.removed_entries()
        if removed:
            sub = tk.Menu(menu, tearoff=0)
            for key, name in removed:
                sub.add_command(label=name, command=lambda k=key: self.restore_to_list(k))
            menu.add_cascade(label=f"숨긴 캘린더 다시 보이기 ({len(removed)})", menu=sub)
        menu.add_command(label="오늘 일정과 할 일 보기", command=self.show_summary)
        menu.add_command(label="끝낸 할 일 보기…", command=self.open_todo_history)
        menu.add_command(label="새로고침", command=lambda: self.ensure_data(force=True))
        menu.add_command(label="오늘로 이동", command=self.go_today)
        menu.add_separator()
        menu.add_checkbutton(label="위치와 크기 고정", variable=self.lock_var,
                             command=lambda: self.toggle_lock(self.lock_var.get()))
        menu.add_command(label="화면 전체에 맞추기", command=self.fit_to_screen)
        menu.add_command(label="설정", command=self.open_settings)
        menu.add_separator()
        menu.add_command(label="종료", command=self.quit_app)
        self._popup(menu, e.x_root, e.y_root)

    def _popup(self, menu: tk.Menu, x: int, y: int) -> None:
        """메뉴 바깥을 누르면 메뉴가 닫히도록, 보이지 않는 작은 창을 잠깐 활성 창으로 만들어요."""
        if self.layer:
            try:
                user32.SetForegroundWindow(int(self.host.wm_frame(), 16))
            except Exception:
                pass
        menu.tk_popup(x, y)

    def _show_problems(self, _e=None) -> None:
        if self.problems:
            messagebox.showwarning(APP_TITLE, "\n\n".join(self.problems), parent=self.host)

    def show_flash(self, text: str) -> None:
        self.flash = text
        self.render_status()
        self.after(4000, lambda: (setattr(self, "flash", ""), self.render_status()))

    def confirm_quit(self) -> None:
        if messagebox.askyesno(APP_TITLE, "위젯을 닫을까요?\n다시 보려면 프로그램을 다시 실행하면 돼요.", parent=self.host):
            self.quit_app()

    def quit_app(self) -> None:
        self.cfg["geometry"] = [self.winfo_x(), self.winfo_y(), self.winfo_width(), self.winfo_height()]
        self.save()
        self.destroy()

    def open_settings(self, tab: str | None = None) -> None:
        if getattr(self, "_settings_dlg", None) and self._settings_dlg.winfo_exists():
            self._settings_dlg.lift()
            return
        self._settings_dlg = SettingsDialog(self, tab)

    def open_welcome(self) -> None:
        if GOOGLE_CLIENT_ID and not self.cfg.get("welcomed"):
            WelcomeDialog(self)
        else:
            self.open_settings()

    # ── Google 로그인 ──
    def google_sign_in(self, on_done=None) -> None:
        """브라우저로 Google 로그인. 기다리는 동안 위젯이 멈추지 않게 따로 돌려요."""
        if getattr(self, "_signing_in", False):
            return
        self._signing_in = True

        def run():
            try:
                result, error = google_login(), None
            except Exception as exc:
                if not isinstance(exc, SyncError):
                    log_error("Google 로그인 오류\n" + traceback.format_exc())
                    exc = SyncError("Google 로그인 중에 문제가 생겼어요.")
                result, error = None, exc
            self.worker.results.put((lambda r, e: self._signed_in(r, e, on_done), result, error))

        threading.Thread(target=run, daemon=True).start()

    def _signed_in(self, result, error, on_done) -> None:
        self._signing_in = False
        if error is None:
            same_account = result["email"] == self.cfg.get("google_email") and not self.cfg.get("google_url")
            self.cfg.update({"google_refresh": protect(result["refresh_token"]), "google_email": result["email"],
                             "google_can_write": result["can_write"], "google_url": ""})
            self.save()
            self._configure_service()
            self._login_card_shown = False
            if not same_account:
                self.reset_cache()
            self.ensure_data(force=True)
        if on_done:
            on_done(result, error)

    def google_sign_out(self) -> None:
        token = unprotect(self.cfg.get("google_refresh", ""))
        self.cfg.update({"google_refresh": "", "google_email": "", "google_can_write": True})
        self.save()
        self._configure_service()
        self.calendars = [c for c in self.calendars if c.source != "Google"]
        self.reset_cache()
        self.render()
        self.ensure_data(force=True)
        if token:
            threading.Thread(target=revoke_google, args=(token,), daemon=True).start()

    # ── 업데이트 ──
    def _update_tick(self) -> None:
        if self.cfg.get("update_mode", "auto") != "off":
            self.check_updates()
        self.after(6 * 3600_000, self._update_tick)

    def check_updates(self, manual: bool = False, on_done=None) -> None:
        self.worker.submit(check_for_update, callback=lambda info, err: self._update_checked(info, err, manual, on_done))

    def _update_checked(self, info, error, manual: bool, on_done) -> None:
        if on_done:
            on_done(info, error)
        if error is not None:
            log_error(f"업데이트 확인 실패: {error}")
            return
        if info is None or manual:
            return
        if self.cfg.get("update_mode", "auto") == "auto":
            self.install_update(info)
        else:
            self.toasts.append(UpdateCard(self, info))
            self.restack_toasts()

    def install_update(self, info: dict) -> None:
        if getattr(self, "_updating", False):
            return
        self._updating = True
        self.show_flash(f"새 버전 {info['version']}을(를) 내려받는 중…")
        self.worker.submit(download_update, info, callback=lambda path, err: self._update_downloaded(path, err))

    def _update_downloaded(self, path, error) -> None:
        if error is not None:
            self._updating = False
            log_error(f"업데이트 내려받기 실패: {error}")
            self.show_flash(str(error) if isinstance(error, SyncError) else "업데이트를 내려받지 못했어요.")
            return
        self.show_flash("새 버전으로 바꾸는 중이에요. 잠시 뒤 다시 켜져요.")
        self.after(1500, lambda: self._start_installer(path))

    def _start_installer(self, path: str) -> None:
        try:
            launch_installer(path)
        except Exception as exc:
            self._updating = False
            log_error(f"업데이트 설치 시작 실패: {exc}")
            self.show_flash("업데이트 설치를 시작하지 못했어요.")
            return
        self.quit_app()

    def open_add(self, day: date | None = None, start_time: dt_time | None = None, event: Event | None = None,
                 prefill: dict | None = None) -> None:
        if (event is None and prefill is None and start_time is None
                and self.cfg.get("last_calendar") == TODO_CHIP):  # 지난번에 '할 일' 탭을 썼으면 할 일 창으로
            self.open_todo(prefill={"date": day} if day else None)
            return
        if not (self.has_google() or self.has_icloud()):
            if messagebox.askyesno(APP_TITLE, "일정을 추가하려면 Google이나 iCloud 캘린더를 연결해야 해요.\n"
                                              "지금 연결할까요?", parent=self.host):
                self.open_settings()
            return
        if not self.writable_calendars():
            msg = "일정을 넣을 캘린더 목록을 아직 불러오지 못했어요."
            if self.problems:
                msg += "\n\n" + self.problems[0]
            messagebox.showinfo(APP_TITLE, msg, parent=self.host)
            self.ensure_data(force=True)
            return
        old = getattr(self, "_add_dlg", None)
        if old is not None and old.winfo_exists():
            if event is None and old.event is None:
                old.lift()
                return
            old.destroy()
        self._add_dlg = AddEventDialog(self, day or self.selected, start_time, event=event, prefill=prefill)

    def open_import(self) -> None:
        if not self.writable_calendars():
            msg = ("일정을 넣을 캘린더가 아직 없어요. Google이나 iCloud 캘린더를 먼저 연결해 주세요."
                   if not (self.has_google() or self.has_icloud()) else "일정을 넣을 캘린더 목록을 아직 불러오지 못했어요.")
            messagebox.showinfo(APP_TITLE, msg, parent=self.host)
            return
        if getattr(self, "_import_dlg", None) and self._import_dlg.winfo_exists():
            self._import_dlg.lift()
            return
        self._import_dlg = ImportDialog(self)

    def event_added(self, d: date) -> None:
        self.show_flash("일정을 추가했어요")
        self.select_date(d)
        self.ensure_data(force=True)

    def apply_settings(self, old: dict) -> None:
        self.save()
        old_mirror = (old.get("todo_mirror") or "") if old.get("todo_tasks") else ""
        new_mirror = (self.cfg.get("todo_mirror") or "") if self.cfg.get("todo_tasks") else ""
        if old_mirror != new_mirror:
            self.after(400, lambda o=old_mirror, n=new_mirror: self._mirror_changed(o, n))
        if bool(old.get("todo_tasks")) != bool(self.cfg.get("todo_tasks")):
            self.after(300, lambda on=bool(self.cfg.get("todo_tasks")): self._tasks_mode_changed(on))
        if (old.get("todo_sync") or "") != (self.cfg.get("todo_sync") or ""):
            self.after(100, lambda o=old.get("todo_sync") or "", n=self.cfg.get("todo_sync") or "":
                       self._todo_sync_changed(o, n))
        if old.get("font_style") != self.cfg.get("font_style"):
            self._make_fonts()
        self._apply_font_scale()
        self.rebuild()
        self._configure_service()
        source_keys = ("google_url", "google_token", "google_refresh", "apple_id", "password", "caldav_url",
                       "ics_urls", "show_holidays", "holiday_url")
        if any(old.get(k) != self.cfg.get(k) for k in source_keys):
            self.reset_cache()  # 연결이 바뀐 때만 처음부터 다시 받아요
        if not self.has_sources():
            self.events, self.calendars = [], []
            self._index_events()
        self.ensure_data(force=True)
        self._schedule_refresh()

    def _on_tk_error(self, exc, val, tb) -> None:
        log_error("화면 오류\n" + "".join(traceback.format_exception(exc, val, tb)))

    def show_event(self, ev: Event) -> None:
        if self.event_card is not None and self.event_card.winfo_exists():
            self.event_card.destroy()
        self.event_card = EventCard(self, ev)

    def _bind_event(self, cv: tk.Canvas, tag: str, ev: Event) -> None:
        cv.tag_bind(tag, "<Button-1>", lambda e, ev=ev: self.show_event(ev))
        cv.tag_bind(tag, "<Double-Button-1>", lambda e, ev=ev: self._event_double(ev))
        cv.tag_bind(tag, "<Enter>", lambda e: cv.config(cursor="hand2"))
        cv.tag_bind(tag, "<Leave>", lambda e: cv.config(cursor=""))

    # ── 그리기 ──
    def render_soon(self, delay: int = 30) -> None:
        if self._render_job is None:
            self._render_job = self.after(delay, self.render)

    def render(self) -> None:
        if self._render_job is not None:
            try:
                self.after_cancel(self._render_job)
            except tk.TclError:
                pass
            self._render_job = None
        try:
            self.render_title()
            self.render_chips()
            self.render_grid()
            self.render_side()
            self.render_status()
        except tk.TclError:
            log_error("그리기 오류\n" + traceback.format_exc())

    def render_title(self) -> None:
        d = self.today
        self.title_lbl.config(text=f"오늘은 {d.month}월 {d.day}일 {WEEKDAY_FULL[d.weekday()]}")
        parts = [f"{d.year}년"]
        if self.cfg["show_lunar"] and lunar_label(d):
            parts.append(f"음력 {lunar_label(d)}")
        if d in self.holidays:
            parts.append(self.holidays[d])
        self.title_sub.config(text=", ".join(parts))

    def grid_rows(self) -> list:
        """달력에 그릴 줄 목록: ('week', 7칸 날짜 - 빈칸은 None) 또는 ('month', 그 달 1일)"""
        start = self.grid_first_day()
        rows = []
        for w in range(self.cfg["weeks"]):
            days = [start + timedelta(days=7 * w + i) for i in range(7)]
            cut = next((i for i, d in enumerate(days) if d.day == 1), None)
            if self.cfg.get("split_months", True) and cut is not None and (w > 0 or cut > 0):
                if cut > 0:
                    rows.append(("week", [d if i < cut else None for i, d in enumerate(days)]))
                rows.append(("month", days[cut]))
                rows.append(("week", [d if i >= cut else None for i, d in enumerate(days)]))
            else:
                rows.append(("week", days))
        return rows

    def _row_bars(self, days: list) -> list:
        """한 줄에 걸친 종일 · 여러 날 일정을 겹치지 않는 칸에 나눠 놓아요."""
        cols = [i for i, d in enumerate(days) if d]
        if not cols:
            return []
        ca, cb = cols[0], cols[-1]
        row_start, row_end = days[ca], days[cb] + timedelta(days=1)
        bars = []
        for ev in self.bar_events:
            s = ev.start if ev.all_day else ev.start.date()
            e = ev.end if ev.all_day else (ev.end - timedelta(microseconds=1)).date() + timedelta(days=1)
            if e <= row_start or s >= row_end:
                continue
            bars.append((ca + max(0, (s - row_start).days), min(cb, ca + (e - row_start).days - 1),
                         s >= row_start, ev))
        bars.sort(key=lambda b: (b[0], -(b[1] - b[0]), b[3].title))
        lane_end, placed = [], []
        for c0, c1, starts_here, ev in bars:
            for lane, last in enumerate(lane_end):
                if c0 > last:
                    lane_end[lane] = c1
                    placed.append((lane, c0, c1, starts_here, ev))
                    break
            else:
                lane_end.append(c1)
                placed.append((len(lane_end) - 1, c0, c1, starts_here, ev))
        return placed

    def _draw_cell_header(self, cv, d: date, c: int, x0: float, y0: float, col_w: float, bg: str,
                          first: bool) -> None:
        t, f, px = self.t, self.fonts, self.px
        ls = f["day"].metrics("linespace")
        cy = y0 + px(7) + ls / 2
        x = x0 + px(9)
        simple = not (d.day == 1 or first)
        label = str(d.day) if simple else f"{d.month}월 {d.day}일"
        font = f["day"] if simple else f["day_month"]
        color = t[self.tone(d)]
        if d == self.today and simple:
            dia = max(ls, f["day"].measure(label)) + px(6)
            cx = x + dia / 2 - px(3)
            cv.create_image(cx, cy, image=self.circle(dia, t["accent"], bg))
            cv.create_text(cx, cy, text=label, font=font, fill=t["accent_text"])
            right = cx + dia / 2
        else:
            item = cv.create_text(x, cy, text=label, anchor="w", font=font,
                                  fill=t["accent"] if d == self.today else color)
            right = cv.bbox(item)[2]
        extras = []
        if d in self.holidays:
            extras.append((self.holidays[d], t["holiday"]))
        elif d in self.observances:
            extras.append((self.observances[d], t["muted"]))
        if self.cfg["show_lunar"] and lunar_label(d):
            extras.append((f"(음){lunar_label(d)}", t["muted"]))
        x_after = right + px(6)
        limit = x0 + col_w - px(6)
        for text, fill in extras:
            fitted = self.fit(text, f["day_small"], limit - x_after)
            if not fitted:
                break
            item = cv.create_text(x_after, cy + px(1), text=fitted, anchor="w", font=f["day_small"], fill=fill)
            x_after = cv.bbox(item)[2] + px(5)

    def render_grid(self) -> None:
        cv, t, f, px = self.grid_cv, self.t, self.fonts, self.px
        cv.delete("all")
        self._tag_n = 0
        W, H = cv.winfo_width(), cv.winfo_height()
        if W < 80 or H < 80:
            return
        wk_w = px(30) if self.cfg["show_week_numbers"] else 0
        head_h = f["dow"].metrics("linespace") + px(12)
        col_w = (W - wk_w) / 7
        rows = self.grid_rows()
        n_weeks = sum(1 for kind, _ in rows if kind == "week")
        month_h = f["title"].metrics("linespace") + px(18)
        row_h = max(px(36), (H - head_h - (len(rows) - n_weeks) * month_h) / max(1, n_weeks))
        self._grid_cols = (wk_w, col_w)
        self._row_geom = []
        names = WEEKDAY_FULL_SUN if col_w >= px(84) else GRID_HEADER
        for c, name in enumerate(names):
            color = t["sun"] if c == 0 else t["sat"] if c == 6 else t["muted"]
            cv.create_text(wk_w + c * col_w + col_w / 2, head_h / 2, text=name, font=f["dow"], fill=color)
        y, first_row = head_h, True
        for kind, payload in rows:
            if kind == "month":
                d = payload
                label = f"{d.month}월" if d.year == self.today.year else f"{d.year}년 {d.month}월"
                cv.create_text(wk_w + px(10), y + month_h / 2 + px(3), text=label, anchor="w",
                               font=f["title"], fill=t["text"])
                self._row_geom.append((y, y + month_h, "month", d))
                y += month_h
                continue
            self._draw_week(cv, payload, y, row_h, wk_w, col_w, first_row)
            self._row_geom.append((y, y + row_h, "week", payload))
            first_row = False
            y += row_h

    def _draw_week(self, cv, days: list, y0: float, row_h: float, wk_w: float, col_w: float,
                   first_row: bool) -> None:
        t, f, px = self.t, self.fonts, self.px
        gap = max(2, px(3))
        ev_font = f["event"]
        line_h = ev_font.metrics("linespace") + px(5)
        header_h = f["day"].metrics("linespace") + px(14)
        now = datetime.now().astimezone()
        first_col = next(i for i, d in enumerate(days) if d)
        if wk_w:
            d = days[first_col]
            sunday = d - timedelta(days=(d.weekday() + 1) % 7)
            cv.create_text(wk_w / 2, y0 + row_h / 2, text=str((sunday + timedelta(days=1)).isocalendar()[1]),
                           font=f["small"], fill=t["muted"])
        for c, d in enumerate(days):
            if d is None:
                continue  # 다른 달의 칸은 비워 둬요
            x0 = wk_w + c * col_w
            bg = t["today_cell"] if d == self.today else t["weekend"] if c in (0, 6) else t["cell"]
            round_rect(cv, x0 + gap / 2, y0 + gap / 2, x0 + col_w - gap / 2, y0 + row_h - gap / 2, px(7),
                       fill=bg, outline="")
            if d == self.selected and d != self.today:
                inset = gap / 2 + 1
                round_outline(cv, x0 + inset, y0 + inset, x0 + col_w - inset, y0 + row_h - inset, px(7),
                              t["accent"], max(1, px(1.5)))
            self._draw_cell_header(cv, d, c, x0, y0, col_w, bg, first=first_row and c == first_col)
        max_lines = int((row_h - gap - header_h - px(4)) // line_h)
        if max_lines <= 0:
            return

        # 종일 · 여러 날 일정은 막대로
        bar_limit = max_lines - 1
        lanes_in_col, hidden = [0] * 7, [0] * 7
        for lane, c0, c1, starts_here, ev in self._row_bars(days):
            if lane >= bar_limit:
                for c in range(c0, c1 + 1):
                    hidden[c] += 1
                continue
            for c in range(c0, c1 + 1):
                lanes_in_col[c] = max(lanes_in_col[c], lane + 1)
            bx0 = wk_w + c0 * col_w + px(6)
            bx1 = wk_w + (c1 + 1) * col_w - px(6)
            by = y0 + header_h + lane * line_h
            tag = self._next_tag()
            round_rect(cv, bx0, by + px(1), bx1, by + line_h - px(1), px(4),
                       fill=blend(ev.color, t["cell"], t["tint"]), outline="", tags=(tag,))
            if starts_here:
                round_rect(cv, bx0 + px(3), by + px(4), bx0 + px(6), by + line_h - px(4), px(1.5), fill=ev.color,
                           outline="", tags=(tag,))
            cv.create_text(bx0 + px(8), by + line_h / 2, text=self.fit(ev.title, ev_font, bx1 - bx0 - px(12)),
                           anchor="w", font=ev_font, fill=t["text"], tags=(tag,))
            self._bind_event(cv, tag, ev)

        # 날짜 있는 할 일, 그다음 시간이 있는 일정을 줄마다
        todo_index = self._todo_index()
        for c, d in enumerate(days):
            if d is None:
                continue
            x0 = wk_w + c * col_w
            timed = [ev for ev in self.by_day.get(d, []) if ev.kind == "event" and not ev.all_day
                     and not is_long(ev) and ev.start.date() == d]
            todos = todo_index.get(d, [])
            first_line = lanes_in_col[c]
            room = max_lines - first_line
            overflow = len(todos) + len(timed) > room or hidden[c] > 0
            show = max(0, room - 1) if overflow else room
            cell_bg = t["today_cell"] if d == self.today else t["weekend"] if c in (0, 6) else t["cell"]
            for i, item in enumerate(todos[:show]):
                self._draw_todo_line(cv, item, x0, y0 + header_h + (first_line + i) * line_h, col_w, line_h,
                                     cell_bg)
            first_line += min(len(todos), show)
            more_todos = len(todos) - min(len(todos), show)
            show = max(0, show - len(todos))
            for i, ev in enumerate(timed[:show]):
                ly = y0 + header_h + (first_line + i) * line_h
                tag = self._next_tag()
                tint = min(0.93, t["tint"] + (0.14 if ev.end <= now else 0.07))  # 종일 막대보다 한 단계 옅게
                round_rect(cv, x0 + px(4), ly + px(1), x0 + col_w - px(4), ly + line_h - px(1), px(4),
                           fill=blend(ev.color, cell_bg, tint), outline="", tags=(tag,))
                r = max(2, px(3))
                cv.create_oval(x0 + px(10) - r, ly + line_h / 2 - r, x0 + px(10) + r, ly + line_h / 2 + r,
                               fill=ev.color, outline="", tags=(tag,))
                label = f"{ev.start.hour}:{ev.start.minute:02d} {ev.title}"
                cv.create_text(x0 + px(16), ly + line_h / 2, text=self.fit(label, ev_font, col_w - px(24)),
                               anchor="w", font=ev_font, fill=t["muted"] if ev.end <= now else t["text"],
                               tags=(tag,))
                self._bind_event(cv, tag, ev)
            more = len(timed) - min(show, len(timed)) + hidden[c] + more_todos
            if overflow and more > 0:
                ly = y0 + header_h + (first_line + show) * line_h
                tag = self._next_tag()
                cv.create_text(x0 + px(16), ly + line_h / 2, text=f"+{more}개 더", anchor="w",
                               font=f["small"], fill=t["muted"], tags=(tag,))
                cv.tag_bind(tag, "<Button-1>", lambda e, d=d: self.select_date(d))
        # 오늘: 한눈에 보이게 굵은 테두리 (일정 막대에 가려지지 않게 맨 위에)
        if self.today in days:
            c = days.index(self.today)
            x0, w = wk_w + c * col_w, max(2, px(2.5))
            inset = gap / 2 + w / 2
            round_outline(cv, x0 + inset, y0 + inset, x0 + col_w - inset, y0 + row_h - inset, px(7),
                          t.get("today_ring", t["accent"]), w,
                          state="disabled")  # 보이기만 하고 클릭은 그 아래 할 일 · 일정으로 그대로 가요

    def _todo_index(self) -> dict:
        """달력에 보일 할 일: 남은 할 일은 모두, 끝낸 할 일은 '끝낸 할 일' 설정을 따라요."""
        index: dict = {}
        if TODO_CHIP in (self.cfg.get("hidden_cals") or []) + (self.cfg.get("removed_cals") or []):  # 단추로 숨겼어요
            return index
        _all, done_shown = self._shown_done()
        shown_done_ids = {i["id"] for i in done_shown}
        for item in self.todos.items:
            if not item.get("due") or (item.get("done") and item["id"] not in shown_done_ids):
                continue
            try:
                day = date.fromisoformat(item["due"])
            except ValueError:
                continue
            if day < self.today and not item.get("done") and self.cfg.get("todo_rollover", True):
                day = self.today  # 못 끝낸 할 일은 오늘 칸에서 빨간 글씨로 보여요
            index.setdefault(day, []).append(item)
        for items in index.values():
            items.sort(key=lambda i: (bool(i.get("done")), str(i.get("time") or "99:99"), i.get("created", "")))
        return index

    def _draw_todo_line(self, cv, item: dict, x0: float, ly: float, col_w: float, line_h: float,
                        cell_bg: str) -> None:
        t, f, px = self.t, self.fonts, self.px
        done = bool(item.get("done"))
        color = todo_hex(item.get("color", "")) or TASK_BLUE
        box_tag, text_tag = self._next_tag(), self._next_tag()
        strip = blend(color, cell_bg, min(0.93, t["tint"] + (0.14 if done else 0.07)))
        round_rect(cv, x0 + px(4), ly + px(1), x0 + col_w - px(4), ly + line_h - px(1), px(4), fill=strip, outline="",
                   tags=(text_tag,))
        r = max(3.5, px(4.5))
        cx, cy = x0 + px(8) + r, ly + line_h / 2
        # 손가락으로도 누르기 쉽게 동그라미 둘레를 넓게 잡아요
        cv.create_rectangle(x0 + px(4), ly + px(1), cx + r + px(3), ly + line_h - px(1), fill=strip, outline="",
                            tags=(box_tag,))
        self._task_circle(cv, cx, cy, r, color, done, strip, (box_tag,))
        title = item["text"].splitlines()[0]
        at = parse_time(str(item.get("time") or ""))
        if at:
            title = f"{at.hour}:{at.minute:02d} {title}"
        font = f["event_done"] if done else f["event"]
        cv.create_text(x0 + px(21), ly + line_h / 2, text=self.fit(title, font, col_w - px(29)), anchor="w",
                       font=font, fill=t["muted"] if done else (t["sun"] if str(item.get("due") or "") < self.today.isoformat()
                                                                else t["text"]), tags=(text_tag,))
        action = self.reopen_todo if done else self.complete_todo
        cv.tag_bind(box_tag, "<Button-1>", lambda e, i=item["id"]: self.after(1, lambda: action(i)))
        cv.tag_bind(text_tag, "<Button-1>", lambda e, it=item: self.after(1, lambda: self.open_todo(it)))
        for tag in (box_tag, text_tag):
            cv.tag_bind(tag, "<Double-Button-1>", lambda e: setattr(self, "_event_dbl", True))
            cv.tag_bind(tag, "<Button-3>", lambda e, i=item["id"], dn=done:
                        (setattr(self, "_menu_handled", True), self._todo_menu(e, i, dn)))
            cv.tag_bind(tag, "<Enter>", lambda e: cv.config(cursor="hand2"))
            cv.tag_bind(tag, "<Leave>", lambda e: cv.config(cursor=""))

    def _task_circle(self, cv, cx: float, cy: float, r: float, color: str, done: bool, bg: str, tags) -> None:
        """Google 캘린더의 할 일처럼 동그란 완료 단추 (끝내면 채워지고 흰 체크 표시). 가장자리가 부드러운 그림으로 그려요."""
        size = max(9, int(round(r * 2 + 2)))
        cv.create_image(int(round(cx)), int(round(cy)), image=self._task_icon(size, color, done, bg), tags=tags)

    def _task_icon(self, size: int, color: str, done: bool, bg: str) -> tk.PhotoImage:
        """동그라미(와 체크)를 4배 크기로 계산해서 줄인 그림. 같은 모양은 다시 쓰려고 기억해 둬요."""
        key = (size, color, done, bg)
        cache = self.__dict__.setdefault("_task_icons", {})
        if key in cache:
            return cache[key]
        ss = 4
        n = size * ss
        cx = cy = n / 2
        outer = n / 2 - ss * 0.6
        ring = max(1.5, size * 0.12) * ss
        check_w = max(1.5, size * 0.13) * ss
        pts = [(0.28 * n, 0.53 * n), (0.44 * n, 0.68 * n), (0.73 * n, 0.36 * n)]
        fg, back, white = hex_rgb(color), hex_rgb(bg), (255, 255, 255)

        def near_check(x: float, y: float) -> bool:
            for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
                dx, dy = x2 - x1, y2 - y1
                t_ = max(0.0, min(1.0, ((x - x1) * dx + (y - y1) * dy) / (dx * dx + dy * dy)))
                if (x - x1 - t_ * dx) ** 2 + (y - y1 - t_ * dy) ** 2 <= (check_w / 2) ** 2:
                    return True
            return False

        rows = []
        for py in range(size):
            row = []
            for px_ in range(size):
                acc = [0.0, 0.0, 0.0]
                for sy in range(ss):
                    for sx in range(ss):
                        x, y = px_ * ss + sx + 0.5, py * ss + sy + 0.5
                        d = ((x - cx) ** 2 + (y - cy) ** 2) ** 0.5
                        if done:
                            c = (white if near_check(x, y) else fg) if d <= outer else back
                        else:
                            c = fg if outer - ring <= d <= outer else back
                        acc[0] += c[0]
                        acc[1] += c[1]
                        acc[2] += c[2]
                k = ss * ss
                row.append("#%02x%02x%02x" % (round(acc[0] / k), round(acc[1] / k), round(acc[2] / k)))
            rows.append("{" + " ".join(row) + "}")
        img = tk.PhotoImage(master=self, width=size, height=size)
        img.put(" ".join(rows))
        cache[key] = img
        return img

    def _next_tag(self) -> str:
        self._tag_n += 1
        return f"g{self._tag_n}"

    def render_side(self) -> None:
        if not self.cfg["show_timeline"] or not hasattr(self, "side_title"):
            return
        t, d = self.t, self.selected
        tone = self.tone(d)
        self.side_title.config(text=f"{d.month}월 {d.day}일 {WEEKDAY_FULL[d.weekday()]}",
                               fg=t[tone] if tone != "text" else t["text"])
        parts = [relative_label(d, self.today)]
        if d in self.holidays:
            parts.append(self.holidays[d])
        elif d in self.observances:
            parts.append(self.observances[d])
        if self.cfg["show_lunar"] and lunar_label(d):
            parts.append(f"음력 {lunar_label(d)}")
        self.side_sub.config(text=", ".join(parts))
        self.render_allday()
        self.render_timeline()

    def render_allday(self) -> None:
        cv, t, f, px = self.allday_cv, self.t, self.fonts, self.px
        cv.delete("all")
        W = cv.winfo_width()
        chips = [ev for ev in self.by_day.get(self.selected, [])
                 if ev.kind == "event" and (ev.all_day or is_long(ev))]
        if not chips or W < 40:
            if int(float(cv.cget("height"))) != 1:
                cv.configure(height=1)
            return
        h = f["event"].metrics("linespace") + px(8)
        x = y = 0
        for i, ev in enumerate(chips):
            text = self.fit(ev.title, f["event"], W - px(18))
            w = f["event"].measure(text) + px(18)
            if x > 0 and x + w > W:
                x, y = 0, y + h + px(5)
            tag = f"a{i}"
            round_rect(cv, x, y, x + w, y + h, px(5), fill=blend(ev.color, t["panel"], t["tint"]), outline="",
                       tags=(tag,))
            round_rect(cv, x + px(3), y + px(4), x + px(6), y + h - px(4), px(1.5), fill=ev.color, outline="",
                       tags=(tag,))
            cv.create_text(x + px(10), y + h / 2, text=text, anchor="w", font=f["event"], fill=t["text"], tags=(tag,))
            self._bind_event(cv, tag, ev)
            x += w + px(6)
        height = y + h + px(4)
        if int(float(cv.cget("height"))) != height:
            cv.configure(height=height)

    def render_timeline(self) -> None:
        cv, t, f, px = self.time_cv, self.t, self.fonts, self.px
        cv.delete("all")
        W, Hv = cv.winfo_width(), cv.winfo_height()
        if W < 60 or Hv < 60:
            return
        s_h, e_h = self.cfg["timeline_start"], self.cfg["timeline_end"]
        hour_h = max(px(26), Hv / max(1, e_h - s_h))
        self._hour_h = hour_h
        gutter = f["small"].measure("오후 12시") + px(12)
        cv.configure(scrollregion=(0, 0, W, hour_h * 24), yscrollincrement=max(1, int(hour_h / 2)))
        for h in range(1, 24):
            y = h * hour_h
            cv.create_line(gutter, y, W, y, fill=t["line"])
            cv.create_text(gutter - px(6), y, text=hour_label(h), anchor="e", font=f["small"], fill=t["muted"])

        d = self.selected
        day_start, day_end = local_midnight(d), local_midnight(d + timedelta(days=1))
        items = []
        min_minutes = (f["event_bold"].metrics("linespace") + px(8)) / hour_h * 60  # 제목 한 줄은 꼭 보이게
        for ev in self.by_day.get(d, []):
            if ev.all_day or ev.kind != "event" or is_long(ev):
                continue
            s, e = max(ev.start, day_start), min(ev.end, day_end)
            sm = (s - day_start).total_seconds() / 60
            em = max((e - day_start).total_seconds() / 60, sm + max(25, min_minutes))
            items.append((sm, em, ev))
        for item in self._todo_index().get(d, []):  # 시간 있는 할 일 (Google 캘린더처럼 시간표에도)
            at = parse_time(str(item.get("time") or ""))
            if not at:
                continue
            until = parse_time(str(item.get("end_time") or ""))
            sm = at.hour * 60 + at.minute
            em = until.hour * 60 + until.minute if until and until > at else sm + 30
            items.append((sm, max(em, sm + max(25, min_minutes)), ("todo", item)))
        area_x0, area_w = gutter + px(4), W - gutter - px(6)
        now = datetime.now().astimezone()
        for i, (col, ncols, sm, em, ev) in enumerate(layout_columns(items)):
            x0 = area_x0 + col * area_w / ncols + 1
            x1 = area_x0 + (col + 1) * area_w / ncols - px(2)
            y0, y1 = sm / 60 * hour_h + 1, em / 60 * hour_h - 1
            if isinstance(ev, tuple):
                self._draw_timeline_task(cv, ev[1], x0, x1, y0, y1, f"t{i}")
                continue
            tag = f"t{i}"
            past = ev.end <= now
            fill = blend(ev.color, t["panel"], min(0.9, t["tint"] + (0.12 if past else 0)))
            round_rect(cv, x0, y0, x1, y1, px(6), fill=fill, outline="", tags=(tag,))
            round_rect(cv, x0 + px(3), y0 + px(4), x0 + px(6), y1 - px(4), px(1.5), fill=ev.color, outline="",
                       tags=(tag,))
            lines = [(ev.title, f["event_bold"], t["text"]),
                     (f"{fmt_time(ev.start)} ~ {fmt_time(ev.end)}", f["small"], t["muted"])]
            if ev.location:
                lines.append((ev.location, f["small"], t["muted"]))
            ty = y0 + px(3)
            for j, (text, font, fill_color) in enumerate(lines):
                lh = font.metrics("linespace")
                if j and ty + lh > y1 - px(1):
                    break
                cv.create_text(x0 + px(8), ty, text=self.fit(text, font, x1 - x0 - px(12)), anchor="nw",
                               font=font, fill=t["muted"] if past and not j else fill_color, tags=(tag,))
                ty += lh
            self._bind_event(cv, tag, ev)
        if d == self.today:
            ny = (now.hour * 60 + now.minute) / 60 * hour_h
            cv.create_line(gutter, ny, W, ny, fill=t["now"], width=max(1, px(2)))
            cv.create_image(gutter, ny, image=self.circle(px(9), t["now"], t["panel"]))
        if self._scrolled_for != (d, round(hour_h)):
            target = s_h
            if d == self.today and not s_h <= now.hour < e_h:
                target = max(0, now.hour - 2)
            cv.yview_moveto(max(0.0, target - 0.35) / 24)  # 첫 시각 글자가 잘리지 않게
            self._scrolled_for = (d, round(hour_h))

    def _draw_timeline_task(self, cv, item: dict, x0: float, x1: float, y0: float, y1: float, tag: str) -> None:
        t, f, px = self.t, self.fonts, self.px
        done = bool(item.get("done"))
        color = todo_hex(item.get("color", "")) or TASK_BLUE
        fill = blend(color, t["panel"], min(0.92, t["tint"] + (0.14 if done else 0.04)))
        round_rect(cv, x0, y0, x1, y1, px(6), fill=fill, outline="", tags=(tag,))
        title_font = f["event_done"] if done else f["event_bold"]
        r = max(4, px(6))
        cx, cy = x0 + px(5) + r, y0 + px(3) + title_font.metrics("linespace") / 2
        box_tag = tag + "b"
        cv.create_oval(cx - r - px(3), cy - r - px(3), cx + r + px(3), cy + r + px(3), fill=fill, outline="",
                       tags=(box_tag,))
        self._task_circle(cv, cx, cy, r, color, done, fill, (box_tag,))
        at, until = parse_time(str(item.get("time") or "")), parse_time(str(item.get("end_time") or ""))
        day = date.fromisoformat(item["due"]) if item.get("due") else self.today
        when = fmt_time(datetime.combine(day, at)) + (" ~ " + fmt_time(datetime.combine(day, until)) if until else "")
        lines = [((item.get("text") or "").splitlines()[0], title_font, t["muted"] if done else t["text"]),
                 (when + " · 할 일", f["small"], t["muted"])]
        ty = y0 + px(3)
        for j, (text, font, fg) in enumerate(lines):
            lh = font.metrics("linespace")
            if j and ty + lh > y1 - px(1):
                break
            cv.create_text(cx + r + px(5), ty, text=self.fit(text, font, x1 - cx - r - px(9)), anchor="nw", font=font,
                           fill=fg, tags=(tag,))
            ty += lh
        action = self.reopen_todo if done else self.complete_todo
        cv.tag_bind(box_tag, "<Button-1>", lambda e, i=item["id"]: self.after(1, lambda: action(i)))
        cv.tag_bind(tag, "<Button-1>", lambda e, it=item: self.after(1, lambda: self.open_todo(it)))
        for tg in (tag, box_tag):
            cv.tag_bind(tg, "<Enter>", lambda e: cv.config(cursor="hand2"))
            cv.tag_bind(tg, "<Leave>", lambda e: cv.config(cursor=""))

    def render_status(self) -> None:
        t = self.t
        cursor = ""
        if self.problems:
            text, color, cursor = self.problems[0], ERROR_RED, "hand2"
            if len(self.problems) > 1:
                text += f" 외 {len(self.problems) - 1}건"
        elif self.flash:
            text, color = self.flash, t["text"]
        elif self.syncing:
            text, color = "동기화하는 중…", t["muted"]
        elif self.last_sync:
            text, color = f"{fmt_time(self.last_sync)}에 동기화함", t["muted"]
        else:
            text, color = "", t["muted"]
        self.status_lbl.config(text=self.fit(text, self.fonts["small"], self.px(420)), fg=color, cursor=cursor)


class _Dialog(tk.Toplevel):
    """설정 · 일정 추가 창의 공통 부분"""

    def __init__(self, app: App, title: str):
        super().__init__(app)
        self.app = app
        self.withdraw()
        self.title(title)
        self.resizable(False, False)
        self.attributes("-topmost", True)
        self.bind("<Escape>", lambda e: self.destroy())
        self.outer = ttk.Frame(self, padding=(app.px(18), app.px(14)))
        self.outer.pack(fill="both", expand=True)
        self.use(self.outer)

    def use(self, container: ttk.Frame, row: int = 0) -> None:
        """이후의 section · field · hint를 이 칸에 차례로 놓아요."""
        self.frame, self.row = container, row
        container.columnconfigure(1, weight=1)

    def section(self, text: str) -> None:
        ttk.Label(self.frame, text=text, font=self.app.fonts["side_head"]).grid(
            row=self.row, column=0, columnspan=3, sticky="w",
            pady=(self.app.px(12) if self.row else 0, self.app.px(4)))
        self.row += 1

    def hint(self, text: str) -> None:
        ttk.Label(self.frame, text=text, foreground=HINT_GRAY, font=self.app.fonts["small"],
                  wraplength=self.app.px(410), justify="left").grid(
            row=self.row, column=0, columnspan=3, sticky="w", pady=(0, self.app.px(6)))
        self.row += 1

    def field(self, label: str, widget: tk.Widget, stretch: bool = True) -> tk.Widget:
        ttk.Label(self.frame, text=label).grid(row=self.row, column=0, sticky="w",
                                               padx=(0, self.app.px(12)), pady=self.app.px(3))
        widget.grid(row=self.row, column=1, columnspan=2, sticky="ew" if stretch else "w", pady=self.app.px(3))
        self.row += 1
        return widget

    def check(self, text: str, var: tk.BooleanVar) -> None:
        ttk.Checkbutton(self.frame, text=text, variable=var).grid(
            row=self.row, column=0, columnspan=3, sticky="w", pady=self.app.px(2))
        self.row += 1

    def with_unit(self, make, unit: str) -> ttk.Frame:
        """입력 칸 바로 옆에 단위(일, 분마다)를 붙여요."""
        box = ttk.Frame(self.frame)
        make(box).pack(side="left")
        ttk.Label(box, text=unit).pack(side="left", padx=(self.app.px(6), 0))
        return box

    def message_area(self) -> None:
        self.msg = ttk.Label(self.frame, text="", wraplength=self.app.px(410), justify="left",
                             font=self.app.fonts["small"])
        self.msg.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(self.app.px(10), 0))
        self.row += 1

    def say(self, text: str, error: bool = False) -> None:
        self.msg.config(text=text, foreground=ERROR_RED if error else "#3D4249")

    def show(self) -> None:
        self.update_idletasks()
        w, h = self.winfo_reqwidth(), self.winfo_reqheight()
        app = self.app
        x = app.winfo_rootx() + (app.winfo_width() - w) // 2
        y = app.winfo_rooty() + max(0, (app.winfo_height() - h) // 3)
        x = min(max(0, x), self.winfo_screenwidth() - w)
        y = min(max(0, y), self.winfo_screenheight() - h - app.px(48))
        self.geometry(f"+{x}+{y}")
        self.deiconify()
        self.lift()
        self.focus_force()


class SettingsDialog(_Dialog):
    AUTO = "자동 (Google 기본 캘린더)"

    UPDATE_CHOICES = [("auto", "자동으로 설치"), ("notify", "알려만 주기"), ("off", "끄기")]

    def __init__(self, app: App, tab: str | None = None):
        super().__init__(app, "캘린더 위젯 설정")
        cfg, px = app.cfg, app.px
        style = ttk.Style()
        style.layout("Side.TNotebook.Tab", [])  # 윈도우 기본 탭 줄은 숨기고 왼쪽 메뉴로 골라요
        notebook = ttk.Notebook(self.outer, style="Side.TNotebook")
        notebook.grid(row=0, column=1, columnspan=2, sticky="nsew")
        tabs = {}
        labels = [("google", "Google"), ("more", "iCloud · 구독"), ("events", "일정 · 알림"), ("screen", "화면"),
                  ("colors", "색"), ("meal", "급식 · 시간표"), ("about", "정보")]
        for key, label in labels:
            tabs[key] = ttk.Frame(notebook, padding=(px(14), px(12)))
            notebook.add(tabs[key], text=label)
        self._side_menu(notebook, tabs, labels)

        # Google
        self.use(tabs["google"])
        self.section("Google 캘린더")
        self.google_url = None
        if GOOGLE_CLIENT_ID:
            self.login_status = ttk.Label(self.frame, font=app.fonts["sub_bold"])
            self.login_status.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
            self.row += 1
            self.login_box = ttk.Frame(self.frame)
            self.login_box.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(8)))
            self.row += 1
            self.hint("브라우저가 열리면 아이폰 캘린더에 쓰는 Google 계정을 고르고, 캘린더 권한을 모두 체크한 뒤 "
                      "계속을 눌러 주세요. 로그인 정보는 이 컴퓨터에만 암호화해서 저장돼요.")
            self._render_login()
        if not GOOGLE_CLIENT_ID:
            self.hint("Google 아이디와 비밀번호로 로그인하려면, 처음 한 번 Google Cloud에서 '로그인 정보' 파일을 만들어 "
                      "불러와야 해요. Google은 프로그램이 비밀번호를 직접 받지 못하게 해서, 비밀번호는 Google 화면에 적어요.\n"
                      "1. 'Google Cloud 열기'에서 새 프로젝트를 만들고 Google Calendar API를 사용으로 켜요.\n"
                      "2. Google 인증 플랫폼에서 앱을 '외부'로 만들고, 데이터 액세스에 캘린더 범위 두 개를 넣고, "
                      "대상 → 테스트 사용자에 내 Gmail을 추가해요.\n"
                      "3. 클라이언트 만들기에서 유형을 '데스크톱 앱'으로 만들고 JSON을 내려받아요.\n"
                      "4. 아래 '로그인 정보 파일 불러오기'로 그 파일을 고르면 'Google 계정으로 로그인' 단추가 생겨요.\n"
                      "자세한 순서는 배포_가이드.md의 2단계에 있어요.")
            prep = ttk.Frame(self.frame)
            ttk.Button(prep, text="로그인 정보 파일 불러오기…", command=self._load_google_client).pack(side="left")
            cloud = ttk.Label(prep, text="Google Cloud 열기", foreground=LINK_BLUE, cursor="hand2")
            cloud.pack(side="left", padx=(px(12), 0))
            cloud.bind("<Button-1>", lambda e: webbrowser.open("https://console.cloud.google.com/"))
            prep.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(2), px(6)))
            self.row += 1
        if not GOOGLE_CLIENT_ID or cfg["google_url"]:
            if GOOGLE_CLIENT_ID:
                self.section("연결 코드 방식 (예전 방식)")
                self.hint("위에서 Google 계정으로 로그인하면 이 방식은 쓰지 않아도 돼요.")
            else:
                self.section("연결 코드 방식 (지금 쓰는 방식)" if cfg["google_url"] else "또는 연결 코드 방식")
            self._legacy_google(px)

        # iCloud · 구독
        self.use(tabs["more"])
        self.section("iCloud 캘린더 (선택)")
        self.apple_id = self.field("Apple ID", ttk.Entry(self.frame, width=42))
        self.app_pw = self.field("앱 암호", ttk.Entry(self.frame, width=42, show="•"))
        self.hint("account.apple.com → 로그인 및 보안 → 앱 암호에서 만든 암호예요. "
                  "평소 쓰는 Apple ID 암호는 넣지 마세요.")
        self.section("다른 캘린더 (선택)")
        self.hint("구독 캘린더의 iCal 주소를 한 줄에 하나씩 넣으면 일정을 볼 수 있어요. "
                  "위에서 Google을 연결했다면 Google의 iCal 주소는 지워도 돼요.")
        self.ics = tk.Text(self.frame, width=52, height=2, wrap="none", font=app.fonts["small"],
                           relief="solid", bd=1, highlightthickness=0)
        self.ics.grid(row=self.row, column=0, columnspan=3, sticky="ew")
        self.row += 1
        self.hol_var = tk.BooleanVar(value=cfg["show_holidays"])
        self.check("대한민국 공휴일 표시", self.hol_var)

        # 일정 · 알림
        self.use(tabs["events"])
        self.section("캘린더")
        manage = ttk.Frame(self.frame)
        ttk.Button(manage, text="새 캘린더 만들기…", command=lambda: NewCalendarDialog(app)).pack(side="left")
        ttk.Button(manage, text="캘린더 지우기…", command=lambda: DeleteCalendarDialog(app)).pack(side="left", padx=(px(6), 0))
        manage.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
        self.row += 1
        self.removed_row = ttk.Frame(self.frame)
        self.removed_row.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
        self.row += 1
        self._render_removed()
        links = ttk.Frame(self.frame)
        for text, url in (("Google 캘린더 열기", "https://calendar.google.com/"),
                          ("아이폰에 보이게 하기", "https://calendar.google.com/calendar/syncselect")):
            link = ttk.Label(links, text=text, foreground=LINK_BLUE, cursor="hand2")
            link.pack(side="left", padx=(0, px(14)))
            link.bind("<Button-1>", lambda e, u=url: webbrowser.open(u))
        links.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(2), px(4)))
        self.row += 1
        self.hint("내가 만든 Google 캘린더는 여기서 만들고 지울 수 있어요. 아이폰은 Google의 기본 캘린더만 저절로 "
                  "가져오니, 새로 만든 캘린더는 '아이폰에 보이게 하기'에서 체크하고 저장해 주세요.")
        self.section("알림")
        self.notify_cb = self.field("일정 알림", ttk.Combobox(
            self.frame, state="readonly", width=12, values=[label for _, label in NOTIFY_CHOICES]), stretch=False)
        values = [v for v, _ in NOTIFY_CHOICES]
        self.notify_cb.current(values.index(cfg["notify_minutes"]) if cfg["notify_minutes"] in values else 2)
        self.hint("일정이 시작되기 전에 화면 오른쪽 아래에 알림 창을 띄우고 소리를 내요.")
        self.section("컴퓨터를 켤 때")
        self.boot_var = tk.BooleanVar(value=cfg["boot_summary"])
        self.check("오늘 일정과 할 일을 한눈에 보여 주기", self.boot_var)
        if IS_WINDOWS:
            self.auto_var = tk.BooleanVar(value=get_autostart())
            self.check("윈도우를 시작할 때 위젯 자동 실행", self.auto_var)
            self.hint("컴퓨터를 켤 때 오늘 일정을 보려면 자동 실행도 켜 두세요.")
        self.refresh_var = tk.StringVar(value=str(cfg["refresh_minutes"]))
        self.field("새로고침 간격", self.with_unit(
            lambda box: ttk.Spinbox(box, from_=1, to=60, width=5, textvariable=self.refresh_var), "분마다"),
            stretch=False)

        # 화면
        self.use(tabs["screen"])
        self.section("달력")
        self.weeks_cb = self.field("보이는 주 수", ttk.Combobox(
            self.frame, state="readonly", width=8, values=[f"{n}주" for n in range(1, 9)]), stretch=False)
        self.weeks_cb.current(cfg["weeks"] - 1)
        self.split_var = tk.BooleanVar(value=cfg.get("split_months", True))
        self.check("달이 바뀌면 줄을 나누고 달 이름 보여 주기", self.split_var)
        self.last_week_var = tk.BooleanVar(value=cfg["start_last_week"])
        self.check("지난주부터 보기 (3주 이상일 때)", self.last_week_var)
        self.lunar_var = tk.BooleanVar(value=cfg["show_lunar"])
        self.check("음력 날짜 표시", self.lunar_var)
        self.weeknum_var = tk.BooleanVar(value=cfg["show_week_numbers"])
        self.check("주 번호 표시", self.weeknum_var)
        self.section("오른쪽 패널")
        self.timeline_var = tk.BooleanVar(value=cfg["show_timeline"])
        self.check("시간표와 할 일 보기", self.timeline_var)
        span = ttk.Frame(self.frame)
        self.tl_start = ttk.Combobox(span, state="readonly", width=9, values=[hour_label(h) for h in range(0, 24)])
        self.tl_start.current(cfg["timeline_start"])
        self.tl_start.pack(side="left")
        ttk.Label(span, text="부터").pack(side="left", padx=(px(4), px(10)))
        self.tl_end = ttk.Combobox(span, state="readonly", width=9, values=[hour_label(h) for h in range(1, 25)])
        self.tl_end.current(cfg["timeline_end"] - 1)
        self.tl_end.pack(side="left")
        ttk.Label(span, text="까지").pack(side="left", padx=(px(4), 0))
        self.field("한 화면에 보일 시간", span, stretch=False)
        self.todo_done_cb = self.field("끝낸 할 일", ttk.Combobox(
            self.frame, state="readonly", width=30, values=[label for _, label in TODO_DONE_CHOICES]), stretch=False)
        keys = [k for k, _ in TODO_DONE_CHOICES]
        self.todo_done_cb.current(keys.index(cfg.get("todo_done", "strike")))
        self.hint("숨긴 할 일도 오른쪽 클릭 → '끝낸 할 일 보기'에서 1년 동안 다시 볼 수 있어요.")
        sync_opts = [("", "쓰지 않음 (이 컴퓨터에만)"), ("tasks", "Google Tasks (하위 할 일 · 체크로 끝내기)")] + \
            [("cal:" + c.key, f"'{c.name}' 캘린더에 일정으로 (아이폰 기본 캘린더에 보여요)")
             for c in app.writable_calendars() if c.source == "Google"]
        current = "tasks" if cfg.get("todo_tasks") else ("cal:" + cfg["todo_sync"] if cfg.get("todo_sync") else "")
        if current and current not in [k for k, _ in sync_opts]:
            sync_opts.append((current, "저장해 둔 캘린더 (아직 불러오지 못함)"))
        self.todo_sync_opts = sync_opts
        self.todo_sync_cb = self.field("할 일 맞추기", ttk.Combobox(
            self.frame, state="readonly", width=42, values=[label for _, label in sync_opts]), stretch=False)
        self.todo_sync_cb.current([k for k, _ in sync_opts].index(current))
        if app.service._google_api() is None:
            self.todo_sync_cb.state(["disabled"])
        self.hint("Google Tasks를 고르면 할 일과 하위 할 일이 Google Tasks 앱 · Google 캘린더 앱과 맞춰지고, 체크로 끝낼 수 있어요. "
                  "(시간은 Tasks 메모 끝에 '[시간] 15:30'으로 적어 둬요. 아이폰 기본 캘린더에는 보이지 않아요) "
                  "캘린더를 고르면 날짜 있는 할 일이 그 캘린더에 일정으로 들어가 아이폰 기본 캘린더에서 보여요.")
        mirror_opts = [("", "쓰지 않음")] + [(c.key, f"'{c.name}' 캘린더에 복사") for c in app.writable_calendars()
                                             if c.source == "Google"]
        current_mirror = cfg.get("todo_mirror") or ""
        if current_mirror and current_mirror not in [k for k, _ in mirror_opts]:
            mirror_opts.append((current_mirror, "저장해 둔 캘린더 (아직 불러오지 못함)"))
        self.mirror_opts = mirror_opts
        self.mirror_cb = self.field("아이폰 기본 캘린더에도", ttk.Combobox(
            self.frame, state="readonly", width=30, values=[label for _, label in mirror_opts]), stretch=False)
        self.mirror_cb.current([k for k, _ in mirror_opts].index(current_mirror))
        self.hint("Google Tasks를 쓸 때, 날짜 있는 할 일을 고른 캘린더에 일정으로 복사해서 아이폰 기본 캘린더에서도 보여요. "
                  "'할 일' 캘린더를 따로 만들어 고르는 걸 권해요. 아이폰에서는 보기만 하세요(고치거나 지워도 다시 맞춰져요). "
                  "Google 캘린더 웹에서는 할 일이 두 번 보일 수 있으니 그 캘린더의 체크를 꺼 두세요.")

        def mirror_state(_e=None) -> None:
            tasks = self.todo_sync_opts[max(0, self.todo_sync_cb.current())][0] == "tasks"
            self.mirror_cb.state(["!disabled"] if tasks else ["disabled"])

        self.todo_sync_cb.bind("<<ComboboxSelected>>", mirror_state, add="+")
        mirror_state()
        self.rollover_var = tk.BooleanVar(value=bool(cfg.get("todo_rollover", True)))
        ttk.Checkbutton(self.frame, text="끝내지 못한 할 일은 달력에서 오늘로 넘겨 보여 주기",
                        variable=self.rollover_var).grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(4)))
        self.row += 1
        problem = app.todo_sync_problem() or (
            "Google 계정으로 로그인해야 쓸 수 있어요. 지금은 연결 코드 방식이에요. Google 탭에서 로그인해 주세요."
            if app.service._google_api() is None else "")
        if problem:
            note = ttk.Label(self.frame, text=problem, foreground="#C5221F", wraplength=px(420), justify="left")
            note.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
            self.row += 1
        self.section("글자와 창")
        self.font_opts = [("gyeonggi", "경기천년체 (제목 · 바탕)"), ("system", "맑은 고딕")]
        self.font_cb = self.field("글꼴", ttk.Combobox(self.frame, state="readonly", width=24,
                                                     values=[label for _, label in self.font_opts]), stretch=False)
        self.font_cb.current([k for k, _ in self.font_opts].index(cfg.get("font_style", "gyeonggi")))
        self.scale_cb = self.field("일정 글자 크기", ttk.Combobox(
            self.frame, state="readonly", width=8, values=[f"{p}%" for p in range(80, 151, 10)]), stretch=False)
        self.scale_cb.current((cfg["event_scale"] - 80) // 10)
        alpha_row = ttk.Frame(self.frame)
        self.alpha_var = tk.DoubleVar(value=cfg["opacity"])
        self.alpha_lbl = ttk.Label(alpha_row, width=5)
        ttk.Scale(alpha_row, from_=30, to=100, variable=self.alpha_var, length=px(200),
                  command=self._preview_alpha).pack(side="left")
        self.alpha_lbl.pack(side="left", padx=(px(8), 0))
        self._preview_alpha(cfg["opacity"])
        self.field("불투명도", alpha_row, stretch=False)
        self.lock_var = tk.BooleanVar(value=cfg["locked"])
        self.check("위치와 크기 고정 (움직이지 않게)", self.lock_var)
        ttk.Button(self.frame, text="화면 전체에 맞추기", command=app.fit_to_screen).grid(
            row=self.row, column=0, columnspan=3, sticky="w", pady=(px(6), 0))
        self.row += 1

        # 색
        self.use(tabs["colors"])
        self.section("테마")
        self.theme_cb = self.field("색 묶음", ttk.Combobox(
            self.frame, state="readonly", width=18, values=[label for _, label in THEME_CHOICES]), stretch=False)
        names = [k for k, _ in THEME_CHOICES]
        self.theme_cb.current(names.index(cfg["theme"]) if cfg["theme"] in names else 0)
        self.theme_cb.bind("<<ComboboxSelected>>", lambda e: self._load_swatches())
        self.section("색 하나씩 바꾸기")
        self.hint("네모를 누르면 색을 고를 수 있어요. 바꾼 색은 지금 고른 색 묶음에만 적용돼요.")
        self.swatch_box = ttk.Frame(self.frame)
        self.swatch_box.grid(row=self.row, column=0, columnspan=3, sticky="w")
        self.row += 1
        ttk.Button(self.frame, text="이 색 묶음의 기본 색으로 되돌리기", command=self._reset_colors).grid(
            row=self.row, column=0, columnspan=3, sticky="w", pady=(px(10), 0))
        self.row += 1
        self.color_overrides = {k: dict(v) for k, v in (cfg.get("colors") or {}).items() if isinstance(v, dict)}
        self._load_swatches()

        # 정보 · 업데이트
        # 급식
        self.use(tabs["meal"])
        self.section("우리 학교 급식")
        self.school_lbl = ttk.Label(self.frame, font=app.fonts["sub_bold"])
        self.school_lbl.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
        self.row += 1
        self._show_school()
        pick = ttk.Frame(self.frame)
        pick.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
        self.row += 1
        ttk.Button(pick, text="학교 찾기…", command=lambda: SchoolDialog(app, on_done=self._show_school)).pack(side="left")
        self.hint("위쪽 아이콘 줄의 밥그릇 모양을 누르면 고른 날의 급식이 떠요. 메뉴는 나이스 교육정보 개방 포털에서 받아 와요.")
        self.section("나이스 인증키 (선택)")
        self.neis_key_e = self.field("인증키", ttk.Entry(self.frame, width=36))
        self.neis_key_e.insert(0, cfg.get("neis_key", ""))
        self.hint("없어도 급식은 잘 보여요. 학교 찾기 결과가 5개까지만 나와서 불편하면 open.neis.go.kr에서 무료로 받아 넣으세요.")
        self.section("시간표")
        self.timetable_e = self.field("주소", ttk.Entry(self.frame, width=44))
        self.timetable_e.insert(0, cfg.get("timetable_url", ""))
        self.hint("위쪽 아이콘 줄에서 밥그릇 오른쪽의 표 모양을 누르면 이 주소가 브라우저로 열려요.")

        self.use(tabs["about"])
        self.section("캘린더 위젯")
        ttk.Label(self.frame, text=f"지금 쓰는 버전: {VERSION}").grid(row=self.row, column=0, columnspan=3,
                                                                  sticky="w", pady=(0, px(6)))
        self.row += 1
        self.update_cb = None
        if UPDATE_REPO and is_frozen():
            self.update_cb = self.field("업데이트", ttk.Combobox(
                self.frame, state="readonly", width=14, values=[label for _, label in self.UPDATE_CHOICES]),
                stretch=False)
            modes = [m for m, _ in self.UPDATE_CHOICES]
            self.update_cb.current(modes.index(cfg.get("update_mode", "auto")))
            self.hint("자동으로 설치하면 새 버전이 나왔을 때 위젯이 잠깐 닫혔다가 새 버전으로 다시 켜져요.")
            row = ttk.Frame(self.frame)
            row.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(4), 0))
            self.row += 1
            self.update_btn = ttk.Button(row, text="지금 확인", command=self.check_update)
            self.update_btn.pack(side="left")
            self.update_msg = ttk.Label(row, text="", font=app.fonts["small"], wraplength=px(300))
            self.update_msg.pack(side="left", padx=(px(10), 0))
        else:
            self.hint("설치 파일로 설치한 위젯은 새 버전이 나오면 업데이트를 받을 수 있어요.")

        # 아래쪽: 결과 메시지와 버튼
        self.use(self.outer, row=1)
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(12), 0))
        self.test_btn = ttk.Button(buttons, text="연결 테스트", command=self.test)
        self.test_btn.pack(side="left")
        ttk.Button(buttons, text="취소", command=self.cancel).pack(side="right")
        ttk.Button(buttons, text="저장", command=self.save).pack(side="right", padx=(0, px(6)))
        self.protocol("WM_DELETE_WINDOW", self.cancel)

        self.apple_id.insert(0, cfg["apple_id"])
        self.app_pw.insert(0, unprotect(cfg["app_password"]))
        self.ics.insert("1.0", "\n".join(cfg["ics_urls"]))
        if tab in tabs:
            notebook.select(tabs[tab])
        self.show()

    def check_update(self) -> None:
        self.update_btn.state(["disabled"])
        self.update_msg.config(text="확인하는 중…", foreground="#3D4249")
        self.app.check_updates(manual=True, on_done=self._update_checked)

    def _update_checked(self, info, error) -> None:
        if not self.winfo_exists():
            return
        self.update_btn.state(["!disabled"])
        if error is not None:
            self.update_msg.config(text=str(error), foreground=ERROR_RED)
        elif info is None:
            self.update_msg.config(text="이미 가장 새 버전이에요.", foreground="#1E7B45")
        else:
            self.update_msg.config(text=f"새 버전 {info['version']}이 있어요.", foreground="#3D4249")
            self.update_btn.config(text="지금 업데이트", command=lambda: self.app.install_update(info))

    def _theme_key(self) -> str:
        return THEME_CHOICES[max(0, self.theme_cb.current())][0]

    def _palette(self) -> dict:
        key = self._theme_key()
        base = dict(THEMES["dark" if key == "system" and windows_dark_mode() else
                           "light" if key == "system" else key])
        base.update(self.color_overrides.get(key, {}))
        return base

    def _load_swatches(self) -> None:
        for w in self.swatch_box.winfo_children():
            w.destroy()
        palette = self._palette()
        px = self.app.px
        for i, (key, label) in enumerate(COLOR_KEYS):
            cell = ttk.Frame(self.swatch_box)
            cell.grid(row=i // 2, column=i % 2, sticky="w", padx=(0, px(18)), pady=px(3))
            swatch = tk.Label(cell, bg=palette[key], width=3, relief="solid", bd=1, cursor="hand2")
            swatch.pack(side="left")
            swatch.bind("<Button-1>", lambda e, k=key: self._pick_color(k))
            ttk.Label(cell, text=label, width=12).pack(side="left", padx=(px(8), 0))

    def _pick_color(self, key: str) -> None:
        from tkinter import colorchooser
        current = self._palette()[key]
        _rgb, chosen = colorchooser.askcolor(color=current, parent=self, title="색 고르기")
        if chosen:
            self.color_overrides.setdefault(self._theme_key(), {})[key] = chosen.upper()
            self._load_swatches()

    def _reset_colors(self) -> None:
        self.color_overrides.pop(self._theme_key(), None)
        self._load_swatches()

    def _preview_alpha(self, value) -> None:
        pct = int(round(float(value) / 10) * 10)
        self.alpha_lbl.config(text=f"{pct}%")
        self.app.attributes("-alpha", pct / 100)

    def _slot_options(self, current: str, index: int) -> list[tuple[str, str]]:
        auto = self.app.slot_calendar(index, auto=True)
        options = [("", f"자동: {auto.name}" if auto else "자동으로 고르기")] + \
            [(c.key, c.label) for c in self.app.event_calendars()]
        if current and current not in [k for k, _ in options]:
            options.append((current, "저장해 둔 캘린더 (아직 불러오지 못함)"))
        return options

    def _calendar_options(self) -> list[tuple[str, str]]:
        options = [("", self.AUTO)] + [(c.key, c.label) for c in self.app.event_calendars()]
        current = self.app.cfg.get("default_calendar", "")
        if current and current not in [k for k, _ in options]:
            options.append((current, "저장해 둔 캘린더 (아직 불러오지 못함)"))
        return options

    def _render_removed(self) -> None:
        """목록에서 숨긴 캘린더와 '다시 보이기' 단추"""
        for w in self.removed_row.winfo_children():
            w.destroy()
        removed = self.app.removed_entries()
        if not removed:
            ttk.Label(self.removed_row, text="목록에서 숨긴 캘린더: 없어요", foreground=HINT_GRAY).pack(side="left")
            return
        ttk.Label(self.removed_row, text="목록에서 숨긴 캘린더").pack(side="left", padx=(0, self.app.px(8)))
        combo = ttk.Combobox(self.removed_row, state="readonly", width=18, values=[n for _k, n in removed])
        combo.current(0)
        combo.pack(side="left")

        def restore() -> None:
            self.app.restore_to_list(removed[max(0, combo.current())][0])
            self._render_removed()

        ttk.Button(self.removed_row, text="다시 보이기", command=restore).pack(side="left", padx=(self.app.px(6), 0))

    def _side_menu(self, notebook, tabs: dict, labels: list) -> None:
        """설정 창 왼쪽 메뉴: 고른 항목은 진한 남색에 흰 글씨, 마우스를 올리면 옅게 칠해져요."""
        px = self.app.px
        bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        family = tkfont.nametofont("TkDefaultFont").actual("family")
        f_on = tkfont.Font(self, family=family, size=10, weight="bold")
        f_off = tkfont.Font(self, family=family, size=10)
        self._side_fonts = (f_on, f_off)
        width = max(f_on.measure(label) for _k, label in labels) + px(36)
        row_h, top = px(36), px(2)
        cv = tk.Canvas(self.outer, width=width, height=top + row_h * len(labels), bg=bg, highlightthickness=0)
        cv.grid(row=0, column=0, sticky="nw", padx=(0, px(10)))
        state = {"hover": None}

        def current() -> str | None:
            chosen = notebook.select()
            return next((k for k, frame in tabs.items() if str(frame) == chosen), None)

        def key_at(y: float) -> str | None:
            i = int((y - top) // row_h)
            return labels[i][0] if 0 <= i < len(labels) else None

        def draw() -> None:
            cv.delete("all")
            now = current()
            for i, (key, label) in enumerate(labels):
                y0, y1 = top + i * row_h, top + (i + 1) * row_h - px(4)
                on = key == now
                if on or state["hover"] == key:
                    round_rect(cv, 1, y0, width - 1, y1, px(8), fill="#2D4B7A" if on else "#DEDBD4", outline="")
                cv.create_text(px(16), (y0 + y1) / 2, text=label, anchor="w", font=f_on if on else f_off,
                               fill="#FFFFFF" if on else "#3C4043")

        def motion(e) -> None:
            key = key_at(e.y)
            hover = key if key != current() else None
            if hover != state["hover"]:
                state["hover"] = hover
                cv.config(cursor="hand2" if hover else "")
                draw()

        def leave(_e) -> None:
            state["hover"] = None
            cv.config(cursor="")
            draw()

        def click(e) -> None:
            key = key_at(e.y)
            if key:
                notebook.select(tabs[key])

        cv.bind("<Motion>", motion)
        cv.bind("<Leave>", leave)
        cv.bind("<Button-1>", click)
        notebook.bind("<<NotebookTabChanged>>", lambda e: (state.update(hover=None), draw()), add="+")
        draw()

    def _show_school(self) -> None:
        if not hasattr(self, "school_lbl") or not self.school_lbl.winfo_exists():
            return
        school = self.app.cfg.get("school") or {}
        self.school_lbl.config(text=f"{school['name']} ({school.get('office_name', '')})" if school.get("name")
                               else "아직 학교를 고르지 않았어요")

    def _load_google_client(self) -> None:
        from tkinter import filedialog
        path = filedialog.askopenfilename(parent=self, title="Google Cloud에서 내려받은 JSON 파일 고르기",
                                          filetypes=[("JSON 파일", "*.json"), ("모든 파일", "*.*")])
        if not path:
            return
        try:
            client_id, secret = read_google_client_file(path)
        except SyncError as exc:
            self.say(str(exc), error=True)
            return
        self.app.cfg.update({"google_client_id": client_id, "google_client_secret": protect(secret)})
        self.app.save()
        use_google_client(client_id, secret)
        app = self.app
        self.destroy()
        app.open_settings("google")  # 다시 열면 'Google 계정으로 로그인' 단추가 보여요

    def _legacy_google(self, px) -> None:
        self.hint("내 Google 계정에 작은 연결 코드를 한 번 설치하면 위젯에서 Google 일정을 보고 추가할 수 있어요.\n"
                  "1. 아래 '연결 코드 복사'를 눌러요.\n"
                  "2. script.google.com에서 새 프로젝트를 만들고, 원래 있던 코드를 지운 뒤 붙여 넣고 저장해요.\n"
                  "3. 배포 → 새 배포에서 유형은 '웹 앱', 실행은 '나', 액세스는 '모든 사용자'로 배포하고 권한을 허용해요.\n"
                  "4. 화면에 나온 웹 앱 URL을 아래 칸에 붙여 넣어요.")
        tools = ttk.Frame(self.frame)
        ttk.Button(tools, text="연결 코드 복사", command=self.copy_code).pack(side="left")
        link = ttk.Label(tools, text="script.google.com 열기", foreground=LINK_BLUE, cursor="hand2")
        link.pack(side="left", padx=(px(12), 0))
        link.bind("<Button-1>", lambda e: webbrowser.open("https://script.google.com/"))
        tools.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(0, px(6)))
        self.row += 1
        self.google_url = self.field("웹 앱 URL", ttk.Entry(self.frame, width=42))
        self.google_url.insert(0, self.app.cfg["google_url"])

    def _render_login(self) -> None:
        px = self.app.px
        for w in self.login_box.winfo_children():
            w.destroy()
        email = self.app.cfg.get("google_email", "") if self.app.cfg.get("google_refresh") else ""
        if email:
            self.login_status.config(text=f"{email} 계정으로 연결돼 있어요", foreground="#1E7B45")
            ttk.Button(self.login_box, text="다른 계정으로 로그인", command=self.login).pack(side="left")
            ttk.Button(self.login_box, text="로그아웃", command=self.logout).pack(side="left", padx=(px(6), 0))
        else:
            self.login_status.config(text="아직 로그인하지 않았어요", foreground=HINT_GRAY)
            ttk.Button(self.login_box, text="Google 계정으로 로그인", command=self.login).pack(side="left")

    def login(self) -> None:
        self.say("브라우저에서 로그인을 기다리는 중이에요…")
        self.app.google_sign_in(on_done=self._logged_in)

    def _logged_in(self, result, error) -> None:
        if not self.winfo_exists():
            return
        if error is not None:
            self.say(str(error), error=True)
            return
        note = "" if result["can_write"] else " (일정 추가 권한이 빠져서 보기만 할 수 있어요)"
        self.say(f"{result['email']} 계정으로 연결됐어요. 일정을 불러오고 있어요.{note}")
        self._render_login()

    def logout(self) -> None:
        self.app.google_sign_out()
        self._render_login()
        self.say("로그아웃했어요.")

    def copy_code(self) -> None:
        code = GOOGLE_SCRIPT.replace("__TOKEN__", self.app.google_token(create=True))
        self.clipboard_clear()
        self.clipboard_append(code)
        self.update()
        self.say("연결 코드를 복사했어요. script.google.com의 새 프로젝트에 붙여 넣어 주세요.")

    def _read(self):
        google_url = self.google_url.get().strip() if self.google_url is not None else self.app.cfg["google_url"]
        if google_url and not re.match(r"^https?://\S+/exec/?$", google_url):
            self.say("웹 앱 URL은 https://script.google.com/ 으로 시작하고 /exec 로 끝나야 해요.", error=True)
            return None
        if google_url and not self.app.google_token():
            self.say("먼저 '연결 코드 복사'를 눌러 연결 코드를 Google에 설치해 주세요.", error=True)
            return None
        apple_id = self.apple_id.get().strip()
        password = re.sub(r"\s+", "", self.app_pw.get())
        urls = [u.strip() for u in self.ics.get("1.0", "end").splitlines() if u.strip()]
        for url in urls:
            if not re.match(r"^(https?|webcal)://", url, re.I):
                self.say(f"iCal 주소는 https:// 로 시작해야 해요: {url[:50]}", error=True)
                return None
        if bool(apple_id) != bool(password):
            self.say("Apple ID와 앱 암호를 둘 다 넣어 주세요.", error=True)
            return None
        return google_url, apple_id, password, urls

    def test(self) -> None:
        values = self._read()
        if values is None:
            return
        google_url, apple_id, password, urls = values
        self.test_btn.state(["disabled"])
        self.say("확인하는 중…")
        self.app.worker.submit(CalendarService.test_sources, unprotect(self.app.cfg.get("google_refresh", "")),
                               google_url, self.app.google_token(), apple_id, password, urls,
                               self.app.cfg.get("caldav_url") or ICLOUD_CALDAV, callback=self._tested)

    def _tested(self, result, error) -> None:
        if not self.winfo_exists():
            return
        self.test_btn.state(["!disabled"])
        if error is not None:
            self.say(f"확인하지 못했어요: {error}", error=True)
            return
        ok, lines = result
        self.say("\n".join(lines), error=not ok)

    def save(self) -> None:
        values = self._read()
        if values is None:
            return
        google_url, apple_id, password, urls = values
        try:
            refresh = min(60, max(1, int(float(self.refresh_var.get()))))
        except (TypeError, ValueError):
            refresh = self.app.cfg["refresh_minutes"]
        start_h = self.tl_start.current()
        end_h = max(start_h + 1, self.tl_end.current() + 1)
        cfg = self.app.cfg
        old = dict(cfg)
        cfg.update({
            "google_url": google_url,
            "apple_id": apple_id,
            "app_password": protect(password),
            "ics_urls": urls,
            "show_holidays": bool(self.hol_var.get()),
            "notify_minutes": NOTIFY_CHOICES[max(0, self.notify_cb.current())][0],
            "boot_summary": bool(self.boot_var.get()),
            "refresh_minutes": refresh,
            "weeks": self.weeks_cb.current() + 1,
            "split_months": bool(self.split_var.get()),
            "start_last_week": bool(self.last_week_var.get()),
            "show_lunar": bool(self.lunar_var.get()),
            "show_week_numbers": bool(self.weeknum_var.get()),
            "show_timeline": bool(self.timeline_var.get()),
            "todo_done": TODO_DONE_CHOICES[max(0, self.todo_done_cb.current())][0],
            "todo_tasks": self.todo_sync_opts[max(0, self.todo_sync_cb.current())][0] == "tasks",
            "todo_sync": (lambda k: k[4:] if k.startswith("cal:") else "")(
                self.todo_sync_opts[max(0, self.todo_sync_cb.current())][0]),
            "todo_rollover": bool(self.rollover_var.get()),
            "todo_mirror": self.mirror_opts[max(0, self.mirror_cb.current())][0],
            "neis_key": self.neis_key_e.get().strip(),
            "font_style": self.font_opts[max(0, self.font_cb.current())][0],
            "timetable_url": self.timetable_e.get().strip(),
            "timeline_start": start_h,
            "timeline_end": end_h,
            "event_scale": 80 + 10 * max(0, self.scale_cb.current()),
            "opacity": int(round(float(self.alpha_var.get()) / 10) * 10),
            "locked": bool(self.lock_var.get()),
            "theme": self._theme_key(),
            "colors": self.color_overrides,
        })
        if self.update_cb is not None:
            cfg["update_mode"] = self.UPDATE_CHOICES[max(0, self.update_cb.current())][0]
        self.app.lock_var.set(cfg["locked"])
        if IS_WINDOWS:
            try:
                set_autostart(bool(self.auto_var.get()))
            except OSError as exc:
                log_error(f"자동 실행 설정 실패: {exc}")
        self.destroy()
        self.app.apply_settings(old)

    def cancel(self) -> None:
        self.app.attributes("-alpha", self.app.cfg["opacity"] / 100)
        self.destroy()


EMAIL_RE = re.compile(r"[^@\s,;<>]+@[^@\s,;<>]+\.[^@\s,;<>]+")


class AttachMixin:
    """일정 창 · 할 일 창의 첨부 파일: [파일 넣기…], 끌어다 놓기, 목록(열기 · 빼기)"""

    def _build_attach_row(self, drop_widget) -> None:
        px = self.app.px
        attach = ttk.Frame(self.frame)
        self.attach_btn = ttk.Button(attach, text="파일 넣기…", command=self._pick_files)
        self.attach_btn.pack(side="left")
        self.attach_hint = ttk.Label(attach, text="설명 칸으로 이미지 · PDF 같은 파일을 끌어다 놓아도 돼요",
                                     foreground=HINT_GRAY, font=self.app.fonts["small"])
        self.attach_hint.pack(side="left", padx=(px(8), 0))
        self.field("첨부", attach, stretch=False)
        self.attach_list = ttk.Frame(self.frame)
        self.attach_list.grid(row=self.row, column=1, columnspan=2, sticky="w")
        self.row += 1
        self.attachments, self.new_files = [], []
        self.attach_enabled, self.attach_note = True, ""
        if not enable_file_drop(drop_widget, self._add_files):
            self.attach_hint.config(text="이미지 · PDF 같은 파일을 붙여요")

    def _pick_files(self) -> None:
        from tkinter import filedialog
        if self.attach_enabled:
            self._add_files(list(filedialog.askopenfilenames(parent=self, title="붙일 파일 고르기")))

    def _add_files(self, paths: list) -> None:
        if not self.attach_enabled:
            self.say(self.attach_note or "여기에는 파일을 붙일 수 없어요.", error=True)
            return
        for path in paths:
            if not os.path.isfile(path):
                continue
            if os.path.getsize(path) > ATTACH_MAX_MB * 1024 * 1024:
                self.say(f"'{os.path.basename(path)}'은 {ATTACH_MAX_MB}MB보다 커서 붙일 수 없어요.", error=True)
                continue
            if path not in self.new_files:
                self.new_files.append(path)
        self._render_attachments()

    def _render_attachments(self) -> None:
        for w in self.attach_list.winfo_children():
            w.destroy()
        rows = [(a.get("title") or "파일", self.attachments, a) for a in self.attachments] + \
               [(os.path.basename(p) + "  (저장할 때 올려요)", self.new_files, p) for p in self.new_files]
        for text, bucket, ref in rows:
            row = ttk.Frame(self.attach_list)
            row.pack(anchor="w")
            ttk.Label(row, text="• " + (text if len(text) <= 44 else text[:43] + "…")).pack(side="left")
            if bucket is self.attachments and ref.get("fileUrl"):
                opener = ttk.Label(row, text="열기", foreground=LINK_BLUE, cursor="hand2")
                opener.pack(side="left", padx=(self.app.px(8), 0))
                opener.bind("<Button-1>", lambda e, u=ref["fileUrl"]: webbrowser.open(u))
            out = ttk.Label(row, text="빼기", foreground=LINK_BLUE, cursor="hand2")
            out.pack(side="left", padx=(self.app.px(8), 0))
            out.bind("<Button-1>", lambda e, bk=bucket, r=ref: (bk.remove(r), self._render_attachments()))

    def _set_attach(self, on: bool, note: str = "") -> None:
        self.attach_enabled, self.attach_note = on, note
        self.attach_btn.state(["!disabled"] if on else ["disabled"])

    def _upload_progress(self, n: int, total: int, name: str) -> None:
        self.app.worker.results.put((lambda r, e: self.winfo_exists() and self.say(f"파일을 올리는 중… {r[0]}/{r[1]} ({r[2]})"),
                                     (n, total, name), None))


class AddEventDialog(AttachMixin, _Dialog):
    TODO_LABEL = "할 일 (할 일 목록에 넣기)"
    """일정 추가 창. event를 주면 그 일정을 고치는 창이 돼요."""
    TIMES = [f"{h:02d}:{m:02d}" for h in range(24) for m in (0, 30)]

    def __init__(self, app: App, day: date, start_time: dt_time | None = None, event: Event | None = None, prefill: dict | None = None):
        self.event = event
        editing = event is not None
        super().__init__(app, "일정 고치기" if editing else "일정 추가")
        px = app.px
        self.cals = app.event_calendars()
        if editing:
            # 고칠 때는 Google 캘린더끼리만 옮길 수 있어요
            self.cals = [c for c in self.cals if c.source == "Google"]
        if not editing:
            kind_tabs(self, "event", self._switch_kind)
        values = [c.label for c in self.cals]
        self.cal_cb = ttk.Combobox(self.frame, state="readonly", width=34, values=values, height=15)
        keys = [c.key for c in self.cals]
        if editing:
            index = keys.index(event.cal_key) if event.cal_key in keys else 0
        else:  # 지난번에 고른 캘린더로 열어요
            last = app.cfg.get("last_calendar") or ""
            personal = app.slot_calendar(1)
            index = (keys.index(last) if last in keys
                     else keys.index(personal.key) if personal and personal.key in keys else 0)
        if values:
            self.cal_cb.current(min(index, len(values) - 1))
        self.cal_cb.bind("<<ComboboxSelected>>", lambda e: self._update_where())
        ttk.Label(self.frame, text="캘린더").grid(row=self.row, column=0, sticky="w", padx=(0, px(10)))
        self.cal_cb.grid(row=self.row, column=1, columnspan=2, sticky="w", pady=px(3))
        self.row += 1
        where = ttk.Frame(self.frame)
        self.swatch = tk.Label(where, width=2, bd=0)
        self.swatch.pack(side="left", padx=(0, px(6)))
        self.where = ttk.Label(where, foreground=HINT_GRAY, font=app.fonts["small"], wraplength=px(380),
                               justify="left")
        self.where.pack(side="left")
        where.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(2), px(8)))
        self.row += 1
        self._build_colors()

        self.title_e = self.field("제목", ttk.Entry(self.frame, width=36))
        dates = ttk.Frame(self.frame)
        self.date_e = ttk.Entry(dates, width=11)
        self.date_e.pack(side="left")
        ttk.Button(dates, text="달력", width=5, command=lambda: self._pick(self.date_e)).pack(
            side="left", padx=(px(3), px(6)))
        ttk.Label(dates, text="~").pack(side="left", padx=(0, px(6)))
        self.end_date_e = ttk.Entry(dates, width=11)
        self.end_date_e.pack(side="left")
        self.end_date_btn = ttk.Button(dates, text="달력", width=5, command=lambda: self._pick(self.end_date_e))
        self.end_date_btn.pack(side="left", padx=(px(3), 0))
        self.allday_var = tk.BooleanVar(value=False)
        self.allday_cb = ttk.Checkbutton(dates, text="종일", variable=self.allday_var, command=self._toggle_allday)
        self.allday_cb.pack(side="left", padx=(px(12), 0))
        self.field("날짜", dates, stretch=False)
        self.date_e.insert(0, day.isoformat())
        self.end_date_e.insert(0, day.isoformat())
        self.date_e.bind("<FocusOut>", lambda e: self._keep_end_after_start())

        times = ttk.Frame(self.frame)
        self.start_cb = TimeEntry(times, on_change=self._start_changed)
        self.start_cb.pack(side="left")
        ttk.Label(times, text="부터").pack(side="left", padx=(px(4), px(10)))
        self.end_cb = TimeEntry(times)
        self.end_cb.pack(side="left")
        ttk.Label(times, text="까지").pack(side="left", padx=(px(4), 0))
        ttk.Label(times, text="직접 적거나 ↑↓ · 휠로 5분씩", foreground=HINT_GRAY,
                  font=app.fonts["small"]).pack(side="left", padx=(px(10), 0))
        self.field("시간", times, stretch=False)
        start, end = self._default_times(day, start_time)
        self.start_cb.set(start)
        self.end_cb.set(end)
        self._start_seen = parse_time(start)

        self.loc_e = self.field("장소", ttk.Entry(self.frame, width=36))
        self.desc_t = self.field("설명", tk.Text(self.frame, width=36, height=3, wrap="word", font="TkTextFont",
                                                relief="solid", bd=1, highlightthickness=0, padx=px(4), pady=px(3)))
        self.desc_t.bind("<Return>", self._newline)  # 설명 칸에서는 Enter가 줄바꿈이에요
        self.desc_t.bind("<Tab>", lambda e: (e.widget.tk_focusNext().focus_set(), "break")[1])
        attach = ttk.Frame(self.frame)
        self.attach_btn = ttk.Button(attach, text="파일 넣기…", command=self._pick_files)
        self.attach_btn.pack(side="left")
        self.attach_hint = ttk.Label(attach, text="설명 칸으로 이미지 · PDF 같은 파일을 끌어다 놓아도 돼요",
                                     foreground=HINT_GRAY, font=app.fonts["small"])
        self.attach_hint.pack(side="left", padx=(px(8), 0))
        self.field("첨부", attach, stretch=False)
        self.attach_list = ttk.Frame(self.frame)
        self.attach_list.grid(row=self.row, column=1, columnspan=2, sticky="w")
        self.row += 1
        self.attachments, self.new_files = [], []
        self.attach_enabled, self.attach_note = True, ""
        if not enable_file_drop(self.desc_t, self._add_files):
            self.attach_hint.config(text="이미지 · PDF 같은 파일을 일정에 붙여요")

        self.guest_e = self.field("참석자", ttk.Entry(self.frame, width=36))
        self.modify_var = tk.BooleanVar(value=False)
        self.modify_cb = ttk.Checkbutton(self.frame, text="참석자가 일정을 수정할 수 있어요", variable=self.modify_var)
        self.modify_cb.grid(row=self.row, column=1, columnspan=2, sticky="w", pady=(0, px(2)))
        self.row += 1
        self.guest_note = ttk.Label(self.frame, foreground=HINT_GRAY, font=app.fonts["small"], wraplength=px(380),
                                    justify="left")
        self.guest_note.grid(row=self.row, column=1, columnspan=2, sticky="w")
        self.row += 1
        if editing and event.ref.get("recurring"):
            self.hint("반복 일정이라 이 날 일정만 고쳐져요.")

        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="취소", command=self.destroy).pack(side="right")
        self.save_btn = ttk.Button(buttons, text="저장" if editing else "추가", command=self.save)
        self.save_btn.pack(side="right", padx=(0, px(6)))
        if editing:
            self.delete_btn = ttk.Button(buttons, text="일정 지우기", command=self.delete)
            self.delete_btn.pack(side="left")
            self._fill(event)
        self.bind("<Return>", lambda e: self.save())
        self._choice_changed()
        if prefill:
            self._apply_prefill(prefill)
        self.show()
        self.title_e.focus_set()

    # ── 색 고르기: 기본(캘린더 색) · Google 24색 · 직접 고르기 ──
    def _build_colors(self) -> None:
        px = self.app.px
        self.color = ""
        self.color_enabled = True
        self._color_bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        bg = self._color_bg
        box = ttk.Frame(self.frame)
        self.default_cv = tk.Canvas(box, width=px(52), height=px(42), bg=bg, highlightthickness=0, cursor="hand2")
        self.default_cv.grid(row=0, column=0, rowspan=2, padx=(0, px(6)))
        self.default_cv.bind("<Button-1>", lambda e: self._pick_color(""))
        Tooltip(self.default_cv, "기본: 캘린더 색을 따라가요", self.app)
        self.color_cvs = {}
        for i, (hx, name) in enumerate(GOOGLE_EVENT_COLORS):
            cv = tk.Canvas(box, width=px(21), height=px(21), bg=bg, highlightthickness=0, cursor="hand2")
            cv.grid(row=i // 12, column=1 + i % 12)
            cv.bind("<Button-1>", lambda e, c=hx: self._pick_color(c))
            Tooltip(cv, name, self.app)
            self.color_cvs[hx] = cv
        self.custom_cv = tk.Canvas(box, width=px(21), height=px(21), bg=bg, highlightthickness=0)
        self.custom_cv.grid(row=0, column=13, padx=(px(8), 0))
        self.custom_btn = ttk.Button(box, text="직접…", width=5, command=self._custom_color)
        self.custom_btn.grid(row=1, column=13, padx=(px(8), 0))
        self.field("색", box, stretch=False)
        self.color_note = ttk.Label(self.frame, foreground=HINT_GRAY, font=self.app.fonts["small"],
                                    wraplength=px(380), justify="left")
        self.color_note.grid(row=self.row, column=1, columnspan=2, sticky="w", pady=(0, px(4)))
        self.row += 1

    def _draw_colors(self) -> None:
        px, bg, on = self.app.px, self._color_bg, self.color_enabled
        c, r = px(10.5), px(7)
        for hx, cv in self.color_cvs.items():
            cv.delete("all")
            if on and hx == self.color:
                cv.create_oval(c - px(10), c - px(10), c + px(10), c + px(10), outline=hx, width=max(2, px(2)))
            cv.create_oval(c - r, c - r, c + r, c + r, fill=hx if on else blend(hx, bg, 0.7), outline="")
        cal = self._target()
        colors = self.app.cfg.get("cal_colors") or {}
        cal_color = colors.get(cal.key, cal.color) if cal else HINT_GRAY
        d = self.default_cv
        d.delete("all")
        w, h = int(d["width"]), int(d["height"])
        chosen = on and not self.color
        round_rect(d, 1, h / 2 - px(12), w - 2, h / 2 + px(12), px(8), fill=bg,
                   outline="#1A73E8" if chosen else "#B9BEC5", width=2 if chosen else 1)
        d.create_oval(px(8), h / 2 - px(5), px(18), h / 2 + px(5), fill=cal_color if on else blend(cal_color, bg, 0.7),
                      outline="")
        d.create_text(px(22), h / 2, text="기본", anchor="w", fill="#202124" if on else HINT_GRAY,
                      font=("TkDefaultFont", 9))
        cc = self.custom_cv
        cc.delete("all")
        if on and self.color and self.color not in self.color_cvs:  # 직접 고른 색
            cc.create_oval(c - px(10), c - px(10), c + px(10), c + px(10), outline=self.color, width=max(2, px(2)))
            cc.create_oval(c - r, c - r, c + r, c + r, fill=self.color, outline="")
        else:
            cc.create_oval(c - r, c - r, c + r, c + r, outline="#B9BEC5", dash=(2, 2))
        self.custom_btn.state(["!disabled"] if on else ["disabled"])

    def _pick_color(self, color: str) -> None:
        if self.color_enabled:
            self.color = color
            self._draw_colors()
            if self._todo_mode():
                self.swatch.config(bg=color or "#F6BF26")

    def _custom_color(self) -> None:
        from tkinter import colorchooser
        if not self.color_enabled:
            return
        chosen = colorchooser.askcolor(color=self.color or "#4285F4", parent=self, title="색 직접 고르기")
        color = _clean_color(chosen[1] if chosen else "")
        if color:
            self._pick_color(color)

    # ── 고칠 일정의 내용 채우기 ──
    def _fill(self, ev: Event) -> None:
        self.title_e.insert(0, ev.title)
        self.color = (ev.ref or {}).get("event_color", "")
        if ev.all_day:
            first, last = ev.start, ev.end - timedelta(days=1)
            self.allday_var.set(True)
            self._toggle_allday()
        else:
            first, last = ev.start.date(), ev.end.date()
            if ev.end.time() == dt_time(0, 0) and ev.end.date() > first:
                last = ev.end.date()  # 자정에 끝나면 다음 날 0시로 그대로 둬요
            self.start_cb.set(f"{ev.start.hour:02d}:{ev.start.minute:02d}")
            self.end_cb.set(f"{ev.end.hour:02d}:{ev.end.minute:02d}")
            self._start_seen = ev.start.time().replace(second=0, microsecond=0)
        for entry, d in ((self.date_e, first), (self.end_date_e, max(first, last))):
            entry.delete(0, "end")
            entry.insert(0, d.isoformat())
        self.loc_e.insert(0, ev.location)
        self.desc_t.insert("1.0", split_attachment_block(ev.notes))
        self.attachments = [dict(a) for a in (ev.ref or {}).get("attachments") or []]
        self._render_attachments()
        guests = [a["email"] for a in ev.ref.get("attendees_raw") or []
                  if not (a.get("self") or a.get("organizer") or a.get("resource"))]
        self.guest_e.insert(0, ", ".join(guests))
        self.modify_var.set(bool(ev.ref.get("guests_can_modify")))

    @staticmethod
    def _newline(e):
        e.widget.insert("insert", "\n")
        return "break"

    def _pick(self, entry: ttk.Entry) -> None:
        current = parse_date(entry.get(), self.app.today) or self.app.today

        def picked(d: date) -> None:
            entry.delete(0, "end")
            entry.insert(0, d.isoformat())
            self._keep_end_after_start(changed=entry)

        DatePopup(self, self.app, current, picked, entry.winfo_rootx(),
                  entry.winfo_rooty() + entry.winfo_height() + 2)

    def _keep_end_after_start(self, changed=None) -> None:
        """시작 날짜를 끝나는 날짜보다 뒤로 고르면 끝나는 날짜도 따라와요."""
        sd = parse_date(self.date_e.get(), self.app.today)
        ed = parse_date(self.end_date_e.get(), self.app.today)
        if sd and (not ed or ed < sd) and changed is not self.end_date_e:
            self.end_date_e.delete(0, "end")
            self.end_date_e.insert(0, sd.isoformat())

    def _target(self) -> RemoteCalendar | None:
        index = self.cal_cb.current()
        return self.cals[index] if 0 <= index < len(self.cals) else None

    def _choice_changed(self) -> None:
        self._update_where()

    def _guests_possible(self, cal: RemoteCalendar | None) -> str:
        """참석자를 넣을 수 없으면 그 까닭을 돌려줘요."""
        if cal is None:
            return ""
        if cal.source != "Google":
            return "iCloud 캘린더에는 참석자를 넣을 수 없어요."
        if self.app.service._google_api() is None:
            return "참석자는 설정 → Google에서 Google 계정으로 로그인하면 넣을 수 있어요."
        return ""

    def _switch_kind(self, kind: str) -> None:
        if kind != "todo":
            return
        first = parse_date(self.date_e.get(), self.app.today)
        prefill = {"title": self.title_e.get().strip(), "date": first, "desc": self.desc_t.get("1.0", "end").strip(),
                   "allday": bool(self.allday_var.get()), "start": self.start_cb.get().strip(),
                   "end": self.end_cb.get().strip(), "files": list(self.new_files)}
        app = self.app
        self.destroy()
        app.open_todo(prefill=prefill)

    def _apply_prefill(self, prefill: dict) -> None:
        if prefill.get("files"):
            self.new_files = list(prefill["files"])
            self._render_attachments()
        if prefill.get("title"):
            self.title_e.delete(0, "end")
            self.title_e.insert(0, prefill["title"])
        if prefill.get("desc"):
            self.desc_t.insert("1.0", prefill["desc"])
        if prefill.get("date"):
            for entry in (self.date_e, self.end_date_e):
                entry.delete(0, "end")
                entry.insert(0, prefill["date"].isoformat())
        if prefill.get("allday"):
            self.allday_var.set(True)
            self._toggle_allday()
        elif prefill.get("start"):
            self.start_cb.set(prefill["start"])
            if prefill.get("end"):
                self.end_cb.set(prefill["end"])
            self._start_seen = parse_time(prefill["start"])

    def _todo_mode(self) -> bool:
        return self.event is None and self.cal_cb.current() == len(self.cals)

    def _set_todo_fields(self, todo: bool) -> None:
        """'할 일'을 고르면 끝나는 날짜 · 끝 시간 · 장소 · 참석자를 흐리게 하고, 종일은 '시간 없음'이 돼요."""
        state = ["disabled"] if todo else ["!disabled"]
        for w in (self.end_date_e, self.end_date_btn, self.loc_e):
            w.state(state)
        self.allday_cb.config(text="시간 없음" if todo else "종일")
        if todo != getattr(self, "_was_todo", False):
            self.allday_var.set(todo)  # 할 일은 시간 없이 시작해요 (원하면 체크를 풀고 시간을 적어요)
            self._was_todo = todo
        self._toggle_allday()

    def _update_where(self) -> None:
        if self._todo_mode():
            self._set_todo_fields(True)
            sync = self.app.todo_sync_cal()
            self.swatch.config(bg=self.color or "#F6BF26")
            self.where.config(text="할 일로 저장돼요. " + (
                "Google Tasks에도 함께 들어가요." if self.app.tasks_mode() else
                f"아이폰 캘린더('{sync.name}')에도 함께 보여요." if sync else
                "설정의 '할 일 맞추기'를 켜 두면 Google Tasks나 아이폰 캘린더에도 보여요."))
            self.save_btn.state(["!disabled"])
            self.guest_e.state(["disabled"])
            self.modify_cb.state(["disabled"])
            self.guest_note.config(text="할 일에는 끝나는 날짜 · 장소 · 참석자 · 첨부가 없어요. 설명은 할 일의 둘째 줄부터 들어가요.")
            self._set_attach(False, "할 일에는 파일을 붙일 수 없어요.")
            self.color_enabled = True
            self.color_note.grid_remove()
            self._draw_colors()
            return
        if self.event is None:
            self._set_todo_fields(False)
        cal = self._target()
        if cal is None:
            self.color_enabled = False
            self._draw_colors()
            self.swatch.config(bg=HINT_GRAY)
            self.where.config(text="일정을 넣을 캘린더가 없어요. 설정 → Google에서 계정을 연결하거나, "
                                   "오른쪽 클릭 메뉴의 '새 캘린더 만들기'로 캘린더를 만들어 주세요.")
            self.save_btn.state(["disabled"])
            return
        colors = self.app.cfg.get("cal_colors") or {}
        self.swatch.config(bg=colors.get(cal.key, cal.color))
        self.where.config(text=f"{cal.source} 캘린더 '{cal.name}'에 저장돼요. 아이폰 캘린더에도 함께 보여요.")
        self.save_btn.state(["!disabled"])
        why_not = self._guests_possible(cal)
        state = ["disabled"] if why_not else ["!disabled"]
        self.guest_e.state(state)
        self.modify_cb.state(state)
        self._set_attach(not why_not, why_not.replace("참석자는", "파일은").replace("참석자를", "파일을") if why_not else "")
        self.color_enabled = not why_not
        if why_not:
            self.color_note.config(text=why_not.replace("참석자는", "색은").replace("참석자를", "색을"))
            self.color_note.grid()
        else:
            self.color_note.grid_remove()  # 안내할 게 없으면 빈 줄을 남기지 않아요
        self._draw_colors()
        self.guest_note.config(text=why_not or "이메일을 쉼표로 나눠 여러 명 적을 수 있어요. 참석자에게 초대 메일이 가요.")

    def _default_times(self, day: date, start_time: dt_time | None) -> tuple[str, str]:
        if start_time is not None:
            start = start_time.hour * 60 + start_time.minute
        elif day == self.app.today:
            now = datetime.now()
            start = min(((now.hour * 60 + now.minute) // 30 + 1) * 30, 23 * 60)
        else:
            start = 9 * 60
        end = min(start + 60, 23 * 60 + 59)
        return f"{start // 60:02d}:{start % 60:02d}", f"{end // 60:02d}:{end % 60:02d}"

    def _start_changed(self, _e=None) -> None:
        """시작 시간을 바꾸면 끝나는 시간이 원래 길이만큼 따라와요 (처음에는 1시간)."""
        new = parse_time(self.start_cb.get())
        if not new:
            return
        old, end = getattr(self, "_start_seen", None), parse_time(self.end_cb.get())
        length = 60
        if old and end:
            gap = (end.hour * 60 + end.minute) - (old.hour * 60 + old.minute)
            if gap > 0:
                length = gap
        if old != new:
            m = min(new.hour * 60 + new.minute + length, 23 * 60 + 59)
            self.end_cb.set(f"{m // 60:02d}:{m % 60:02d}")
        self._start_seen = new

    def _toggle_allday(self) -> None:
        state = "disabled" if self.allday_var.get() else "normal"
        self.start_cb.configure(state=state)
        self.end_cb.configure(state="disabled" if self._todo_mode() else state)

    # ── 저장 · 지우기 ──
    def save(self) -> None:
        if self._todo_mode():
            return self._save_todo()
        title = self.title_e.get().strip()
        if not title:
            return self.say("제목을 입력해 주세요.", error=True)
        first = parse_date(self.date_e.get(), self.app.today)
        last = parse_date(self.end_date_e.get(), self.app.today) if self.end_date_e.get().strip() else first
        if not first or not last:
            return self.say("날짜를 2026-11-20처럼 입력해 주세요.", error=True)
        if last < first:
            return self.say("끝나는 날짜가 시작 날짜보다 빠를 수 없어요.", error=True)
        if self.allday_var.get():
            start, end, all_day = first, last + timedelta(days=1), True
        else:
            t1, t2 = parse_time(self.start_cb.get()), parse_time(self.end_cb.get())
            if not t1 or not t2:
                return self.say("시간을 09:30처럼 입력해 주세요.", error=True)
            start = datetime.combine(first, t1).astimezone()
            end = datetime.combine(last, t2).astimezone()
            if end <= start:
                if last == first and t2 < t1:  # 밤 11시 ~ 새벽 1시처럼 다음 날로 넘어가는 일정
                    end = datetime.combine(first + timedelta(days=1), t2).astimezone()
                else:
                    return self.say("끝나는 시간이 시작 시간보다 늦어야 해요.", error=True)
            all_day = False
        cal = self._target()
        if cal is None:
            return self.say("일정을 넣을 캘린더를 골라 주세요.", error=True)
        guests, bad = [], []
        if not self._guests_possible(cal):
            for part in re.split(r"[,;\s]+", self.guest_e.get().strip()):
                if part:
                    (guests if EMAIL_RE.fullmatch(part) else bad).append(part)
        if bad:
            return self.say(f"이메일 주소를 확인해 주세요: {', '.join(bad[:3])}", error=True)
        payload = {"source": cal.source, "calendar_id": cal.url, "title": title, "start": start, "end": end,
                   "all_day": all_day, "location": self.loc_e.get().strip(),
                   "description": self.desc_t.get("1.0", "end").strip(),
                   "attendees": guests, "guests_can_modify": bool(self.modify_var.get())}
        if self.color_enabled:
            payload["color"] = self.color
        if self.attach_enabled:
            payload.update({"attachments": list(self.attachments), "new_files": list(self.new_files),
                            "progress": self._upload_progress})
        self.save_btn.state(["disabled"])
        if self.event is not None:
            self.say("고치는 중…")
            self.app.worker.submit(self.app.service.update_event, self.event.ref, payload,
                                   callback=lambda res, err: self._saved(err, first))
        else:
            self.say("추가하는 중…")
            self.app.worker.submit(self.app.service.add_event, payload,
                                   callback=lambda res, err: self._saved(err, first))

    def _save_todo(self) -> None:
        title = self.title_e.get().strip()
        if not title:
            return self.say("할 일을 적어 주세요.", error=True)
        due = parse_date(self.date_e.get(), self.app.today)
        if not due:
            return self.say("날짜를 2026-11-20처럼 입력해 주세요.", error=True)
        at = None
        if not self.allday_var.get():
            raw = self.start_cb.get().strip()
            at = parse_time(raw) if raw else None
            if raw and at is None:
                return self.say("시간을 15:00이나 오후 3시처럼 적어 주세요.", error=True)
        desc = self.desc_t.get("1.0", "end").strip()
        self.app.add_todo(title + ("\n" + desc if desc else ""), due, self.color or None, at)
        self.app.cfg["last_calendar"] = TODO_CHIP
        self.app.save()
        self.destroy()
        self.app.show_flash("할 일을 추가했어요")

    def _saved(self, error, day: date) -> None:
        if not self.winfo_exists():
            return
        if error is not None:
            self.save_btn.state(["!disabled"])
            verb = "고치지" if self.event is not None else "추가하지"
            self.say(str(error) if isinstance(error, SyncError) else f"{verb} 못했어요: {error}", error=True)
            return
        cal = self._target()
        if self.event is None and cal is not None:  # 다음에도 같은 캘린더로 열려요
            self.app.cfg["last_calendar"] = cal.key
            self.app.save()
        edited = self.event is not None
        self.destroy()
        self.app.event_added(day)
        if edited:
            self.app.show_flash("일정을 고쳤어요")

    def delete(self) -> None:
        ev = self.event
        guests = [a for a in ev.ref.get("attendees_raw") or [] if not (a.get("self") or a.get("organizer"))]
        lines = [f"'{ev.title}' 일정을 지울까요?"]
        if ev.ref.get("recurring"):
            lines.append("반복 일정이라 이 날 일정만 지워져요.")
        if guests:
            lines.append("참석자에게 취소 메일이 가요.")
        if not messagebox.askyesno(APP_TITLE, "\n".join(lines), parent=self):
            return
        self.save_btn.state(["disabled"])
        self.delete_btn.state(["disabled"])
        self.say("지우는 중…")
        day = ev.start if ev.all_day else ev.start.date()

        def done(_res, err) -> None:
            if not self.winfo_exists():
                return
            if err is not None:
                self.save_btn.state(["!disabled"])
                self.delete_btn.state(["!disabled"])
                self.say(str(err) if isinstance(err, SyncError) else f"지우지 못했어요: {err}", error=True)
                return
            self.destroy()
            self.app.event_added(day)
            self.app.show_flash("일정을 지웠어요")

        self.app.worker.submit(self.app.service.delete_google_event, ev.ref, callback=done)


HOLIDAY_WORDS = re.compile(r"신정|설날|설\s*연휴|동시\s*지방\s*선거|대통령\s*선거|국회의원\s*선거|삼일절|3\s*[·.]\s*1\s*절|어린이날|부처님\s*오신\s*날|석가\s*탄신일|현충일|광복절|추석|"
                           r"개천절|한글날|성탄절|기독\s*탄신일|크리스마스|대체\s*(공휴일|휴일)|선거일")


def schedule_when(it: dict) -> str:
    s, e = it["start"], it["end"]
    if it["all_day"]:
        text = f"{s.year}. {s.month}. {s.day}. ({WEEKDAY_SHORT[s.weekday()]})"
        if e != s:
            year = f"{e.year}. " if e.year != s.year else ""
            text += f" ~ {year}{e.month}. {e.day}. ({WEEKDAY_SHORT[e.weekday()]})"
        return text
    return f"{s.year}. {s.month}. {s.day}. ({WEEKDAY_SHORT[s.weekday()]}) {fmt_time(s)} ~ {fmt_time(e)}"


class ImportDialog(_Dialog):
    """학사일정 파일을 읽어 일정을 보여 주고, 고른 것만 캘린더에 넣어요."""

    def __init__(self, app: App):
        super().__init__(app, "학사일정 · 방과후 가져오기")
        self.resizable(True, True)
        px = app.px
        self.items: list = []
        self.lines: list = []
        self.path = ""
        self.raws: list = []
        self.refs: list = []
        self.busy = False
        self.cals = app.event_calendars()

        row = ttk.Frame(self.frame)
        ttk.Button(row, text="파일 고르기…", command=self.choose).pack(side="left")
        self.file_lbl = ttk.Label(row, text="한글 · PDF · 엑셀 · 워드 · 캘린더(ics) 파일을 고르세요",
                                  foreground=HINT_GRAY)
        self.file_lbl.pack(side="left", padx=(px(10), 0))
        self.field("파일", row)
        modes = ttk.Frame(self.frame)
        self.mode_var = tk.StringVar(value="schedule")
        ttk.Radiobutton(modes, text="학사일정", value="schedule", variable=self.mode_var, style="Toolbutton",
                        command=self._mode_changed).pack(side="left", padx=(0, px(4)))
        self.after_rb = ttk.Radiobutton(modes, text="방과후 시간표", value="afterschool", variable=self.mode_var,
                                        style="Toolbutton", command=self._mode_changed)
        self.after_rb.pack(side="left", padx=(0, px(10)))
        ttk.Button(modes, text="방과후 규칙…", command=self._edit_rules).pack(side="left")
        self.field("읽는 방식", modes, stretch=False)
        self.grid_entries, self.grid_texts = [], []
        self.after_rb.state(["disabled"])
        years = ttk.Frame(self.frame)
        today = app.today
        self.year_var = tk.StringVar(value=str(today.year if today.month >= 3 else today.year - 1))
        spin = ttk.Spinbox(years, from_=2000, to=2100, width=6, textvariable=self.year_var, command=self.reparse)
        spin.pack(side="left")
        spin.bind("<Return>", lambda e: self.reparse())
        spin.bind("<FocusOut>", lambda e: self.reparse())
        ttk.Label(years, text="학년도  (3~12월은 이 해, 1~2월은 다음 해로 넣어요)",
                  foreground=HINT_GRAY).pack(side="left", padx=(px(8), 0))
        self.field("학년도", years, stretch=False)
        self.cal_cb = self.field("넣을 캘린더", ttk.Combobox(
            self.frame, state="readonly", width=32, values=[c.label for c in self.cals]), stretch=False)
        school = app.slot_calendar(0)
        keys = [c.key for c in self.cals]
        self.cal_cb.current(keys.index(school.key) if school and school.key in keys else 0)
        self.cal_cb.bind("<<ComboboxSelected>>", lambda e: self.check_existing())
        # 이 파일의 일정이 다른 캘린더에 이미 있으면 여기로 옮길 수 있어요
        self.move_bar = ttk.Frame(self.frame)
        self.move_bar.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(6), 0))
        self.row += 1
        self.move_lbl = ttk.Label(self.move_bar, foreground="#1E5FA8", wraplength=px(420), justify="left")
        self.move_lbl.pack(side="left")
        self.move_btn = ttk.Button(self.move_bar, text="옮기기", command=self.do_move)
        self.move_btn.pack(side="right")
        self.move_bar.grid_remove()
        self.move_plan = None
        # 이미 들어간 일정의 색이 규칙과 다르면 한꺼번에 바꿀 수 있어요
        self.color_bar = ttk.Frame(self.frame)
        self.color_bar.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(6), 0))
        self.row += 1
        self.color_lbl = ttk.Label(self.color_bar, foreground="#1E5FA8", wraplength=px(420), justify="left")
        self.color_lbl.pack(side="left")
        self.color_btn = ttk.Button(self.color_bar, text="색 입히기", command=self.do_recolor)
        self.color_btn.pack(side="right")
        self.color_bar.grid_remove()
        self.recolor_plan = None

        box = ttk.Frame(self.frame)
        box.grid(row=self.row, column=0, columnspan=3, sticky="nsew", pady=(px(8), 0))
        self.frame.rowconfigure(self.row, weight=1)
        self.row += 1
        self.tree = ttk.Treeview(box, columns=("pick", "when", "title", "note"), show="headings",
                                 height=14, selectmode="browse")
        for col, text, width, anchor in (("pick", "넣기", 46, "center"), ("when", "날짜", 220, "w"),
                                         ("title", "일정", 250, "w"), ("note", "참고", 150, "w")):
            self.tree.heading(col, text=text)
            self.tree.column(col, width=px(width), minwidth=px(40), anchor=anchor, stretch=col == "title")
        bar = ttk.Scrollbar(box, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=bar.set)
        self.tree.pack(side="left", fill="both", expand=True)
        bar.pack(side="right", fill="y")
        self.tree.tag_configure("off", foreground="#9AA0A6")
        self.tree.tag_configure("warn", foreground="#B3261E")
        self.tree.bind("<Button-1>", self._click)
        self.tree.bind("<Double-1>", self._edit)
        self.tree.bind("<space>", lambda e: self._toggle_selected())

        tools = ttk.Frame(self.frame)
        tools.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(6), 0))
        self.row += 1
        for text, cmd in (("모두 넣기", lambda: self._set_all(True)), ("모두 빼기", lambda: self._set_all(False))):
            link = ttk.Label(tools, text=text, foreground=LINK_BLUE, cursor="hand2")
            link.pack(side="left", padx=(0, px(12)))
            link.bind("<Button-1>", lambda e, c=cmd: c())
        ttk.Label(tools, text="'넣기' 칸을 누르면 넣고 뺄 수 있고, 줄을 두 번 누르면 날짜와 제목을 고칠 수 있어요.",
                  foreground=HINT_GRAY, font=app.fonts["small"]).pack(side="left")
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="닫기", command=self.destroy).pack(side="right")
        self.import_btn = ttk.Button(buttons, text="캘린더에 넣기", command=self.do_import)
        self.import_btn.pack(side="right", padx=(0, px(6)))
        self.undo_btn = ttk.Button(buttons, text="방금 넣은 일정 되돌리기", command=self.undo)
        self.import_btn.state(["disabled"])
        self.show()
        self.after(150, self.choose)

    # ── 파일 읽기 ──
    def choose(self) -> None:
        from tkinter import filedialog
        path = filedialog.askopenfilename(parent=self, title="학사일정 파일 고르기", filetypes=IMPORT_TYPES)
        if path:
            self.load(path)

    def load(self, path: str) -> None:
        self.path = path
        self.file_lbl.config(text=os.path.basename(path), foreground="#3D4249")
        self.say("파일을 읽는 중…")
        if path.lower().endswith(".ics"):
            self.lines, self.raws, self.grid_entries = [], [], []
            self.after_rb.state(["disabled"])
            self.mode_var.set("schedule")
            self.reparse()
            return

        def job():
            grid = read_code_grid(path) if path.lower().endswith((".xlsx", ".xlsm")) else ([], [])
            return read_schedule_file(path), grid

        self.app.worker.submit(job, callback=self._read)

    def _read(self, result, error) -> None:
        if not self.winfo_exists():
            return
        if error is not None:
            self.items = []
            self._fill()
            self.say(str(error) if isinstance(error, SyncError) else "파일을 읽지 못했어요.", error=True)
            return
        (self.lines, note), (self.grid_entries, self.grid_texts) = result
        self.raws = scan_schedule(self.lines)
        self.year_var.set(str(guess_school_year(self.lines, self.raws, self.app.today)))
        codes = {re.sub(r"\s+", "", str(r.get("code") or "")) for r in self.app.cfg["afterschool"]["rules"]}
        matches = sum(1 for e in self.grid_entries if e[2] in codes)
        self.after_rb.state(["!disabled"] if self.grid_entries else ["disabled"])
        if matches >= 3:  # 방과후 시간표처럼 생긴 표예요
            self.mode_var.set("afterschool")
            self._prefer_afterschool_calendar()
            year = next((int(m.group(1)) for t in self.grid_texts for m in [_SCHOOL_YEAR_RE.search(t)] if m), None)
            if year:
                self.year_var.set(str(year))
        elif self.mode_var.get() == "afterschool":
            self.mode_var.set("schedule")
        self.reparse(note)

    def _prefer_afterschool_calendar(self) -> None:
        names = [c.name for c in self.cals]
        idx = next((i for i, n in enumerate(names) if "방과후" in n), None)
        if idx is not None:
            self.cal_cb.current(idx)

    def _mode_changed(self) -> None:
        if self.mode_var.get() == "afterschool":
            self._prefer_afterschool_calendar()
        if self.path:
            self.reparse()

    def _edit_rules(self) -> None:
        AfterschoolRulesDialog(self.app, on_saved=lambda: self.reparse() if self.winfo_exists() else None)

    def reparse(self, note: str = "") -> None:
        if not self.path:
            return
        try:
            year = int(self.year_var.get())
        except ValueError:
            return
        unknown: Counter = Counter()
        afterschool = self.mode_var.get() == "afterschool"
        try:
            if afterschool:
                items, unknown = afterschool_items(self.grid_entries, self.app.cfg["afterschool"], year)
            elif self.path.lower().endswith(".ics"):
                items = ics_items(self.path, year)
            else:
                items = resolve_schedule(self.raws, year)
        except SyncError as exc:
            self.say(str(exc), error=True)
            return
        for it in items:
            it["checked"], it["note"] = True, ""
            if afterschool:
                names = {hx: nm for hx, nm in GOOGLE_EVENT_COLORS}
                color_name = names.get(it.get("color") or "", "직접 고른 색" if it.get("color") else "")
                it["note"] = " · ".join(x for x in (it["line"], "방학 시간" if it.get("vacation") else "", color_name) if x)
            if it["wd_ok"] is False:
                it["note"] = "요일이 안 맞아요"
            if HOLIDAY_WORDS.search(it["title"]) or it["start"] in self.app.holidays:
                it["checked"], it["note"] = False, "공휴일 (이미 보여요)"
        self.items = items
        self._fill()
        if not items:
            self.say("날짜와 일정을 찾지 못했어요. 표가 그림으로 들어 있거나, 날짜가 '3. 2.(월)'처럼 적혀 있지 않은 것 같아요.",
                     error=True)
            return
        holidays = sum(1 for it in items if it["note"].startswith("공휴일"))
        warns = sum(1 for it in items if it["note"] == "요일이 안 맞아요")
        text = f"일정 {len(items)}개를 찾았어요."
        if afterschool:
            counts = Counter(it["title"] for it in items)
            text = f"방과후 일정 {len(items)}개를 찾았어요: " + ", ".join(f"{t} {n}" for t, n in counts.items()) + "."
            if unknown:
                text += (" 규칙에 없는 표시(" + ", ".join(f"{c} {n}개" for c, n in unknown.most_common(5))
                         + ")는 넣지 않아요. '방과후 규칙…'에서 더할 수 있어요.")
        if holidays:
            text += f" 공휴일 {holidays}개는 이미 보여서 뺐어요."
        if warns:
            text += f" 파일에 적힌 요일이 달력과 다른 {warns}개는 빨갛게 표시했어요. 날짜를 한 번 확인해 주세요."
        self.say(note or text, error=bool(note))
        self.check_existing()

    def check_existing(self) -> None:
        self.move_plan = None
        self.move_bar.grid_remove()
        self.recolor_plan = None
        self.color_bar.grid_remove()
        if not self.items or self.cal_cb.current() < 0:
            return
        cal = self.cals[self.cal_cb.current()]
        days = [it["start"] if it["all_day"] else it["start"].date() for it in self.items]
        start, end = min(days), max(days) + timedelta(days=1)
        service = self.app.service
        others = [c for c in self.cals if c.source == "Google" and c.key != cal.key]

        def job():
            here = service.existing_keys(cal.source, cal.url, start, end)
            elsewhere, here_refs = {}, {}
            if cal.source == "Google" and service._google_api() is not None:
                here_refs = service.google_event_ids(cal.url, start, end)
                for other in others:
                    ids = service.google_event_ids(other.url, start, end)
                    if ids:
                        elsewhere[other.key] = ids
            return here, elsewhere, here_refs

        self.app.worker.submit(job, callback=lambda res, err: self._existing(cal, res, err))

    def _existing(self, target, result, error) -> None:
        if not self.winfo_exists() or error is not None or not result:
            return
        keys, elsewhere, here_refs = result
        dup = 0
        for it in self.items:
            day = it["start"] if it["all_day"] else it["start"].date()
            if (day, norm_title(it["title"])) in keys:
                it["checked"], it["note"] = False, "이미 캘린더에 있어요"
                dup += 1
        # 여기에는 없지만 다른 캘린더에 있는 일정: 가장 많이 있는 캘린더에서 옮겨 올 수 있게
        best, best_ids = None, []
        for key, found in elsewhere.items():
            ids = []
            for it in self.items:
                day = it["start"] if it["all_day"] else it["start"].date()
                hit = found.get((day, norm_title(it["title"])))
                if it["note"] != "이미 캘린더에 있어요" and hit:
                    ids.append((it, hit[0][0]))
            if len(ids) > len(best_ids):
                best, best_ids = key, ids
        self._fill()
        text = f"일정 {len(self.items)}개 중 {dup}개는 이미 캘린더에 있어서 뺐어요." if dup else ""
        if best_ids:
            src = next(c for c in self.cals if c.key == best)
            for it, _eid in best_ids:
                it["checked"], it["note"] = False, f"'{src.name}'에 있어요"
            self._fill()
            self.move_plan = (src, target, [eid for _it, eid in best_ids])
            self.move_lbl.config(text=f"이 파일의 일정 {len(best_ids)}개가 '{src.name}' 캘린더에 이미 있어요. "
                                      f"두 번 들어가지 않게 빼 두었어요. '{target.name}'(으)로 옮길 수 있어요.")
            self.move_btn.config(text=f"'{target.name}'(으)로 옮기기")
            self.move_bar.grid()
        # 이미 여기 있는 일정 가운데 규칙의 색과 다른 것
        plan = []
        for it in self.items:
            if it["note"] != "이미 캘린더에 있어요" or "color" not in it:
                continue
            day = it["start"] if it["all_day"] else it["start"].date()
            hit = here_refs.get((day, norm_title(it["title"])))
            if hit and (it["color"] or "") != (hit[0][1] or ""):
                plan.append((hit[0][0], it["color"] or "", hit[0][2]))
        if plan:
            self.recolor_plan = (target, plan)
            self.color_lbl.config(text=f"이미 들어간 일정 {len(plan)}개의 색이 방과후 규칙과 달라요. "
                                       "규칙의 색으로 한꺼번에 바꿀 수 있어요.")
            self.color_bar.grid()
        if text:
            self.say(text)

    def do_recolor(self) -> None:
        if not self.recolor_plan or self.busy:
            return
        target, plan = self.recolor_plan
        self.busy = True
        self.color_btn.state(["disabled"])
        self.say(f"색을 바꾸는 중… 0/{len(plan)}")

        def progress(n, total):
            self.app.worker.results.put((lambda r, e: self.busy and self.winfo_exists() and
                                         self.say(f"색을 바꾸는 중… {r[0]}/{r[1]}"), (n, total), None))

        self.app.worker.submit(self.app.service.recolor_events, target.url, plan, progress,
                               callback=lambda res, err: self._recolored(res, err))

    def _recolored(self, result, error) -> None:
        self.app.refresh_all()
        if not self.winfo_exists():
            return
        self.busy = False
        self.color_btn.state(["!disabled"])
        if error is not None:
            self.say(str(error) if isinstance(error, SyncError) else "색을 바꾸지 못했어요.", error=True)
            return
        text = f"일정 {result['done']}개의 색을 규칙대로 바꿨어요."
        if result["failed"]:
            text += f" {len(result['failed'])}개는 바꾸지 못했어요: {result['failed'][0]}"
        self.check_existing()
        self.after(300, lambda: self.winfo_exists() and self.say(text, error=bool(result["failed"])))

    def do_move(self) -> None:
        if not self.move_plan or self.busy:
            return
        src, dest, ids = self.move_plan
        if not messagebox.askyesno(APP_TITLE, f"'{src.name}'에 있는 이 파일의 일정 {len(ids)}개를 '{dest.name}'(으)로 "
                                              "옮길까요?\nGoogle 캘린더와 아이폰에서도 함께 옮겨져요.", parent=self):
            return
        self.busy = True
        self.move_btn.state(["disabled"])
        self.import_btn.state(["disabled"])
        self.say(f"'{dest.name}'(으)로 옮기는 중… 0/{len(ids)}")

        def progress(n, total):
            self.app.worker.results.put((lambda r, e: self.busy and self.winfo_exists() and
                                         self.say(f"'{dest.name}'(으)로 옮기는 중… {r[0]}/{r[1]}"), (n, total), None))

        self.app.worker.submit(self.app.service.move_events, src.url, dest.url, ids, progress,
                               callback=lambda res, err: self._moved(src, dest, res, err))

    def _moved(self, src, dest, result, error) -> None:
        self.app.refresh_all()
        if not self.winfo_exists():
            return
        self.busy = False
        self.move_btn.state(["!disabled"])
        if error is not None:
            self.say(str(error) if isinstance(error, SyncError) else "옮기지 못했어요.", error=True)
            return
        text = f"{result['moved']}개를 '{src.name}'에서 '{dest.name}'(으)로 옮겼어요."
        if result["failed"]:
            text += f" {len(result['failed'])}개는 옮기지 못했어요: {result['failed'][0]}"
        self.check_existing()
        self.after(300, lambda: self.winfo_exists() and self.say(text, error=bool(result["failed"])))

    # ── 목록 ──
    def _fill(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for i, it in enumerate(self.items):
            tags = ("warn",) if it["note"] == "요일이 안 맞아요" else () if it["checked"] else ("off",)
            self.tree.insert("", "end", iid=str(i), tags=tags,
                             values=("■" if it["checked"] else "□", schedule_when(it), it["title"], it["note"]))
        picked = sum(1 for it in self.items if it["checked"])
        self.import_btn.config(text=f"캘린더에 넣기 ({picked}개)" if picked else "캘린더에 넣기")
        self.import_btn.state(["!disabled"] if picked and not self.busy else ["disabled"])

    def _click(self, e):
        if self.tree.identify_region(e.x, e.y) == "cell" and self.tree.identify_column(e.x) == "#1":
            iid = self.tree.identify_row(e.y)
            if iid:
                self._toggle(int(iid))
                return "break"
        return None

    def _toggle(self, index: int) -> None:
        self.items[index]["checked"] = not self.items[index]["checked"]
        self._fill()
        self.tree.selection_set(str(index))
        self.tree.see(str(index))

    def _toggle_selected(self) -> None:
        sel = self.tree.selection()
        if sel:
            self._toggle(int(sel[0]))

    def _set_all(self, value: bool) -> None:
        for it in self.items:
            it["checked"] = value
        self._fill()

    def _edit(self, e) -> None:
        iid = self.tree.identify_row(e.y)
        if not iid:
            return
        it = self.items[int(iid)]
        win = _Dialog(self.app, "일정 고치기")
        title = win.field("제목", ttk.Entry(win.frame, width=34))
        title.insert(0, it["title"])
        start_e = end_e = None
        if it["all_day"]:
            start_e = win.field("시작", ttk.Entry(win.frame, width=14), stretch=False)
            start_e.insert(0, it["start"].isoformat())
            end_e = win.field("끝", ttk.Entry(win.frame, width=14), stretch=False)
            end_e.insert(0, it["end"].isoformat())
        win.message_area()

        def ok() -> None:
            if start_e is not None:
                s = parse_date(start_e.get(), self.app.today)
                en = parse_date(end_e.get(), self.app.today)
                if not s or not en or en < s:
                    win.say("날짜를 2026-03-02처럼 적어 주세요. 끝은 시작과 같거나 뒤여야 해요.", error=True)
                    return
                it["start"], it["end"] = s, en
            text = title.get().strip()
            if not text:
                win.say("제목을 적어 주세요.", error=True)
                return
            it["title"], it["checked"], it["note"] = text, True, "고침"
            win.destroy()
            self._fill()

        btns = ttk.Frame(win.frame)
        btns.grid(row=win.row, column=0, columnspan=3, sticky="ew", pady=(self.app.px(10), 0))
        ttk.Button(btns, text="취소", command=win.destroy).pack(side="right")
        ttk.Button(btns, text="확인", command=ok).pack(side="right", padx=(0, self.app.px(6)))
        win.bind("<Return>", lambda ev: ok())
        win.show()
        title.focus_set()

    # ── 넣기 · 되돌리기 ──
    def do_import(self) -> None:
        picked = [it for it in self.items if it["checked"]]
        if not picked or self.busy:
            return
        cal = self.cals[self.cal_cb.current()]
        self.busy = True
        self.import_btn.state(["disabled"])
        self.undo_btn.pack_forget()
        self.say(f"'{cal.name}'에 넣는 중… 0/{len(picked)}")

        def progress(n, total):
            self.app.worker.results.put((lambda r, e: self._progress(cal, r), (n, total), None))

        self.app.worker.submit(self.app.service.import_events, cal, picked, progress,
                               callback=lambda res, err: self._imported(cal, picked, res, err))

    def _progress(self, cal, value) -> None:
        if self.winfo_exists() and self.busy:
            self.say(f"'{cal.name}'에 넣는 중… {value[0]}/{value[1]}")

    def _imported(self, cal, picked, result, error) -> None:
        self.app.refresh_all()
        if not self.winfo_exists():
            return
        self.busy = False
        if error is not None:
            self.say(str(error) if isinstance(error, SyncError) else "일정을 넣지 못했어요.", error=True)
            self._fill()
            return
        self.refs = [r for r in result["refs"] if r.get("id") or r.get("url")]
        done = len(result["refs"])
        for it in picked[:done]:
            it["checked"], it["note"] = False, "넣었어요"
        self._fill()
        text = f"{done}개를 '{cal.name}' 캘린더에 넣었어요. 아이폰 캘린더에도 곧 나타나요."
        if result["failed"]:
            text += f"\n{len(result['failed'])}개는 넣지 못했어요: {result['failed'][0][1]}"
        self.say(text, error=bool(result["failed"]))
        if self.refs:
            self.undo_btn.pack(side="left")

    def undo(self) -> None:
        refs, self.refs = self.refs, []
        if not refs or self.busy:
            return
        self.busy = True
        self.undo_btn.pack_forget()
        self.say("방금 넣은 일정을 지우는 중…")

        def job():
            removed, failed = 0, 0
            for ref in refs:
                try:
                    self.app.service.delete_event(ref)
                    removed += 1
                except SyncError:
                    failed += 1
            return removed, failed

        self.app.worker.submit(job, callback=self._undone)

    def _undone(self, result, error) -> None:
        self.app.refresh_all()
        if not self.winfo_exists():
            return
        self.busy = False
        if error is not None:
            self.say("되돌리지 못했어요.", error=True)
            return
        removed, failed = result
        for it in self.items:
            if it["note"] == "넣었어요":
                it["checked"], it["note"] = True, ""
        self._fill()
        self.say(f"방금 넣은 일정 {removed}개를 지웠어요." + (f" {failed}개는 지우지 못했어요." if failed else ""),
                 error=bool(failed))


def done_label(item: dict) -> str:
    """'2026-11-20T15:04' → '2026. 11. 20. (금) 15:04'"""
    raw = str(item.get("done_at") or "")
    try:
        d = date.fromisoformat(raw[:10])
    except ValueError:
        return ""
    text = f"{d.year}. {d.month}. {d.day}. ({WEEKDAY_SHORT[d.weekday()]})"
    return text + (f" {raw[11:16]}" if len(raw) >= 16 else "")


class TodoHistoryDialog(_Dialog):
    """끝낸 할 일을 최근 것부터 보여 주고, 다시 할 일로 돌리거나 지울 수 있어요."""

    def __init__(self, app: App):
        super().__init__(app, "끝낸 할 일")
        self.resizable(True, True)
        px = app.px
        self.hint(f"끝낸 할 일은 {TODO_KEEP_DAYS // 365}년 동안 보관돼요. 줄을 고른 뒤(Ctrl이나 Shift로 여러 개) 아래 단추를 누르세요. "
                  "두 번 누르면 바로 다시 할 일로 돌아가요.")
        box = ttk.Frame(self.frame)
        box.grid(row=self.row, column=0, columnspan=3, sticky="nsew", pady=(px(4), 0))
        self.frame.rowconfigure(self.row, weight=1)
        self.row += 1
        self.tree = ttk.Treeview(box, columns=("when", "text"), show="headings", height=14, selectmode="extended")
        self.tree.heading("when", text="끝낸 때")
        self.tree.heading("text", text="할 일")
        self.tree.column("when", width=px(170), minwidth=px(120), anchor="w", stretch=False)
        self.tree.column("text", width=px(320), minwidth=px(120), anchor="w")
        bar = ttk.Scrollbar(box, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=bar.set)
        self.tree.pack(side="left", fill="both", expand=True)
        bar.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", lambda e: self.restore())
        self.tree.bind("<Delete>", lambda e: self.delete())
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="모두 지우기", command=self.clear_all).pack(side="left")
        ttk.Button(buttons, text="닫기", command=self.destroy).pack(side="right")
        ttk.Button(buttons, text="지우기", command=self.delete).pack(side="right", padx=(0, px(6)))
        ttk.Button(buttons, text="다시 할 일로", command=self.restore).pack(side="right", padx=(0, px(6)))
        self.fill()
        self.show()

    def fill(self) -> None:
        self.tree.delete(*self.tree.get_children())
        items = self.app.todos.done_items()
        for item in items:
            self.tree.insert("", "end", iid=item["id"], values=(done_label(item), item["text"]))
        if not items:
            self.say("끝낸 할 일이 아직 없어요.")

    def _changed(self) -> None:
        self.app.render_todos()
        self.app.refresh_summary()
        self.fill()

    def restore(self) -> None:
        ids = list(self.tree.selection())
        if not ids:
            return self.say("다시 할 일로 돌릴 줄을 골라 주세요.", error=True)
        for item_id in ids:
            self.app.todos.reopen(item_id)
        self._changed()
        self.say(f"{len(ids)}개를 다시 할 일로 돌렸어요.")

    def delete(self) -> None:
        ids = list(self.tree.selection())
        if not ids:
            return self.say("지울 줄을 골라 주세요.", error=True)
        for item_id in ids:
            self.app.todos.delete(item_id)
        self._changed()
        self.say(f"{len(ids)}개를 지웠어요.")

    def clear_all(self) -> None:
        count = len(self.app.todos.done_items())
        if not count:
            return
        if not messagebox.askyesno(APP_TITLE, f"끝낸 할 일 {count}개를 모두 지울까요?\n지우면 되돌릴 수 없어요.",
                                   parent=self):
            return
        self.app.todos.clear_done()
        self._changed()
        self.say(f"끝낸 할 일 {count}개를 지웠어요.")


class WelcomeDialog(_Dialog):
    """처음 실행할 때: Google 계정으로 로그인만 하면 끝나요."""

    def __init__(self, app: App):
        super().__init__(app, "캘린더 위젯 시작하기")
        px = app.px
        self.section("아이폰 캘린더와 연결해요")
        self.hint("아이폰 캘린더에 쓰는 Google 계정으로 로그인하면 일정이 위젯에 나타나요. "
                  "위젯에서 넣은 일정도 아이폰 캘린더에 나타나요.")
        self.login_btn = ttk.Button(self.frame, text="Google 계정으로 로그인", command=self.login)
        self.login_btn.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(6), px(8)))
        self.row += 1
        self.hint("브라우저가 열리면 계정을 고르고, 캘린더 권한을 모두 체크한 뒤 계속을 눌러 주세요.")
        if IS_WINDOWS:
            self.auto_var = tk.BooleanVar(value=True)
            self.check("윈도우를 켤 때 위젯 자동으로 실행", self.auto_var)
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(12), 0))
        icloud = ttk.Label(buttons, text="iCloud 캘린더만 쓰고 있어요", foreground=LINK_BLUE, cursor="hand2")
        icloud.pack(side="left")
        icloud.bind("<Button-1>", lambda e: self.icloud())
        ttk.Button(buttons, text="나중에 할게요", command=self.close).pack(side="right")
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.show()

    def login(self) -> None:
        self.login_btn.state(["disabled"])
        self.say("브라우저에서 로그인을 기다리는 중이에요…")
        self.app.google_sign_in(on_done=self._done)

    def _done(self, result, error) -> None:
        if not self.winfo_exists():
            return
        self.login_btn.state(["!disabled"])
        if error is not None:
            self.say(str(error), error=True)
            return
        self.say(f"{result['email']} 계정으로 연결됐어요. 일정을 불러오고 있어요!")
        self.after(2200, self.close)

    def icloud(self) -> None:
        self.close()
        self.app.open_settings(tab="more")

    def close(self) -> None:
        if IS_WINDOWS:
            try:
                set_autostart(bool(self.auto_var.get()))
            except OSError as exc:
                log_error(f"자동 실행 설정 실패: {exc}")
        self.app.cfg["welcomed"] = True
        self.app.save()
        self.destroy()


def kind_tabs(dlg, current: str, on_switch) -> None:
    """창 맨 위의 [일정 | 할 일] 단추. 회색 바탕 안에서 고른 쪽만 진한 남색에 흰 글씨로 채워져요."""
    px = dlg.app.px
    bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
    family = tkfont.nametofont("TkDefaultFont").actual("family")  # 창의 다른 글씨와 같은 글꼴
    f_on = tkfont.Font(dlg, family=family, size=10, weight="bold")
    f_off = tkfont.Font(dlg, family=family, size=10)
    dlg._tab_fonts = (f_on, f_off)
    items = (("event", "일정"), ("todo", "할 일"))
    seg = max(f_on.measure(text) for _v, text in items) + px(40)
    h, pad = px(30), px(3)
    width = seg * len(items) + pad * 2
    track, fill, ink, ink_off = "#E3E1DC", "#2D4B7A", "#FFFFFF", "#3C4043"
    bar = tk.Frame(dlg.frame, bg=bg)
    cv = tk.Canvas(bar, width=width, height=h, bg=bg, highlightthickness=0)
    cv.pack(side="left")
    state = {"hover": None}

    def at(x: float) -> str | None:
        i = int((x - pad) // seg)
        return items[i][0] if 0 <= i < len(items) else None

    def draw() -> None:
        cv.delete("all")
        round_rect(cv, 0, 0, width, h, h / 2, fill=track, outline="")
        for i, (value, text) in enumerate(items):
            x0, x1 = pad + i * seg, pad + (i + 1) * seg
            on = value == current
            if on or state["hover"] == value:
                round_rect(cv, x0, pad, x1, h - pad, (h - 2 * pad) / 2,
                           fill=fill if on else blend(fill, track, 0.82), outline="")
            cv.create_text((x0 + x1) / 2, h / 2, text=text, font=f_on if on else f_off, fill=ink if on else ink_off)

    def motion(e) -> None:
        value = at(e.x)
        hover = value if value != current else None
        if hover != state["hover"]:
            state["hover"] = hover
            cv.config(cursor="hand2" if hover else "")
            draw()

    def leave(_e) -> None:
        state["hover"] = None
        cv.config(cursor="")
        draw()

    def click(e) -> None:
        value = at(e.x)
        if value and value != current:
            on_switch(value)

    cv.bind("<Motion>", motion)
    cv.bind("<Leave>", leave)
    cv.bind("<Button-1>", click)
    draw()
    bar.grid(row=dlg.row, column=0, columnspan=3, sticky="w", pady=(0, px(10)))
    dlg.row += 1


class TodoDialog(AttachMixin, _Dialog):
    """할 일 창 (Google 캘린더의 할 일과 같은 모양): 제목 · 날짜 · 종일/시간 · 기한 · 색 · 설명 · 목록"""

    def __init__(self, app: App, item: dict | None = None, parent: dict | None = None, prefill: dict | None = None):
        super().__init__(app, "할 일 고치기" if item else ("하위 할 일 추가" if parent else "할 일 추가"))
        px = app.px
        self.item, self.parent = item, parent
        prefill = prefill or {}
        if item is None and parent is None:
            kind_tabs(self, "todo", self._switch_kind)
        if parent:
            self.hint("상위 할 일: " + (parent.get("text") or "").splitlines()[0])
        self.title_e = self.field("제목", ttk.Entry(self.frame, width=40))
        self.title_e.bind("<Return>", lambda e: (self.add(), "break")[1])
        self.title_e.bind("<KP_Enter>", lambda e: (self.add(), "break")[1])
        when = ttk.Frame(self.frame)
        self.due_e = ttk.Entry(when, width=12)
        self.due_e.pack(side="left")
        ttk.Button(when, text="달력", width=5, command=self._open_calendar).pack(side="left", padx=(px(4), px(8)))
        for text, days in (("오늘", 0), ("내일", 1), ("다음 주", 7)):
            ttk.Button(when, text=text, width=6, command=lambda d=days: self._set_due(app.today + timedelta(days=d))
                       ).pack(side="left", padx=(0, px(2)))
        ttk.Button(when, text="없음", width=5, command=lambda: self._set_due(None)).pack(side="left")
        self.field("날짜", when, stretch=False)
        times = ttk.Frame(self.frame)
        self.allday_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(times, text="종일", variable=self.allday_var, command=self._toggle_time).pack(
            side="left", padx=(0, px(10)))
        self.start_e = TimeEntry(times, on_change=self._start_changed)
        self.start_e.pack(side="left")
        ttk.Label(times, text="~").pack(side="left", padx=px(4))
        self.end_e = TimeEntry(times)
        self.end_e.pack(side="left")
        self.field("시간", times, stretch=False)
        dl = ttk.Frame(self.frame)
        self.deadline_btn = ttk.Button(dl, text="마감일 추가", command=self._add_deadline)
        self.deadline_e = ttk.Entry(dl, width=12)
        self.deadline_cal = ttk.Button(dl, text="달력", width=5, command=self._open_deadline_calendar)
        self.deadline_x = ttk.Button(dl, text="✕", width=3, command=self._clear_deadline)
        self.field("기한", dl, stretch=False)
        self._show_deadline(False)
        bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        colors = ttk.Frame(self.frame)
        self.color = (item or {}).get("color") if item else app.cfg.get("todo_color", "green")
        if self.color not in TODO_COLOR_HEX and not _clean_color(self.color):
            self.color = "green" if not item else ""
        self.dots = {}
        for key, _hex, name in TODO_COLORS:
            dot = tk.Canvas(colors, width=px(24), height=px(24), highlightthickness=0, bg=bg, cursor="hand2")
            dot.pack(side="left", padx=(0, px(4)))
            dot.bind("<Button-1>", lambda e, k=key: self._pick_color(k))
            Tooltip(dot, name, app)
            self.dots[key] = dot
        self._draw_dots()
        self.field("색", colors, stretch=False)
        self.desc_t = self.field("설명", tk.Text(self.frame, width=40, height=3, wrap="word", font="TkTextFont",
                                               relief="solid", bd=1, highlightthickness=0, padx=px(4), pady=px(3)))
        self.desc_t.bind("<Tab>", lambda e: (e.widget.tk_focusNext().focus_set(), "break")[1])
        self._build_attach_row(self.desc_t)
        if app.service._google_api() is None:
            self._set_attach(False, "파일을 붙이려면 Google 계정으로 로그인해야 해요.")
        self.list_cb, self.lists = None, []
        if app.tasks_mode() and parent is None:
            self.lists = list(getattr(app, "_tasks_lists", [])) or [{"id": "@default", "title": "내 할 일"}]
            self.list_cb = self.field("목록", ttk.Combobox(self.frame, state="readonly", width=24,
                                                         values=[tl["title"] for tl in self.lists]), stretch=False)
            current = (item or {}).get("task_list") or getattr(app, "_tasks_default", "")
            self.list_cb.current(next((i for i, tl in enumerate(self.lists) if tl["id"] == current), 0))
            if item:
                self.list_cb.state(["disabled"])  # 다른 목록으로 옮기기는 Tasks 앱에서 해요
        self.hint("제목에서 Enter를 누르면 " + ("저장해요" if item else "추가해요") + ". 날짜는 비워 두어도 돼요. "
                  "'기한'은 꼭 끝내야 하는 날이에요. 날짜가 지나면 할 일이 오늘로 넘어와 보여요.")
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="닫기", command=self.destroy).pack(side="right")
        ttk.Button(buttons, text="저장" if item else "추가", command=self.add).pack(side="right", padx=(0, px(6)))
        if item:
            lines = (item.get("text") or "").splitlines() or [""]
            self.title_e.insert(0, lines[0])
            self.desc_t.insert("1.0", "\n".join(lines[1:]).strip())
            if item.get("due"):
                self.due_e.insert(0, item["due"])
            if item.get("due") and item.get("time"):
                self.allday_var.set(False)
                self.start_e.set(item["time"])
                self.end_e.set(item.get("end_time", ""))
            if item.get("deadline"):
                self._show_deadline(True)
                self.deadline_e.insert(0, item["deadline"])
            self.attachments = [dict(x) for x in item.get("attachments") or []]
            self._render_attachments()
        else:
            if prefill.get("files"):
                self.new_files = list(prefill["files"])
                self._render_attachments()
            if prefill.get("title"):
                self.title_e.insert(0, prefill["title"])
            if prefill.get("desc"):
                self.desc_t.insert("1.0", prefill["desc"])
            if prefill.get("date"):
                self.due_e.insert(0, prefill["date"].isoformat())
            if prefill.get("allday") is False and prefill.get("start"):
                self.allday_var.set(False)
                self.start_e.set(prefill["start"])
                self.end_e.set(prefill.get("end", ""))
        self._start_seen = parse_time(self.start_e.get())
        self._toggle_time()
        self.show()
        self.title_e.focus_set()

    # ── 일정으로 바꾸기 ──
    def _gather(self) -> dict:
        return {"title": self.title_e.get().strip(), "desc": self.desc_t.get("1.0", "end").strip(),
                "date": parse_date(self.due_e.get(), self.app.today) if self.due_e.get().strip() else None,
                "allday": bool(self.allday_var.get()), "start": self.start_e.get().strip(), "end": self.end_e.get().strip(),
                "files": list(self.new_files)}

    def _switch_kind(self, kind: str) -> None:
        if kind == "event":
            prefill, app = self._gather(), self.app
            self.destroy()
            app.open_add(prefill.get("date") or app.today, prefill=prefill)

    # ── 시간 · 기한 ──
    def _toggle_time(self) -> None:
        on = not self.allday_var.get()
        if on and not self.start_e.get().strip():  # 처음 켜면 가까운 30분 눈금부터 30분
            due = parse_date(self.due_e.get(), self.app.today) if self.due_e.get().strip() else None
            now = datetime.now()
            if due == self.app.today and now.hour < 23:
                m = min((now.hour * 60 + now.minute) // 30 * 30 + 30, 23 * 60)
            else:
                m = 9 * 60
            self.start_e.set(f"{m // 60:02d}:{m % 60:02d}")
            self.end_e.set(f"{(m + 30) // 60:02d}:{(m + 30) % 60:02d}")
            self._start_seen = parse_time(self.start_e.get())
        for w in (self.start_e, self.end_e):
            w.configure(state="normal" if on else "disabled")

    def _start_changed(self) -> None:
        new = parse_time(self.start_e.get())
        if not new:
            return
        old, end = getattr(self, "_start_seen", None), parse_time(self.end_e.get())
        length = 30
        if old and end:
            gap = (end.hour * 60 + end.minute) - (old.hour * 60 + old.minute)
            if gap > 0:
                length = gap
        if old != new:
            m = min(new.hour * 60 + new.minute + length, 23 * 60 + 59)
            self.end_e.set(f"{m // 60:02d}:{m % 60:02d}")
        self._start_seen = new

    def _show_deadline(self, on: bool) -> None:
        for w in (self.deadline_btn, self.deadline_e, self.deadline_cal, self.deadline_x):
            w.pack_forget()
        if on:
            self.deadline_e.pack(side="left")
            self.deadline_cal.pack(side="left", padx=(self.app.px(4), self.app.px(4)))
            self.deadline_x.pack(side="left")
        else:
            self.deadline_btn.pack(side="left")
        self._deadline_on = on

    def _add_deadline(self) -> None:
        self._show_deadline(True)
        base = parse_date(self.due_e.get(), self.app.today) if self.due_e.get().strip() else None
        self.deadline_e.delete(0, "end")
        self.deadline_e.insert(0, (base or self.app.today).isoformat())
        self.deadline_e.focus_set()

    def _clear_deadline(self) -> None:
        self.deadline_e.delete(0, "end")
        self._show_deadline(False)

    def _open_deadline_calendar(self) -> None:
        current = parse_date(self.deadline_e.get(), self.app.today) or self.app.today

        def picked(d: date | None) -> None:
            self.deadline_e.delete(0, "end")
            if d:
                self.deadline_e.insert(0, d.isoformat())

        DatePopup(self, self.app, current, picked, self.deadline_e.winfo_rootx(),
                  self.deadline_e.winfo_rooty() + self.deadline_e.winfo_height() + 2)

    def _draw_dots(self) -> None:
        px = self.app.px
        for key, dot in self.dots.items():
            dot.delete("all")
            c, r = px(12), px(7)
            if key == self.color:
                dot.create_oval(c - px(11), c - px(11), c + px(11), c + px(11), outline=TODO_COLOR_HEX[key],
                                width=max(2, px(2)))
            dot.create_oval(c - r, c - r, c + r, c + r, fill=TODO_COLOR_HEX[key], outline="")

    def _pick_color(self, key: str) -> None:
        self.color = key
        self._draw_dots()

    def _set_due(self, d: date | None) -> None:
        self.due_e.delete(0, "end")
        if d:
            self.due_e.insert(0, d.isoformat())
        elif not self.allday_var.get():  # 날짜가 없으면 시간도 없어요
            self.allday_var.set(True)
            self._toggle_time()

    def _open_calendar(self) -> None:
        current = parse_date(self.due_e.get(), self.app.today) or self.app.today
        DatePopup(self, self.app, current, self._set_due,
                  self.due_e.winfo_rootx(), self.due_e.winfo_rooty() + self.due_e.winfo_height() + 2)

    def add(self) -> None:
        title = self.title_e.get().strip()
        if not title:
            return self.say("제목을 적어 주세요.", error=True)
        raw = self.due_e.get().strip()
        due = parse_date(raw, self.app.today) if raw else None
        if raw and due is None:
            return self.say("날짜를 2026-11-23이나 11/23처럼 적어 주세요.", error=True)
        at = until = None
        if not self.allday_var.get():
            if not due:
                return self.say("시간을 넣으려면 날짜도 정해 주세요.", error=True)
            at = parse_time(self.start_e.get().strip())
            if at is None:
                return self.say("시작 시간을 15:00이나 오후 3시처럼 적어 주세요.", error=True)
            raw_end = self.end_e.get().strip()
            until = parse_time(raw_end) if raw_end else None
            if raw_end and until is None:
                return self.say("끝나는 시간을 15:30이나 오후 3시 반처럼 적어 주세요.", error=True)
            if until and until <= at:
                return self.say("끝나는 시간이 시작 시간보다 늦어야 해요.", error=True)
        deadline = None
        if getattr(self, "_deadline_on", False) and self.deadline_e.get().strip():
            deadline = parse_date(self.deadline_e.get().strip(), self.app.today)
            if deadline is None:
                return self.say("기한을 2026-12-01이나 12/1처럼 적어 주세요.", error=True)
        desc = self.desc_t.get("1.0", "end").strip()
        text = title + ("\n" + desc if desc else "")
        extra = {"end_time": f"{until.hour:02d}:{until.minute:02d}" if until else "",
                 "deadline": deadline.isoformat() if deadline else "", "attachments": list(self.attachments)}
        if self.list_cb is not None and self.item is None:
            extra["task_list"] = self.lists[max(0, self.list_cb.current())]["id"]
        if not self.new_files:
            return self._finish(text, title, due, at, extra)
        if getattr(self, "_uploading", False):
            return
        self._uploading = True
        self.say("파일을 올리는 중…")
        files = list(self.new_files)

        def uploaded(result, err) -> None:
            self._uploading = False
            if not self.winfo_exists():
                return
            if err is not None:
                return self.say(str(err) if isinstance(err, SyncError) else "파일을 올리지 못했어요.", error=True)
            self.attachments += result
            self.new_files = []
            extra["attachments"] = list(self.attachments)
            self._finish(text, title, due, at, extra)

        self.app.worker.submit(self.app.service.upload_attachments, files, self._upload_progress, callback=uploaded)

    def _finish(self, text: str, title: str, due, at, extra: dict) -> None:
        if self.color:
            self.app.cfg["todo_color"] = self.color
        if self.item:
            self.app.save()
            self.app.update_todo(self.item["id"], text, due, self.color, at, extra)
            self.destroy()
            return
        self.app.cfg["last_calendar"] = TODO_CHIP  # 다음에도 '할 일' 탭으로 열려요
        self.app.save()
        app = self.app
        app.add_todo(text, due, self.color, at, self.parent["id"] if self.parent else None, extra)
        self.destroy()  # 추가하면 창을 닫아요
        app.show_flash(f"할 일을 추가했어요: {title}")


def load_private_fonts() -> int:
    """assets/fonts의 글꼴(경기천년체)을 이 프로그램 안에서만 쓸 수 있게 불러와요. 컴퓨터에 설치하지 않아도 돼요."""
    folder = resource_path("assets", "fonts")
    if not os.path.isdir(folder):
        return 0
    count = 0
    for name in sorted(os.listdir(folder)):
        if name.lower().endswith((".ttf", ".otf")) and IS_WINDOWS:
            try:
                count += int(ctypes.windll.gdi32.AddFontResourceExW(os.path.join(folder, name), 0x10, 0) > 0)  # FR_PRIVATE
            except Exception as exc:
                log_error(f"글꼴을 불러오지 못함 ({name}): {exc!r}")
    return count


def enable_file_drop(widget, on_files) -> bool:
    """파일을 끌어다 놓을 수 있게 해요 (tkinterdnd2가 있을 때). 안 되면 False — 그때는 '파일 넣기…' 단추를 써요."""
    try:
        from tkinterdnd2 import TkinterDnD, DND_FILES
        root = widget._root()
        if not getattr(root, "_cw_dnd", False):
            TkinterDnD._require(root)
            root._cw_dnd = True
        widget.drop_target_register(DND_FILES)
        widget.dnd_bind("<<Drop>>", lambda e: (on_files(list(widget.tk.splitlist(e.data))), e.action)[1])
        return True
    except Exception as exc:
        log_error(f"끌어다 놓기를 켜지 못함: {exc!r}")
        return False


class TimeEntry(ttk.Entry):
    """시간을 직접 적는 칸: 9:05, 1505, 오후 3시 5분 … ↑ ↓ 키나 마우스 휠로 5분씩, Page Up/Down으로 1시간씩 바꿔요."""

    def __init__(self, master, width: int = 11, on_change=None):
        super().__init__(master, width=width)
        self.on_change = on_change
        for seq, step in (("<Up>", 5), ("<Down>", -5), ("<Prior>", 60), ("<Next>", -60)):
            self.bind(seq, lambda e, s_=step: self.step(s_))
        self.bind("<MouseWheel>", lambda e: self.step(5 if e.delta > 0 else -5))
        self.bind("<Button-4>", lambda e: self.step(5))
        self.bind("<Button-5>", lambda e: self.step(-5))
        self.bind("<FocusOut>", lambda e: self.tidy())

    def set(self, value: str) -> None:
        disabled = str(self.cget("state")) == "disabled"
        if disabled:
            self.configure(state="normal")
        self.delete(0, "end")
        self.insert(0, value or "")
        if disabled:
            self.configure(state="disabled")

    def step(self, minutes: int):
        if str(self.cget("state")) == "disabled":
            return "break"
        t = parse_time(self.get())
        total = t.hour * 60 + t.minute if t else 9 * 60
        if t and abs(minutes) == 5 and total % 5:  # 5분 단위가 아니면 먼저 5분 눈금에 맞춰요
            total = (total // 5 + (1 if minutes > 0 else 0)) * 5
        elif t:
            total += minutes
        total %= 24 * 60
        self.set(f"{total // 60:02d}:{total % 60:02d}")
        if self.on_change:
            self.on_change()
        return "break"

    def tidy(self) -> None:
        """'905'나 '오후 3시 5분'처럼 적으면 '15:05' 모양으로 정리해요."""
        text = self.get().strip()
        t = parse_time(text) if text else None
        if t:
            neat = f"{t.hour:02d}:{t.minute:02d}"
            if neat != text:
                self.set(neat)
            if self.on_change:
                self.on_change()


class AfterschoolRulesDialog(_Dialog):
    """엑셀의 표시('특', '전1' …)를 어떤 이름과 시간의 일정으로 넣을지 정해요."""

    def __init__(self, app: App, on_saved=None):
        super().__init__(app, "방과후 규칙")
        px = app.px
        self.on_saved = on_saved
        self.hint("엑셀 칸에 적힌 표시를 어떤 이름과 시간의 일정으로 넣을지 정해요. 시간은 18:20~21:00처럼 적고, "
                  "방학 시간을 비워 두면 평소 시간으로 넣어요.")
        self.table = ttk.Frame(self.frame)
        self.table.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(4), 0))
        self.row += 1
        for c, head in enumerate(("표시", "일정 이름", "평소 시간", "방학 시간", "색")):
            ttk.Label(self.table, text=head, foreground=HINT_GRAY).grid(row=0, column=c, sticky="w", padx=(0, px(6)))
        self.rows: list = []
        self._next_row = 1
        for rule in app.cfg["afterschool"]["rules"]:
            self._add_row(rule)
        more = ttk.Frame(self.frame)
        more.grid(row=self.row, column=0, columnspan=3, sticky="w", pady=(px(4), px(8)))
        self.row += 1
        ttk.Button(more, text="+ 줄 더하기", command=lambda: self._add_row({})).pack(side="left")
        self.months_e = self.field("방학인 달", ttk.Entry(self.frame, width=14), stretch=False)
        self.months_e.insert(0, ", ".join(str(m) for m in app.cfg["afterschool"].get("vacation_months") or []))
        self.hint("이 달에는 '방학 시간'으로 넣어요. 쉼표로 나눠 적어요. 예: 7, 1")
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="처음 값으로", command=self._reset).pack(side="left")
        ttk.Button(buttons, text="취소", command=self.destroy).pack(side="right")
        ttk.Button(buttons, text="저장", command=self.save).pack(side="right", padx=(0, px(6)))
        self.show()

    def _add_row(self, rule: dict) -> None:
        px = self.app.px
        r = self._next_row
        self._next_row += 1
        entries = []
        for c, (key, width) in enumerate((("code", 6), ("title", 14), ("time", 13), ("vacation", 13))):
            entry = ttk.Entry(self.table, width=width)
            entry.insert(0, str(rule.get(key, "")))
            entry.grid(row=r, column=c, sticky="w", padx=(0, px(6)), pady=px(2))
            entries.append(entry)
        row = {"entries": entries, "color": _clean_color(rule.get("color"))}
        bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        row["swatch"] = tk.Canvas(self.table, width=px(26), height=px(26), bg=bg, highlightthickness=0, cursor="hand2")
        row["swatch"].grid(row=r, column=4, padx=(0, px(6)))
        row["swatch"].bind("<Button-1>", lambda e: self._pick_color(row))
        self._draw_swatch(row)
        row["btn"] = ttk.Button(self.table, text="빼기", width=5, command=lambda: self._remove(row))
        row["btn"].grid(row=r, column=5, pady=px(2))
        self.rows.append(row)

    def _draw_swatch(self, row: dict) -> None:
        px, cv = self.app.px, row["swatch"]
        cv.delete("all")
        c, r = px(13), px(9)
        if row["color"]:
            cv.create_oval(c - r, c - r, c + r, c + r, fill=row["color"], outline="")
        else:
            cv.create_oval(c - r, c - r, c + r, c + r, outline="#9AA0A6", dash=(2, 2))

    def _pick_color(self, row: dict) -> None:
        cv = row["swatch"]

        def picked(color: str) -> None:
            row["color"] = color
            self._draw_swatch(row)

        ColorPickPopup(self, self.app, row["color"], picked, cv.winfo_rootx(), cv.winfo_rooty() + cv.winfo_height())

    def _remove(self, row: dict) -> None:
        for w in row["entries"] + [row["btn"], row["swatch"]]:
            w.destroy()
        self.rows.remove(row)

    def _reset(self) -> None:
        for row in list(self.rows):
            self._remove(row)
        for rule in DEFAULTS["afterschool"]["rules"]:
            self._add_row(rule)
        self.months_e.delete(0, "end")
        self.months_e.insert(0, ", ".join(str(m) for m in DEFAULTS["afterschool"]["vacation_months"]))

    def save(self) -> None:
        rules = []
        for row in self.rows:
            code, title, normal, vacation = (e.get().strip() for e in row["entries"])
            if not (code or title or normal or vacation):
                continue
            if not code or not title:
                return self.say("표시와 일정 이름을 모두 적어 주세요.", error=True)
            if not parse_time_range(normal):
                return self.say(f"'{title}'의 평소 시간을 18:20~21:00처럼 적어 주세요.", error=True)
            if vacation and not parse_time_range(vacation):
                return self.say(f"'{title}'의 방학 시간을 08:30~15:10처럼 적거나 비워 주세요.", error=True)
            rules.append({"code": code, "title": title, "time": normal, "vacation": vacation, "color": row["color"]})
        if not rules:
            return self.say("규칙을 하나 이상 적어 주세요.", error=True)
        months = [int(m) for m in re.findall(r"\d+", self.months_e.get())]
        if any(not 1 <= m <= 12 for m in months):
            return self.say("방학인 달은 1에서 12 사이로 적어 주세요.", error=True)
        self.app.cfg["afterschool"] = {"rules": rules, "vacation_months": months}
        self.app.save()
        callback = self.on_saved
        self.destroy()
        if callback:
            callback()


class NewCalendarDialog(_Dialog):
    """Google 계정에 새 캘린더를 만들어요."""

    def __init__(self, app: App):
        super().__init__(app, "새 캘린더 만들기")
        px = app.px
        self.hint("Google 계정에 새 캘린더를 만들어요. 아이폰에서도 보려면 만든 뒤 '아이폰에 보이게 하기'에서 체크해 주세요.")
        self.name_e = self.field("이름", ttk.Entry(self.frame, width=26))
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="취소", command=self.destroy).pack(side="right")
        self.ok_btn = ttk.Button(buttons, text="만들기", command=self.create)
        self.ok_btn.pack(side="right", padx=(0, px(6)))
        self.name_e.bind("<Return>", lambda e: self.create())
        self.show()
        self.name_e.focus_set()

    def create(self) -> None:
        name = self.name_e.get().strip()
        if not name:
            return self.say("캘린더 이름을 적어 주세요.", error=True)
        if any(c.name == name for c in self.app.calendars):
            return self.say("같은 이름의 캘린더가 이미 있어요.", error=True)
        self.ok_btn.state(["disabled"])
        self.say("만드는 중…")
        self.app.worker.submit(self.app.service.create_calendar, name, callback=self._done)

    def _done(self, result, error) -> None:
        if not self.winfo_exists():
            return
        if error is not None:
            self.ok_btn.state(["!disabled"])
            return self.say(str(error) if isinstance(error, SyncError) else "캘린더를 만들지 못했어요.", error=True)
        app, name = self.app, (result or {}).get("summary") or self.name_e.get().strip()
        self.destroy()
        app.refresh_all()
        app.show_flash(f"'{name}' 캘린더를 만들었어요")
        if messagebox.askyesno(APP_TITLE, f"'{name}' 캘린더를 만들었어요.\n아이폰에서도 보려면 열리는 페이지에서 "
                                          f"'{name}'을 체크하고 저장해 주세요.\n\n지금 열까요?", parent=app.host):
            webbrowser.open("https://calendar.google.com/calendar/syncselect")


class DeleteCalendarDialog(_Dialog):
    """내가 만든 Google 캘린더를 지워요. 이름을 똑같이 적어야 지울 수 있어요."""

    def __init__(self, app: App, key: str | None = None):
        super().__init__(app, "캘린더 지우기")
        px = app.px
        self.cands = [c for c in app.calendars if c.source == "Google" and c.owner and not c.primary]
        buttons = ttk.Frame(self.frame)
        if not self.cands:
            self.hint("지울 수 있는 캘린더가 없어요. 내가 만든 캘린더만 지울 수 있고, 계정의 기본 캘린더는 지울 수 없어요.")
            buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
            ttk.Button(buttons, text="닫기", command=self.destroy).pack(side="right")
            self.show()
            return
        self.hint("내가 만든 캘린더를 지워요. 그 안의 일정도 모두 함께 지워지고 되돌릴 수 없어요.")
        self.cal_cb = self.field("캘린더", ttk.Combobox(self.frame, state="readonly", width=28,
                                                     values=[c.name for c in self.cands]), stretch=False)
        self.cal_cb.current(next((i for i, c in enumerate(self.cands) if c.key == key), 0))
        self.message_area()
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="취소", command=self.destroy).pack(side="right")
        self.del_btn = ttk.Button(buttons, text="지우기", command=self.delete)
        self.del_btn.pack(side="right", padx=(0, px(6)))
        self.show()

    def delete(self) -> None:
        cal = self.cands[max(0, self.cal_cb.current())]
        app = self.app
        self.destroy()
        app.confirm_delete_calendar(cal)


class MemoDialog(_Dialog):
    """패널의 메모를 고치는 창. 위젯은 키보드를 받지 않아서 글자는 여기서 적어요. 닫으면 저절로 저장돼요."""

    def __init__(self, app: App):
        super().__init__(app, "메모")
        self.resizable(True, True)
        px = app.px
        box = ttk.Frame(self.frame)
        box.grid(row=self.row, column=0, columnspan=3, sticky="nsew")
        self.frame.rowconfigure(self.row, weight=1)
        self.row += 1
        self.text = tk.Text(box, width=54, height=14, wrap="word", font="TkTextFont", relief="solid", bd=1,
                            highlightthickness=0, padx=px(6), pady=px(5), undo=True)
        bar = ttk.Scrollbar(box, orient="vertical", command=self.text.yview)
        self.text.configure(yscrollcommand=bar.set)
        self.text.pack(side="left", fill="both", expand=True)
        bar.pack(side="right", fill="y")
        self.text.insert("1.0", app.memo_text)
        self.text.edit_reset()
        self.hint("적은 내용은 창을 닫을 때 저절로 저장돼요. Ctrl+S로 바로 저장할 수도 있어요.")
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="닫기", command=self.close).pack(side="right")
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self.bind("<Control-s>", lambda e: (self.save(), self.say("저장했어요."), "break")[2])
        self.show()
        self._place_over_memo()
        self.text.focus_set()
        self.text.mark_set("insert", "end-1c")

    def _place_over_memo(self) -> None:
        """패널의 메모 칸 자리에 창을 띄워서 그 자리에서 고치는 것처럼 보이게 해요."""
        box = getattr(self.app, "memo_box", None)
        if box is None or not box.winfo_ismapped():
            return
        self.update_idletasks()
        w, h = self.winfo_width(), self.winfo_height()
        x = box.winfo_rootx() + (box.winfo_width() - w) // 2
        y = box.winfo_rooty() + box.winfo_height() - h
        x = min(max(0, x), self.winfo_screenwidth() - w)
        y = min(max(0, y), self.winfo_screenheight() - h - self.app.px(48))
        self.geometry(f"+{x}+{y}")

    def save(self) -> None:
        self.app.set_memo(self.text.get("1.0", "end-1c"))

    def close(self) -> None:
        self.save()
        self.destroy()


class ColorPopup(tk.Toplevel):
    """위 막대의 캘린더를 오른쪽 클릭하면 뜨는 색 고르기 창"""

    def __init__(self, app: App, key: str, name: str, current: str, x: int, y: int):
        super().__init__(app)
        self.app, self.key = app, key
        px = app.px
        self.withdraw()
        self.title("색 바꾸기")
        self.transient(app.host if hasattr(app, "host") else app)
        self.resizable(False, False)
        bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        self.configure(bg=bg)
        body = tk.Frame(self, bg=bg, padx=px(12), pady=px(10))
        body.pack()
        tk.Label(body, text=app._chip_name(name), bg=bg, font=("TkDefaultFont", 10, "bold")).grid(
            row=0, column=0, columnspan=6, sticky="w")
        size = px(26)
        for i, color in enumerate(CAL_COLORS):
            cv = tk.Canvas(body, width=size, height=size, bg=bg, highlightthickness=0, cursor="hand2")
            cv.grid(row=1 + i // 6, column=i % 6, padx=px(2), pady=px(3))
            c, r = size / 2, px(9)
            if color.lower() == str(current).lower():
                cv.create_oval(c - px(12), c - px(12), c + px(12), c + px(12), outline=color, width=max(2, px(2)))
            cv.create_oval(c - r, c - r, c + r, c + r, fill=color, outline="")
            cv.bind("<Button-1>", lambda e, col=color: self._pick(col))
        links = tk.Frame(body, bg=bg)
        links.grid(row=3, column=0, columnspan=6, sticky="w", pady=(px(6), 0))
        cal = next((c for c in app.calendars if c.key == key), None)
        actions = [("원래 색으로", lambda: self._pick(None)),
                   ("이 캘린더만 보기", lambda: self._do(lambda: app.toggle_cal(key, only=True))),
                   ("모두 보기", lambda: self._do(lambda: app.toggle_cal(key, show_all=True)))]
        actions.append(("목록에서 숨기기", lambda: self._do(lambda: app.remove_from_list(key, name))))
        if cal is not None and cal.source == "Google" and cal.owner and not cal.primary:
            actions.append(("지우기…", lambda: self._do(lambda: app.confirm_delete_calendar(cal))))
        for text, cmd in actions:
            link = tk.Label(links, text=text, bg=bg, fg=LINK_BLUE, cursor="hand2")
            link.pack(side="left", padx=(0, px(10)))
            link.bind("<Button-1>", lambda e, c=cmd: c())
        tk.Label(body, text="위젯에서만 바뀌어요. 아이폰의 색은 Google 캘린더에서 바꿀 수 있어요.", bg=bg,
                 fg=HINT_GRAY, font=("TkDefaultFont", 8)).grid(row=4, column=0, columnspan=6, sticky="w",
                                                              pady=(px(4), 0))
        self.bind("<Escape>", lambda e: self.destroy())
        self.update_idletasks()
        x = min(max(0, x), self.winfo_screenwidth() - self.winfo_reqwidth())
        y = min(max(0, y), self.winfo_screenheight() - self.winfo_reqheight() - px(48))
        self.geometry(f"+{x}+{y}")
        self.deiconify()
        self.focus_set()

    def _pick(self, color: str | None) -> None:
        self.app.set_cal_color(self.key, color)
        self.destroy()

    def _do(self, fn) -> None:
        fn()
        self.destroy()


class ColorPickPopup(tk.Toplevel):
    """Google 24색 가운데 고르거나, 색을 빼거나, 직접 고르는 작은 창"""

    def __init__(self, master, app: App, current: str, on_pick, x: int, y: int):
        super().__init__(master)
        self.app, self.on_pick, self.current = app, on_pick, current
        px = app.px
        self.withdraw()
        self.title("색 고르기")
        self.transient(master)
        self.resizable(False, False)
        bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        self.configure(bg=bg)
        body = tk.Frame(self, bg=bg, padx=px(10), pady=px(8))
        body.pack()
        size = px(24)
        for i, (hx, name) in enumerate(GOOGLE_EVENT_COLORS):
            cv = tk.Canvas(body, width=size, height=size, bg=bg, highlightthickness=0, cursor="hand2")
            cv.grid(row=i // 12, column=i % 12)
            c, r = size / 2, px(8)
            if hx == current:
                cv.create_oval(c - px(11), c - px(11), c + px(11), c + px(11), outline=hx, width=max(2, px(2)))
            cv.create_oval(c - r, c - r, c + r, c + r, fill=hx, outline="")
            cv.bind("<Button-1>", lambda e, col=hx: self._pick(col))
            Tooltip(cv, name, app)
        links = tk.Frame(body, bg=bg)
        links.grid(row=2, column=0, columnspan=12, sticky="w", pady=(px(6), 0))
        for text, cmd in (("색 없음 (캘린더 색)", lambda: self._pick("")), ("직접 고르기…", self._custom)):
            link = tk.Label(links, text=text, bg=bg, fg=LINK_BLUE, cursor="hand2")
            link.pack(side="left", padx=(0, px(12)))
            link.bind("<Button-1>", lambda e, c=cmd: c())
        self.bind("<Escape>", lambda e: self.destroy())
        self.update_idletasks()
        x = min(max(0, x), self.winfo_screenwidth() - self.winfo_reqwidth())
        y = min(max(0, y), self.winfo_screenheight() - self.winfo_reqheight() - px(48))
        self.geometry(f"+{x}+{y}")
        self.deiconify()
        self.focus_set()

    def _pick(self, color: str) -> None:
        self.on_pick(color)
        self.destroy()

    def _custom(self) -> None:
        from tkinter import colorchooser
        chosen = colorchooser.askcolor(color=self.current or "#4285F4", parent=self, title="색 직접 고르기")
        color = _clean_color(chosen[1] if chosen else "")
        if color:
            self._pick(color)


class DatePopup(tk.Toplevel):
    """할 일 날짜를 고르는 작은 달력"""

    def __init__(self, master, app: App, current: date, on_pick, x: int, y: int):
        super().__init__(master)
        self.app, self.on_pick = app, on_pick
        self.month = current.replace(day=1)
        self.current = current
        self.withdraw()
        self.title("날짜 고르기")
        self.transient(master)
        self.resizable(False, False)
        self.bg = ttk.Style().lookup("TFrame", "background") or "#F0F0F0"
        self.configure(bg=self.bg)
        self.body = tk.Frame(self, bg=self.bg, padx=app.px(8), pady=app.px(6))
        self.body.pack()
        self.bind("<Escape>", lambda e: self.destroy())
        self._draw()
        self.geometry(f"+{x}+{y}")
        self.deiconify()
        self.focus_set()

    def _move(self, n: int) -> None:
        m = self.month.month - 1 + n
        self.month = date(self.month.year + m // 12, m % 12 + 1, 1)
        self._draw()

    def _draw(self) -> None:
        px, bg = self.app.px, self.bg
        for w in self.body.winfo_children():
            w.destroy()
        head = tk.Frame(self.body, bg=bg)
        head.grid(row=0, column=0, columnspan=7, sticky="ew", pady=(0, px(4)))
        ttk.Button(head, text="‹", width=3, command=lambda: self._move(-1)).pack(side="left")
        tk.Label(head, text=f"{self.month.year}년 {self.month.month}월", bg=bg,
                 font=("TkDefaultFont", 10, "bold")).pack(side="left", expand=True)
        ttk.Button(head, text="›", width=3, command=lambda: self._move(1)).pack(side="right")
        for c, name in enumerate("일월화수목금토"):
            fg = "#D93A3E" if c == 0 else "#2F6BD8" if c == 6 else "#555555"
            tk.Label(self.body, text=name, bg=bg, fg=fg, width=4).grid(row=1, column=c)
        first = self.month
        start = first - timedelta(days=(first.weekday() + 1) % 7)
        for i in range(42):
            d = start + timedelta(days=i)
            if d.month != first.month:
                continue
            col = i % 7
            selected, today = d == self.current, d == self.app.today
            cell = tk.Label(self.body, text=str(d.day), width=4, pady=px(3), cursor="hand2",
                            bg="#2F6BD8" if selected else bg,
                            fg="white" if selected else "#D93A3E" if col == 0 else "#2F6BD8" if col == 6 else "#222222",
                            font=("TkDefaultFont", 9, "bold" if today else "normal"),
                            relief="solid" if today and not selected else "flat", bd=1 if today else 0)
            cell.grid(row=2 + i // 7, column=col, padx=1, pady=1)
            cell.bind("<Button-1>", lambda e, day=d: self._pick(day))

    def _pick(self, d: date) -> None:
        self.on_pick(d)
        self.destroy()


class _Floating(tk.Toplevel):
    """테두리 없이 떠 있는 카드 창 (알림, 오늘 요약)"""

    def __init__(self, app: App):
        super().__init__(app)
        self.app = app
        t = app.t
        self.withdraw()
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        self.configure(bg=t["line"])
        self.card = tk.Frame(self, bg=t["panel"])
        self.card.pack(fill="both", expand=True, padx=1, pady=1)

    def label(self, parent, text: str, font: str, fg: str, wrap: int = 0, **pack) -> tk.Label:
        lbl = tk.Label(parent, text=text, font=self.app.fonts[font], bg=self.app.t["panel"], fg=fg,
                       anchor="w", justify="left", wraplength=wrap)
        lbl.pack(fill="x", **pack)
        return lbl

    def button(self, parent, text: str, command, primary: bool = False) -> tk.Label:
        t, px = self.app.t, self.app.px
        bg = t["accent"] if primary else blend(t["panel"], t["text"], 0.08)
        fg = t["accent_text"] if primary else t["text"]
        btn = tk.Label(parent, text=text, font=self.app.fonts["sub_bold"], bg=bg, fg=fg, cursor="hand2",
                       padx=px(14), pady=px(6))
        btn.bind("<Button-1>", lambda e: command())
        return btn


class MealCard(_Floating):
    """식판 단추를 누르면 뜨는 급식 카드. ‹ › 로 다른 날도 봐요 (주말은 건너뛰어요)."""

    def __init__(self, app: App, day: date, anchor=None):
        super().__init__(app)
        t, px = app.t, app.px
        self.day = day
        body = tk.Frame(self.card, bg=t["panel"])
        body.pack(fill="both", expand=True, padx=px(18), pady=px(14))
        tk.Frame(body, bg=t["panel"], width=px(300), height=1).pack()  # 최소 너비
        head = tk.Frame(body, bg=t["panel"])
        head.pack(fill="x")
        for text, step, side in (("‹", -1, "left"), ("›", 1, "right")):
            arrow = tk.Label(head, text=text, font=app.fonts["big"], bg=t["panel"], fg=t["muted"], cursor="hand2",
                             padx=px(6))
            arrow.pack(side=side)
            arrow.bind("<Button-1>", lambda e, s_=step: self.move(s_))
        self.title = tk.Label(head, font=app.fonts["big_bold"], bg=t["panel"], fg=t["text"])
        self.title.pack(side="left", expand=True)
        school = app.cfg.get("school") or {}
        sub = tk.Frame(body, bg=t["panel"])
        sub.pack(fill="x", pady=(px(2), px(8)))
        tk.Label(sub, text=school.get("name", ""), font=app.fonts["small"], bg=t["panel"], fg=t["muted"]).pack(side="left")
        for text, cmd in (("학교 바꾸기", self._change_school), ("오늘", lambda: self.go(app.today))):
            link = tk.Label(sub, text=text, font=app.fonts["link"], bg=t["panel"], fg=t["muted"], cursor="hand2")
            link.pack(side="right", padx=(px(10), 0))
            link.bind("<Button-1>", lambda e, c=cmd: c())
        tk.Frame(body, bg=t["line"], height=1).pack(fill="x")
        self.content = tk.Frame(body, bg=t["panel"])
        self.content.pack(fill="both", expand=True, pady=(px(8), 0))
        row = tk.Frame(body, bg=t["panel"])
        row.pack(fill="x", pady=(px(10), 0))
        self.button(row, "닫기", self.destroy, primary=True).pack(side="right")
        tk.Label(row, text="나이스 교육정보 개방 포털", font=app.fonts["small"], bg=t["panel"],
                 fg=blend(t["muted"], t["panel"], 0.3)).pack(side="left")
        self.bind("<Escape>", lambda e: self.destroy())
        self.go(day, place=anchor)

    def _change_school(self) -> None:
        app = self.app
        self.destroy()
        SchoolDialog(app, on_done=lambda: app.open_meal())

    def move(self, step: int) -> None:
        d = self.day + timedelta(days=step)
        while d.weekday() >= 5:  # 주말은 건너뛰어요
            d += timedelta(days=step)
        self.go(d)

    def go(self, day: date, place=None) -> None:
        app = self.app
        self.day = day
        label = f"{day.month}월 {day.day}일 ({WEEKDAY_SHORT[day.weekday()]})"
        self.title.config(text=label + (" · 오늘" if day == app.today else ""))
        self._fill([("muted", "불러오는 중…")])
        if place is not None or not self.winfo_ismapped():
            self._place(place)
        app.meals_for(day, lambda meals, err, d=day: self._show(d, meals, err))

    def _place(self, anchor) -> None:
        app = self.app
        self.update_idletasks()
        sw = max(self.winfo_reqwidth(), app.px(330))
        if anchor is not None and anchor.winfo_exists():
            x = anchor.winfo_rootx() + anchor.winfo_width() - sw
            y = anchor.winfo_rooty() + anchor.winfo_height() + app.px(6)
        else:
            wx, wy, ww, wh = work_area(app)
            x, y = wx + ww - sw - app.px(40), wy + app.px(60)
        self.geometry(f"+{max(0, x)}+{max(0, y)}")
        self.deiconify()
        self.lift()
        self.focus_force()

    def _fill(self, lines: list) -> None:
        t, px = self.app.t, self.app.px
        for w in self.content.winfo_children():
            w.destroy()
        for kind, text in lines:
            if kind == "meal":
                self.label(self.content, text, "sub_bold", t["accent"], pady=(px(6), px(2)))
            elif kind == "dish":
                self.label(self.content, text, "big_text", t["text"], wrap=px(300))
            elif kind == "cal":
                self.label(self.content, text, "small", t["muted"], pady=(px(2), 0))
            else:
                self.label(self.content, text, "sub", t["muted"], wrap=px(300), pady=(px(4), 0))

    def _show(self, day: date, meals, error) -> None:
        if not self.winfo_exists() or day != self.day:
            return
        if error is not None:
            self._fill([("muted", str(error) if isinstance(error, SyncError) else "급식 정보를 받지 못했어요.")])
        elif not meals:
            self._fill([("muted", "이날은 급식 정보가 없어요. 방학이거나 쉬는 날일 수 있어요.")])
        else:
            lines = []
            for meal in meals:
                lines.append(("meal", meal["name"]))
                lines += [("dish", d) for d in meal["dishes"]]
                if meal["cal"]:
                    lines.append(("cal", meal["cal"]))
            self._fill(lines)
        self.update_idletasks()
        self.geometry("")  # 내용에 맞게 높이를 맞춰요


class SchoolDialog(_Dialog):
    """급식을 볼 학교를 찾아서 골라요 (나이스 학교기본정보)."""

    def __init__(self, app: App, on_done=None):
        super().__init__(app, "우리 학교 찾기")
        px = app.px
        self.on_done = on_done
        self.results: list = []
        self.hint("학교 이름을 적고 찾기를 누르세요. 급식 메뉴는 나이스 교육정보 개방 포털에서 받아 와요.")
        row = ttk.Frame(self.frame)
        self.name_e = ttk.Entry(row, width=26)
        self.name_e.pack(side="left")
        self.name_e.insert(0, (app.cfg.get("school") or {}).get("name", ""))
        ttk.Button(row, text="찾기", command=self.search).pack(side="left", padx=(px(6), 0))
        self.field("학교 이름", row, stretch=False)
        box = ttk.Frame(self.frame)
        box.grid(row=self.row, column=0, columnspan=3, sticky="nsew", pady=(px(6), 0))
        self.row += 1
        self.tree = ttk.Treeview(box, columns=("name", "office", "address"), show="headings", height=6,
                                 selectmode="browse")
        for col, text, width in (("name", "학교", 170), ("office", "교육청", 110), ("address", "주소", 260)):
            self.tree.heading(col, text=text)
            self.tree.column(col, width=px(width), anchor="w")
        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<Double-1>", lambda e: self.choose())
        self.message_area()
        buttons = ttk.Frame(self.frame)
        buttons.grid(row=self.row, column=0, columnspan=3, sticky="ew", pady=(px(10), 0))
        ttk.Button(buttons, text="취소", command=self.destroy).pack(side="right")
        self.ok_btn = ttk.Button(buttons, text="이 학교로 하기", command=self.choose)
        self.ok_btn.pack(side="right", padx=(0, px(6)))
        self.ok_btn.state(["disabled"])
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.ok_btn.state(["!disabled"]))
        self.name_e.bind("<Return>", lambda e: self.search())
        self.show()
        self.name_e.focus_set()

    def search(self) -> None:
        name = self.name_e.get().strip()
        if len(name) < 2:
            return self.say("학교 이름을 두 글자 이상 적어 주세요.", error=True)
        self.say("찾는 중…")
        key = self.app.cfg.get("neis_key", "").strip()
        self.app.worker.submit(search_schools, name, key, callback=lambda res, err: self._found(res, err, key))

    def _found(self, results, error, key: str) -> None:
        if not self.winfo_exists():
            return
        self.tree.delete(*self.tree.get_children())
        self.ok_btn.state(["disabled"])
        if error is not None:
            return self.say(str(error) if isinstance(error, SyncError) else "학교를 찾지 못했어요.", error=True)
        self.results = results
        for i, sc in enumerate(results):
            self.tree.insert("", "end", iid=str(i), values=(sc["name"], sc["office_name"], sc["address"]))
        if not results:
            return self.say("찾는 학교가 없어요. 학교 이름을 정확히 적어 주세요. (예: 한빛고등학교)", error=True)
        if len(results) == 1:
            self.tree.selection_set("0")
        note = "학교를 고르고 '이 학교로 하기'를 누르세요."
        if len(results) >= 5 and not key:
            note += " 결과는 5개까지만 나와요. 안 보이면 이름을 더 자세히 적어 보세요."
        self.say(note)

    def choose(self) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        self.app.cfg["school"] = dict(self.results[int(sel[0])])
        self.app.save()
        callback = self.on_done
        self.destroy()
        if callback:
            callback()


class Toast(_Floating):
    """일정 시작 전 알림 (화면 오른쪽 아래)"""

    def __init__(self, app: App, ev: Event):
        super().__init__(app)
        t, px = app.t, app.px
        self.ev = ev
        tk.Frame(self.card, bg=ev.color, width=px(5)).pack(side="left", fill="y")
        body = tk.Frame(self.card, bg=t["panel"])
        body.pack(side="left", fill="both", expand=True, padx=px(16), pady=px(12))
        tk.Frame(body, bg=t["panel"], width=px(300), height=1).pack()  # 최소 너비
        self.lead = self.label(body, self._lead_text(), "small", t["accent"] if t["accent"] != t["panel"] else t["text"])
        self.label(body, ev.title, "big_bold", t["text"], wrap=px(300), pady=(px(2), 0))
        self.label(body, f"{fmt_time(ev.start)} ~ {fmt_time(ev.end)}", "sub", t["muted"])
        if ev.location:
            self.label(body, ev.location, "sub", t["muted"], wrap=px(300))
        row = tk.Frame(body, bg=t["panel"])
        row.pack(fill="x", pady=(px(10), 0))
        self.button(row, "5분 뒤 다시", self.snooze).pack(side="right")
        self.button(row, "확인", self.close, primary=True).pack(side="right", padx=(0, px(6)))
        self.deiconify()

    def _lead_text(self) -> str:
        minutes = int((self.ev.start - datetime.now().astimezone()).total_seconds() // 60) + 1
        if minutes <= -1:
            return "이미 시작했어요"
        if minutes <= 0:
            return "지금 시작해요"
        if minutes < 60:
            return f"{minutes}분 뒤 시작해요"
        return f"{minutes // 60}시간 {minutes % 60}분 뒤 시작해요" if minutes % 60 else f"{minutes // 60}시간 뒤 시작해요"

    def close(self) -> None:
        self.destroy()
        self.app.restack_toasts()

    def snooze(self) -> None:
        ev, app = self.ev, self.app
        self.close()
        app.after(5 * 60_000, lambda: app.show_toast(ev))


class UpdateCard(_Floating):
    """새 버전이 나왔을 때 (업데이트를 '알려만 주기'로 둔 경우)"""

    def __init__(self, app: App, info: dict):
        super().__init__(app)
        t, px = app.t, app.px
        self.info = info
        tk.Frame(self.card, bg=t["accent"], width=px(5)).pack(side="left", fill="y")
        body = tk.Frame(self.card, bg=t["panel"])
        body.pack(side="left", fill="both", expand=True, padx=px(16), pady=px(12))
        tk.Frame(body, bg=t["panel"], width=px(300), height=1).pack()  # 최소 너비
        self.label(body, "새 버전이 나왔어요", "small", t["accent"] if t["accent"] != t["panel"] else t["text"])
        self.label(body, f"캘린더 위젯 {info['version']}", "big_bold", t["text"], pady=(px(2), 0))
        self.label(body, f"지금 쓰는 버전은 {VERSION}이에요. 업데이트하면 위젯이 잠깐 닫혔다가 다시 켜져요.",
                   "sub", t["muted"], wrap=px(320))
        if info.get("page"):
            link = self.label(body, "무엇이 바뀌었는지 보기", "link", t["muted"], pady=(px(4), 0))
            link.config(cursor="hand2")
            link.bind("<Button-1>", lambda e: webbrowser.open(info["page"]))
        row = tk.Frame(body, bg=t["panel"])
        row.pack(fill="x", pady=(px(10), 0))
        self.button(row, "나중에", self.close).pack(side="right")
        self.button(row, "업데이트", self.update_now, primary=True).pack(side="right", padx=(0, px(6)))
        self.deiconify()

    def update_now(self) -> None:
        self.close()
        self.app.install_update(self.info)

    def close(self) -> None:
        self.destroy()
        self.app.restack_toasts()


class LoginCard(_Floating):
    """Google 로그인이 풀렸을 때 (테스트 중인 앱은 7일마다 풀려요). 단추 하나로 다시 로그인해요."""

    def __init__(self, app: App):
        super().__init__(app)
        t, px = app.t, app.px
        tk.Frame(self.card, bg=t["accent"], width=px(5)).pack(side="left", fill="y")
        body = tk.Frame(self.card, bg=t["panel"])
        body.pack(side="left", fill="both", expand=True, padx=px(16), pady=px(12))
        tk.Frame(body, bg=t["panel"], width=px(300), height=1).pack()  # 최소 너비
        self.label(body, "Google 캘린더", "small", t["accent"] if t["accent"] != t["panel"] else t["text"])
        self.label(body, LOGIN_EXPIRED, "big_bold", t["text"], pady=(px(2), 0))
        self.label(body, "아래 단추를 누르고, 브라우저에서 계정을 고른 뒤 '계속'을 누르면 돼요. "
                         "그동안 받아 둔 일정은 그대로 보여요.", "sub", t["muted"], wrap=px(320))
        row = tk.Frame(body, bg=t["panel"])
        row.pack(fill="x", pady=(px(10), 0))
        self.button(row, "나중에", self.close).pack(side="right")
        self.button(row, "다시 로그인", self.login, primary=True).pack(side="right", padx=(0, px(6)))
        self.deiconify()

    def login(self) -> None:
        app = self.app
        self.close()
        app.show_flash("브라우저에서 로그인을 기다리는 중이에요")
        app.google_sign_in(on_done=lambda res, err: app.show_flash(
            "다시 로그인했어요" if err is None else "로그인하지 못했어요. 설정의 Google 탭에서 다시 해 주세요"))

    def close(self) -> None:
        self.destroy()
        self.app.restack_toasts()


class EventCard(_Floating):
    """일정을 누르면 뜨는 자세히 보기 카드"""

    def __init__(self, app: App, ev: Event):
        super().__init__(app)
        t, px = app.t, app.px
        tk.Frame(self.card, bg=ev.color, width=px(5)).pack(side="left", fill="y")
        body = tk.Frame(self.card, bg=t["panel"])
        body.pack(side="left", fill="both", expand=True, padx=px(16), pady=px(12))
        tk.Frame(body, bg=t["panel"], width=px(300), height=1).pack()  # 최소 너비
        wrap = px(330)
        self.label(body, ev.title, "big_bold", t["text"], wrap=wrap)
        self.label(body, event_when(ev), "sub", t["muted"], wrap=wrap, pady=(px(2), 0))
        self.label(body, ev.cal_name if ev.source in ev.cal_name else f"{ev.cal_name} ({ev.source})",
                   "sub", t["muted"], wrap=wrap)
        if ev.location:
            self.label(body, f"장소: {ev.location}", "sub", t["text"], wrap=wrap, pady=(px(6), 0))
        if ev.notes:
            self.label(body, ev.notes[:600], "sub", t["text"], wrap=wrap, pady=(px(6), 0))
        row = tk.Frame(body, bg=t["panel"])
        row.pack(fill="x", pady=(px(10), 0))
        self.button(row, "닫기", self.destroy, primary=True).pack(side="right")
        if ev.kind == "event":
            self.button(row, "고치기", lambda: app.edit_event(ev)).pack(side="right", padx=(0, px(6)))
        self.update_idletasks()
        x, y, w, h = work_area(app)
        cw, ch = self.winfo_reqwidth(), self.winfo_reqheight()
        mx, my = app.winfo_pointerxy()
        nx = min(max(x + px(8), mx + px(12)), x + w - cw - px(8))
        ny = min(max(y + px(8), my - ch // 3), y + h - ch - px(8))
        self.geometry(f"+{nx}+{ny}")
        self.deiconify()


class SummaryWindow(_Floating):
    """컴퓨터를 켰을 때 보여 주는 오늘 일정과 할 일"""

    def __init__(self, app: App):
        super().__init__(app)
        t, px = app.t, app.px
        self.inner = tk.Frame(self.card, bg=t["panel"])
        self.inner.pack(fill="both", expand=True, padx=px(28), pady=px(24))
        self.bind("<Escape>", lambda e: self.destroy())
        self.refresh()
        self.update_idletasks()
        x, y, w, h = work_area(app)
        sw, sh = self.winfo_reqwidth(), self.winfo_reqheight()
        self.geometry(f"+{x + (w - sw) // 2}+{y + max(0, (h - sh) // 3)}")
        self.deiconify()
        self.lift()
        self.focus_force()

    def refresh(self) -> None:
        app, t, px = self.app, self.app.t, self.app.px
        for w in self.inner.winfo_children():
            w.destroy()
        d = app.today
        wrap = px(380)
        tk.Frame(self.inner, bg=t["panel"], width=px(400), height=1).pack()  # 최소 너비
        head = self.label(self.inner, f"{d.month}월 {d.day}일 {WEEKDAY_FULL[d.weekday()]}", "big",
                          t[app.tone(d)] if app.tone(d) != "text" else t["text"])
        head.bind("<ButtonPress-1>", self._drag_start)
        head.bind("<B1-Motion>", self._drag_move)
        events = [ev for ev in app.by_day.get(d, []) if ev.kind == "event"]
        todos = app.todos.open_items()
        sub = f"오늘 일정 {len(events)}개, 할 일 {len(todos)}개"
        if d in app.holidays:
            sub = f"{app.holidays[d]}, {sub}"
        self.label(self.inner, sub, "sub", t["muted"], pady=(px(2), px(4)))
        now = datetime.now().astimezone()
        upcoming = [ev for ev in events if not ev.all_day and ev.start > now]
        if upcoming:
            nxt = upcoming[0]
            minutes = int((nxt.start - now).total_seconds() // 60)
            when = f"{minutes}분 뒤" if minutes < 60 else f"{minutes // 60}시간 {minutes % 60}분 뒤"
            self.label(self.inner, f"다음 일정: {fmt_time(nxt.start)} {nxt.title} ({when})", "sub_bold",
                       t["accent"] if t["accent"] != t["panel"] else t["text"], wrap=wrap)

        self._section("일정")
        if not app.loaded_once and app.has_sources():
            self.label(self.inner, "일정을 아직 불러오지 못했어요. 인터넷 연결을 확인해 주세요.", "big_text",
                       t["muted"], wrap=wrap)
        elif not events:
            self.label(self.inner, "오늘은 일정이 없어요.", "big_text", t["muted"])
        for ev in events[:10]:
            row = tk.Frame(self.inner, bg=t["panel"])
            row.pack(fill="x", pady=px(3))
            tk.Frame(row, bg=ev.color, width=px(4)).pack(side="left", fill="y", padx=(0, px(10)))
            when = "종일" if ev.all_day or is_long(ev) else fmt_time(ev.start)
            tk.Label(row, text=when, font=app.fonts["big_text"], bg=t["panel"], fg=t["muted"], width=8,
                     anchor="w").pack(side="left", anchor="n")
            text_box = tk.Frame(row, bg=t["panel"])
            text_box.pack(side="left", fill="x", expand=True)
            past = not ev.all_day and ev.end <= now
            self.label(text_box, ev.title, "big_bold", t["muted"] if past else t["text"], wrap=px(280))
            if ev.location:
                self.label(text_box, ev.location, "sub", t["muted"], wrap=px(280))
        if len(events) > 10:
            self.label(self.inner, f"외 {len(events) - 10}개", "sub", t["muted"])

        self._section("할 일")
        if not todos:
            self.label(self.inner, "할 일이 없어요. 위젯 오른쪽 아래 '+ 할 일 추가'로 적을 수 있어요.", "big_text",
                       t["muted"], wrap=wrap)
        for item in todos[:12]:
            row = tk.Frame(self.inner, bg=t["panel"])
            row.pack(fill="x", pady=px(2))
            color = todo_hex(item.get("color", ""))
            if color:
                tk.Label(row, text="●", font=app.fonts["sub"], bg=t["panel"], fg=color).pack(
                    side="left", anchor="n", padx=(0, px(4)), pady=(px(3), 0))
            box = tk.Label(row, text=app.icons["box"], font=app.fonts["icon"], bg=t["panel"], fg=t["muted"],
                           cursor="hand2")
            box.pack(side="left", anchor="n", padx=(0, px(8)))
            box.bind("<Button-1>", lambda e, i=item["id"]: app.complete_todo(i))
            col = tk.Frame(row, bg=t["panel"])
            col.pack(side="left", fill="x", expand=True)
            self.label(col, item["text"], "big_text", t["text"], wrap=px(320))
            due = todo_due_label(item, app.today)
            if due:
                self.label(col, due[0], "sub", {"late": t["sun"], "soon": SOON_ORANGE}.get(due[1], t["muted"]))
        if len(todos) > 12:
            self.label(self.inner, f"외 {len(todos) - 12}개", "sub", t["muted"])

        footer = tk.Frame(self.inner, bg=t["panel"])
        footer.pack(fill="x", pady=(px(18), 0))
        self.button(footer, "확인", self.destroy, primary=True).pack(side="right")

    def _section(self, text: str) -> None:
        t, px = self.app.t, self.app.px
        tk.Frame(self.inner, bg=t["line"], height=1).pack(fill="x", pady=(px(14), px(8)))
        self.label(self.inner, text, "side_head", t["text"], pady=(0, px(4)))

    def _drag_start(self, e):
        self._drag = (e.x_root - self.winfo_x(), e.y_root - self.winfo_y())

    def _drag_move(self, e):
        self.geometry(f"+{e.x_root - self._drag[0]}+{e.y_root - self._drag[1]}")


# ───────────────────────── 시작 ─────────────────────────

SELFTEST_ICS = b"""BEGIN:VCALENDAR
VERSION:2.0
PRODID:-//selftest//KO
BEGIN:VTIMEZONE
TZID:Asia/Seoul
BEGIN:STANDARD
DTSTART:19700101T000000
TZOFFSETFROM:+0900
TZOFFSETTO:+0900
TZNAME:KST
END:STANDARD
END:VTIMEZONE
BEGIN:VEVENT
UID:selftest-1
DTSTAMP:20260101T000000Z
DTSTART;TZID=Asia/Seoul:20260105T093000
DTEND;TZID=Asia/Seoul:20260105T103000
RRULE:FREQ=WEEKLY;COUNT=3
SUMMARY:Selftest
END:VEVENT
END:VCALENDAR
"""


def selftest() -> int:
    """설치가 제대로 됐는지 확인해요:  calendar_widget.py --selftest"""
    import zoneinfo
    zoneinfo.reset_tzpath(to=[])  # 윈도우처럼 tzdata 패키지만 쓰게 해요
    zoneinfo.ZoneInfo.clear_cache()
    cal = icalendar.Calendar.from_ical(SELFTEST_ICS)
    events = parse_events(cal, date(2026, 1, 1), date(2026, 2, 1), cal_name="t", color="#000000", source="t")
    utc_hours = sorted(ev.start.astimezone(timezone.utc).hour for ev in events)
    assert len(events) == 3 and utc_hours == [0, 0, 0], (len(events), utc_hours)
    build_event_ics("X", "t", date(2026, 1, 1), date(2026, 1, 2), True)
    cal = RemoteCalendar("t", "t@x", "#000000", True, "Google")
    timed = google_api_event({"summary": "a", "start": {"dateTime": "2026-01-05T09:30:00+09:00"},
                              "end": {"dateTime": "2026-01-05T10:30:00+09:00"}}, cal, False)
    allday = google_api_event({"summary": "b", "start": {"date": "2026-01-05"}, "end": {"date": "2026-01-07"}},
                              cal, False)
    assert timed.start.astimezone(timezone.utc).hour == 0 and allday.all_day and (allday.end - allday.start).days == 2
    assert version_tuple("v2.10.1") > version_tuple("2.9.9")
    import importlib
    for module in ("olefile", "openpyxl", "pypdf"):  # 학사일정 파일을 읽는 부품이 설치 파일에 들어갔는지
        importlib.import_module(module)
    sample = ["2026학년도 학사일정", "3. 2.(월) 입학식", "4. 27.(월) ~ 4. 30.(목) 1학기 지필평가", "2. 12.(금) 졸업식"]
    raws = scan_schedule(sample)
    items = resolve_schedule(raws, guess_school_year(sample, raws, date(2026, 5, 1)))
    assert [(i["start"], i["end"]) for i in items] == [
        (date(2026, 3, 2), date(2026, 3, 2)), (date(2026, 4, 27), date(2026, 4, 30)),
        (date(2027, 2, 12), date(2027, 2, 12))], items
    assert [clean_dish(x) for x in ("자장소스(구리고)2.5.6.10.13.16.", "현미밥 (5.6)", "*돼지갈비찜 (10.13)",
                                    "우유 200ml", "비타민C 음료")] == \
        ["자장소스(구리고)", "현미밥", "돼지갈비찜", "우유 200ml", "비타민C 음료"]
    import tempfile
    from openpyxl import Workbook
    wb = Workbook()
    ws = wb.active
    ws.append(["2026학년도 방과후 수업 운영 일정표"])
    for month, mark in ((3, "전1"), (7, "전1")):
        ws.append([f"{month}월"])
        ws.append(["구분", None] + list(range(1, 32)))
        ws.append(["전공", "1학년"] + [None] * 8 + [mark])
    tmp = os.path.join(tempfile.gettempdir(), "cw_selftest.xlsx")
    wb.save(tmp)
    entries, texts = read_code_grid(tmp)
    os.remove(tmp)
    got, _ = afterschool_items(entries, DEFAULTS["afterschool"], 2026)
    assert [(i["title"], i["start"].strftime("%m-%d %H:%M"), i["end"].strftime("%H:%M")) for i in got] == [
        ("전공1", "03-09 18:20", "21:00"), ("전공1", "07-09 08:30", "15:10")], got
    grid = ["2026학년도 학사일정", "3", "1일(일):삼일절", "3일(화):개학식", "4", "5", "1일(수):행사",
            "29일(수)~5.1일(금):야영", "5", "6", "4일(월):재량휴업일"]  # 달력 모양 학사일정
    raws = scan_schedule(grid)
    got = [(i["start"], i["end"]) for i in resolve_schedule(raws, guess_school_year(grid, raws, date(2026, 5, 1)))]
    assert got == [(date(2026, 3, 1), date(2026, 3, 1)), (date(2026, 3, 3), date(2026, 3, 3)),
                   (date(2026, 4, 1), date(2026, 4, 1)), (date(2026, 4, 29), date(2026, 5, 1)),
                   (date(2026, 5, 4), date(2026, 5, 4))], got
    icon = os.path.exists(resource_path("assets", "icon.ico"))
    try:  # 끌어다 놓기 부품(tkdnd)이 프로그램 안에 들어 있나요?
        import tkinterdnd2
        dnd_dir = os.path.join(os.path.dirname(tkinterdnd2.__file__), "tkdnd")
        dnd = "yes" if os.path.isdir(dnd_dir) and os.listdir(dnd_dir) else "no files"
    except Exception:
        dnd = "no"
    assert split_attachment_block("메모\n\n[첨부 파일]\n• a.pdf\n  https://x") == "메모"
    print(f"selftest ok: version {VERSION}, google login {'on' if GOOGLE_CLIENT_ID else 'off'}, "
          f"updates {UPDATE_REPO or 'off'}, icon {'yes' if icon else 'no'}, drag-drop {dnd}, "
          f"fonts {len([n for n in os.listdir(resource_path('assets', 'fonts')) if n.endswith('.ttf')]) if os.path.isdir(resource_path('assets', 'fonts')) else 0}, "
          f"{'system certificates' if truststore else 'certifi'}")
    return 0


def main() -> int:
    if "--selftest" in sys.argv:
        return selftest()
    enable_dpi_awareness()
    if truststore is None:
        log_error("truststore를 쓰지 못해서 기본 인증서 목록으로 연결해요.")
    if not acquire_single_instance():
        root = tk.Tk()
        root.withdraw()
        messagebox.showinfo(APP_TITLE, "캘린더 위젯이 이미 실행 중이에요.\n\n"
                                       "예전에 run.bat으로 켠 위젯이 있다면, 그 위젯을 오른쪽 클릭 → 종료로 닫고 "
                                       "다시 실행해 주세요.")
        root.destroy()
        return 0
    try:
        App(load_config()).mainloop()
    except Exception:
        log_error("실행 오류\n" + traceback.format_exc())
        raise
    return 0


if __name__ == "__main__":
    sys.exit(main())

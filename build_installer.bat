@echo off
setlocal
title 캘린더 위젯 설치 파일 만들기
cd /d "%~dp0"

set "PY="
where py >nul 2>nul && set "PY=py -3"
if not defined PY (
  where python >nul 2>nul && set "PY=python"
)
if not defined PY goto nopython

set "ISCC="
if exist "%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe" set "ISCC=%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe"
if not defined ISCC if exist "%ProgramFiles%\Inno Setup 6\ISCC.exe" set "ISCC=%ProgramFiles%\Inno Setup 6\ISCC.exe"
if not defined ISCC if exist "%LocalAppData%\Programs\Inno Setup 6\ISCC.exe" set "ISCC=%LocalAppData%\Programs\Inno Setup 6\ISCC.exe"
if not defined ISCC if exist "%ProgramFiles%\Inno Setup 7\ISCC.exe" set "ISCC=%ProgramFiles%\Inno Setup 7\ISCC.exe"
if not defined ISCC if exist "%ProgramFiles(x86)%\Inno Setup 7\ISCC.exe" set "ISCC=%ProgramFiles(x86)%\Inno Setup 7\ISCC.exe"
if not defined ISCC if exist "%LocalAppData%\Programs\Inno Setup 7\ISCC.exe" set "ISCC=%LocalAppData%\Programs\Inno Setup 7\ISCC.exe"
if not defined ISCC goto noinno

echo.
echo  이번에 만들 설치 파일:
%PY% tools\make_build_info.py
if errorlevel 1 goto fail
set /p VERSION=<build_version.txt

echo.
echo  필요한 도구를 설치하고 있어요...
%PY% -m pip install --disable-pip-version-check -r requirements.txt pyinstaller
if errorlevel 1 goto fail
%PY% calendar_widget.py --selftest
if errorlevel 1 goto fail

echo.
echo  프로그램을 만들고 있어요. 1~2분쯤 걸려요...
%PY% -m PyInstaller --noconfirm --clean --windowed --name CalendarWidget --icon assets\icon.ico --add-data "assets\icon.ico;assets" --add-data "assets\fonts;assets\fonts" --collect-data tzdata --collect-all tkinterdnd2 calendar_widget.py
if errorlevel 1 goto fail

echo.
echo  설치 파일을 만들고 있어요...
"%ISCC%" /DMyAppVersion=%VERSION% installer\CalendarWidget.iss
if errorlevel 1 goto fail

echo.
echo  다 만들었어요!
echo  %~dp0installer\Output\CalendarWidget-Setup-%VERSION%.exe
echo.
echo  방금 열린 폴더의 CalendarWidget-Setup-%VERSION%.exe를 더블클릭하면 설치돼요.
echo  다른 사람에게는 이 파일 하나만 나눠 주면 돼요.
echo.
start "" "%~dp0installer\Output"
pause
exit /b 0

:nopython
echo.
echo  [!] 파이썬을 찾지 못했어요. README의 '파이썬 설치'를 먼저 해 주세요.
echo.
pause
exit /b 1

:noinno
echo.
echo  [!] 설치 파일을 만드는 프로그램 Inno Setup이 없어요.
echo      아무 키나 누르면 Inno Setup 6.7.4 설치 파일을 받아요.
echo      받은 파일을 실행해서 설치한 뒤, 이 파일을 다시 더블클릭해 주세요.
echo.
pause
start "" "https://github.com/jrsoftware/issrc/releases/download/is-6_7_4/innosetup-6.7.4.exe"
exit /b 1

:fail
echo.
echo  [!] 만들지 못했어요. 위에 나온 내용을 알려 주시면 도와드릴게요.
echo.
pause
exit /b 1

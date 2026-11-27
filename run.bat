@echo off
setlocal
title 캘린더 위젯
cd /d "%~dp0"

if not exist "%~dp0calendar_widget.py" goto notextracted
if not exist "%~dp0requirements.txt" goto notextracted

set "PY="
set "PYW="
where py >nul 2>nul && (set "PY=py -3" & set "PYW=pyw -3")
if not defined PY (
  where python >nul 2>nul && (set "PY=python" & set "PYW=pythonw")
)
if not defined PY goto nopython
%PY% -c "import tkinter"
if errorlevel 1 goto nopython

echo.
echo  캘린더 위젯에 필요한 부품을 설치하고 있어요.
echo  처음 한 번은 1~2분쯤 걸려요. 창을 닫지 말고 기다려 주세요.
echo.
%PY% -m pip install --disable-pip-version-check -r requirements.txt
if errorlevel 1 goto pipfail

%PY% calendar_widget.py --selftest >nul 2>nul
if errorlevel 1 goto selftestfail

start "" %PYW% "%~dp0calendar_widget.py"
echo.
echo  위젯을 실행했어요. 이 창은 잠시 뒤 저절로 닫혀요.
timeout /t 4 >nul
exit /b 0

:notextracted
echo.
echo  [!] 압축을 푼 폴더에서 실행해 주세요.
echo      CalendarWidget.zip을 오른쪽 클릭해서 '모두 압축 풀기'를 누른 뒤,
echo      풀린 폴더 안의 run.bat을 다시 더블클릭해 주세요.
echo.
pause
exit /b 1

:nopython
echo.
echo  [!] 파이썬을 찾지 못했어요.
echo      README의 '1. 파이썬 설치'를 따라 설치한 뒤 run.bat을 다시 실행해 주세요.
echo      설치했는데도 이 메시지가 나오면 컴퓨터를 다시 시작한 뒤 실행해 보세요.
echo.
pause
exit /b 1

:pipfail
echo.
echo  [!] 부품을 내려받지 못했어요.
echo      인터넷 연결을 확인하고 run.bat을 다시 실행해 주세요.
echo      회사나 학교 네트워크에서는 막혀 있을 수 있어요.
echo.
pause
exit /b 1

:selftestfail
echo.
echo  [!] 설치 확인 중에 문제가 생겼어요. 아래 내용을 알려 주시면 도와드릴게요.
echo.
%PY% calendar_widget.py --selftest
echo.
pause
exit /b 1

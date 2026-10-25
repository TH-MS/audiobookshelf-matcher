@echo off
setlocal
cd /d "%~dp0"

set "APPNAME=Audiobookshelf Matcher Portable"

echo ============================================
echo  Building %APPNAME%
echo ============================================

if not exist app.py (
    echo ERROR: app.py must be in the same folder as this script.
    pause & exit /b 1
)

REM --- Find Python ---
set "PY="
where py >nul 2>&1 && set "PY=py -3"
if not defined PY (
    where python >nul 2>&1 && set "PY=python"
)
if not defined PY (
    echo ERROR: Python 3.10+ not found. Install it from https://www.python.org/downloads/
    echo        and tick "Add python.exe to PATH".
    pause & exit /b 1
)

REM --- Virtual environment ---
if exist venv rmdir /s /q venv
%PY% -m venv venv || (echo Failed to create venv & pause & exit /b 1)
call venv\Scripts\activate.bat

python -m pip install --upgrade pip
pip install customtkinter requests pillow mutagen pyinstaller || (echo pip install failed & pause & exit /b 1)

REM --- Build ---
if exist "%APPNAME%" rmdir /s /q "%APPNAME%"
pyinstaller --noconfirm --clean --onedir --noconsole ^
    --name "%APPNAME%" ^
    --collect-all customtkinter ^
    --distpath "." --workpath "build" --specpath "build" ^
    app.py
if errorlevel 1 (echo PyInstaller failed & pause & exit /b 1)

REM --- Cleanup ---
call venv\Scripts\deactivate.bat
if exist build rmdir /s /q build
if exist "%APPNAME%.spec" del /q "%APPNAME%.spec"
if exist __pycache__ rmdir /s /q __pycache__
if exist venv rmdir /s /q venv

echo.
echo ============================================
echo  Done!  Run: "%APPNAME%\%APPNAME%.exe"
echo ============================================
pause
endlocal

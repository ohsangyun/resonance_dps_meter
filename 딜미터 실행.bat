@echo off
rem Resonance DPS meter launcher (ASCII only: this file must not depend on the console code page)
cd /d "%~dp0"
if not exist "logs" mkdir "logs"
if exist "python\pythonw.exe" (
  start "" "python\pythonw.exe" "dps-meter\dps_meter.py" --log-dir "%~dp0logs"
) else (
  start "" pythonw "dps-meter\dps_meter.py" --log-dir "%~dp0logs"
)

@echo off
rem 以管理员身份运行桌宠：游戏（暗区突围等）以管理员运行时，普通权限进程读不到键盘。
rem UAC 弹窗里点「是」即可；不需要提权就还用 run.bat。
powershell -NoProfile -ExecutionPolicy Bypass -Command "Start-Process -FilePath python.exe -ArgumentList Dafeiyu.py -WorkingDirectory '%~dp0' -Verb RunAs"
if errorlevel 1 pause

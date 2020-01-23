@echo off
set /a error=0
call dir /b /s | findstr /e .nut > ~nuts.tmp
call dir /b /s | findstr expected_compiler_error\ >> ~nuts.tmp
..\build\bin\Release\quirrel_static_analyzer.exe --files:~nuts.tmp --output:analysis_log.txt
if %errorlevel% neq 0 (
  echo FAILED
  set error=1
) else (
  echo OK
)
del ~nuts.tmp
exit /b %error%

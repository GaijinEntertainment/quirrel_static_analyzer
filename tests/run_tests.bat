@echo off
set /a error=0
call dir /b /s | findstr /e .nut > ~nuts.tmp
call dir /b /s | findstr /e .nut.txt >> ~nuts.tmp
call dir /b /s | findstr expected_compiler_error\ >> ~nuts.tmp
..\build\bin\Release\quirrel_static_analyzer.exe --files:~nuts.tmp --output:analysis_log.txt
if %errorlevel% neq 0 set "error=BASE TEST" && goto :fail

rem call dir /b /s | findstr /e .nut.2pass > ~nuts.tmp
rem ..\build\bin\Release\quirrel_static_analyzer.exe --files:~nuts.tmp --predefinition-files:~nuts.tmp --output:analysis_log.txt
rem if %errorlevel% neq 0 set "error=2 PASS CSQ" && goto :fail

call dir /b /s | findstr /e .nut.2pass > ~nuts.tmp
..\build\bin\Release\quirrel_static_analyzer.exe "--csq-exe:sq -m" --files:~nuts.tmp --predefinition-files:~nuts.tmp --output:analysis_log.txt
if %errorlevel% neq 0 set "error=2 PASS SQ" && goto :fail

:fail
if "%error%" neq "0" (
  echo FAILED: %error%
) else (
  echo OK
)
del ~nuts.tmp
exit /b %error%

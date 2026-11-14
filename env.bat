@echo off
if "%~1"=="book" goto book
set "ELAN_HOME=%~dp0.elan"
set "MATHLIB_CACHE_DIR=%~dp0.cache\mathlib"
echo ;%PATH%; | find /i ";%~dp0.elan\bin;" >nul || set "PATH=%~dp0.elan\bin;%PATH%"
doskey book="%~f0" book $*
exit /b 0

:book
pushd "%~dp0"
lake exe manifest && typst compile --root . book/main.typ .lake/build/meat.pdf %2 %3 %4 %5 %6 %7 %8 %9
set "rc=%errorlevel%"
popd
exit /b %rc%

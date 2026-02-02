@echo off
echo ╔════════════════════════════════════════════════════════════╗
echo ║         PRISM VSCode Theme Extension Builder               ║
echo ╚════════════════════════════════════════════════════════════╝
echo.

REM Check for icon
if not exist "media\icon.png" (
    echo WARNING: media\icon.png is missing!
    echo Open prism-icon-generator.html to create one.
    echo.
)

REM Check for vsce
where vsce >nul 2>&1
if %ERRORLEVEL% neq 0 (
    echo Installing vsce...
    npm install -g @vscode/vsce
)

echo Packaging extension...
call vsce package

echo.
echo Done! Look for the .vsix file in this folder.
echo.
echo To install locally: code --install-extension prism-themes-1.0.0.vsix
echo To publish: vsce login fleek-ai ^&^& vsce publish
pause

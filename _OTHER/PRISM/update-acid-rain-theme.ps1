# Update Acid Rain theme in installed extension
# Run this script AFTER closing Cursor/VS Code

$source = "c:\Users\justi\desktop\prism\vscode-prism\vscode-prism-theme-generator\themes\prism-acid_rain.json"
$targets = @(
    "$env:USERPROFILE\.vscode\extensions\fleek-ai.prism-theme-generator-*\themes\prism-acid_rain.json",
    "$env:USERPROFILE\.cursor\extensions\fleek-ai.prism-theme-generator-*\themes\prism-acid_rain.json"
)

Write-Host "Updating Acid Rain theme..." -ForegroundColor Cyan

foreach ($pattern in $targets) {
    $files = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
    foreach ($file in $files) {
        try {
            Copy-Item -Path $source -Destination $file.FullName -Force
            Write-Host "✅ Updated: $($file.FullName)" -ForegroundColor Green
        } catch {
            Write-Host "❌ Failed to update $($file.FullName): $_" -ForegroundColor Red
        }
    }
}

Write-Host "`nDone! Now reopen Cursor and reload the window (Ctrl+Shift+P → 'Developer: Reload Window')" -ForegroundColor Yellow

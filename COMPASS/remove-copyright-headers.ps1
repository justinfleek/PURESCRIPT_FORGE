# Remove copyright headers from all PureScript files
Get-ChildItem -Recurse -Filter *.purs | ForEach-Object {
    $file = $_.FullName
    $content = Get-Content $file -Raw
    
    # Pattern to match copyright and license lines in module header
    # Matches: Copyright   : (c) Anomaly 2025
    #         License     : AGPL-3.0
    # with optional blank line after
    $pattern = '(?m)^Copyright\s+:\s+\(c\)\s+Anomaly\s+\d+\r?\n(?:License\s+:\s+[^\r\n]+\r?\n)?'
    
    $newContent = $content -replace $pattern, ''
    
    if ($content -ne $newContent) {
        Set-Content -Path $file -Value $newContent -NoNewline
        Write-Host "Removed copyright from: $file"
    }
}

Write-Host "Done removing copyright headers"

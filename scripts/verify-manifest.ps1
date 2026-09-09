[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'

$repositoryRoot = [System.IO.Path]::GetFullPath(
    (Join-Path -Path $PSScriptRoot -ChildPath '..'))
$manifestPath = Join-Path -Path $repositoryRoot -ChildPath 'MANIFEST.sha256'
$rootPrefix = $repositoryRoot.TrimEnd(
    [System.IO.Path]::DirectorySeparatorChar,
    [System.IO.Path]::AltDirectorySeparatorChar) +
    [System.IO.Path]::DirectorySeparatorChar

$failures = [System.Collections.Generic.List[string]]::new()

foreach ($line in Get-Content -LiteralPath $manifestPath) {
    if ([string]::IsNullOrWhiteSpace($line)) {
        continue
    }

    if ($line -notmatch '^([0-9a-f]{64})  (.+)$') {
        $failures.Add("Malformed manifest line: $line")
        continue
    }

    $expectedHash = $Matches[1]
    $relativePath = $Matches[2]
    $targetPath = [System.IO.Path]::GetFullPath(
        (Join-Path -Path $repositoryRoot -ChildPath $relativePath))

    if (-not $targetPath.StartsWith(
            $rootPrefix,
            [System.StringComparison]::OrdinalIgnoreCase)) {
        $failures.Add("Path escapes repository root: $relativePath")
        continue
    }

    if (-not (Test-Path -LiteralPath $targetPath -PathType Leaf)) {
        $failures.Add("Missing file: $relativePath")
        continue
    }

    $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $targetPath).Hash.ToLowerInvariant()

    if ($actualHash -ne $expectedHash) {
        $failures.Add("Hash mismatch: $relativePath")
        continue
    }

    Write-Host "${relativePath}: OK"
}

if ($failures.Count -gt 0) {
    foreach ($failure in $failures) {
        [System.Console]::Error.WriteLine($failure)
    }
    exit 1
}

Write-Host 'Manifest verification succeeded.'

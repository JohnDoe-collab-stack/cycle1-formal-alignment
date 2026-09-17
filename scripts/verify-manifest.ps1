[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'

$repositoryRoot = [System.IO.Path]::GetFullPath(
    (Join-Path -Path $PSScriptRoot -ChildPath '..'))
$manifestPath = Join-Path -Path $repositoryRoot -ChildPath 'MANIFEST.sha256'
$lakefilePath = Join-Path -Path $repositoryRoot -ChildPath 'lakefile.toml'
$rootPrefix = $repositoryRoot.TrimEnd(
    [System.IO.Path]::DirectorySeparatorChar,
    [System.IO.Path]::AltDirectorySeparatorChar) +
    [System.IO.Path]::DirectorySeparatorChar

$failures = [System.Collections.Generic.List[string]]::new()
$manifestPaths = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal)

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
    [void]$manifestPaths.Add($relativePath)
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

foreach ($line in Get-Content -LiteralPath $lakefilePath) {
    if ($line -notmatch '^\s*"([^"]+)",?\s*$') {
        continue
    }

    $root = $Matches[1]
    $relativePath = $root.Replace('.', '/') + '.lean'
    if ($manifestPaths.Contains($relativePath)) {
        continue
    }

    $targetPath = Join-Path -Path $repositoryRoot -ChildPath $relativePath
    if (Test-Path -LiteralPath $targetPath -PathType Leaf) {
        $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $targetPath).Hash.ToLowerInvariant()
        $failures.Add("Missing manifest entry: ${actualHash}  ${relativePath}")
    }
    else {
        $failures.Add("Lake root has no source file: $relativePath")
    }
}

if ($failures.Count -gt 0) {
    foreach ($failure in $failures) {
        [System.Console]::Error.WriteLine($failure)
    }
    exit 1
}

Write-Host 'Manifest verification succeeded.'

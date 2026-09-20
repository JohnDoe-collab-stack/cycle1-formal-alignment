[CmdletBinding()]
param()

# Non-confirmatory, deterministic smoke protocol. This script writes no files.
$ErrorActionPreference = 'Stop'
$repositoryRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
Push-Location -LiteralPath $repositoryRoot
try {
    $leanPaths = @(& git ls-files --cached --others --exclude-standard -- '*.lean')
    if ($LASTEXITCODE -ne 0) { throw 'Unable to enumerate Lean sources.' }
    [string[]]$sourcePaths = $leanPaths + @('lakefile.toml', 'lean-toolchain', 'lake-manifest.json')
    [Array]::Sort($sourcePaths, [StringComparer]::Ordinal)
    $sourceLines = foreach ($path in $sourcePaths) {
        $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant()
        "${hash}  ${path}"
    }
    $sourceBytes = [Text.Encoding]::UTF8.GetBytes(($sourceLines -join "`n") + "`n")
    $digest = [Security.Cryptography.SHA256]::Create()
    try {
        $sourceDigest = [BitConverter]::ToString($digest.ComputeHash($sourceBytes)).Replace('-', '').ToLowerInvariant()
    } finally { $digest.Dispose() }
    $scriptHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $PSCommandPath).Hash.ToLowerInvariant()
    $smokeHash = (Get-FileHash -Algorithm SHA256 -LiteralPath 'ConstitutiveSearch/NPAndOrP/Smoke.lean').Hash.ToLowerInvariant()
    Write-Output 'classification=non-confirmatory smoke; no scientific conclusion'
    Write-Output "script_sha256=$scriptHash"
    Write-Output "sources_sha256=$sourceDigest"
    Write-Output "smoke_sha256=$smokeHash"
    Write-Output 'inputs=[0,1,2,4]; seed=none; external_data=none'
    Write-Output 'command=lake env lean ConstitutiveSearch/NPAndOrP/Smoke.lean'
    Write-Output 'columns=input,decision,generatedSteps,attempts,measuredComparisonWork,positiveBit,negativeBit'
    & lake env lean ConstitutiveSearch/NPAndOrP/Smoke.lean
    if ($LASTEXITCODE -ne 0) { throw "Smoke failed with code $LASTEXITCODE" }
} finally { Pop-Location }

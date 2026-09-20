[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'

$repositoryRoot = [System.IO.Path]::GetFullPath(
    (Join-Path -Path $PSScriptRoot -ChildPath '..'))
Set-Location -LiteralPath $repositoryRoot

$failures = [System.Collections.Generic.List[string]]::new()
$leanFiles = @(& git ls-files --cached --others --exclude-standard -- '*.lean')
if ($LASTEXITCODE -ne 0) {
    throw 'Unable to enumerate tracked Lean files.'
}

$forbiddenPattern = '\b(noncomputable|sorry|Classical|propext|native_decide|unsafe)\b|\bQuot\.sound\b|implemented_by|(?m)^\s*axiom\b'

foreach ($file in $leanFiles) {
    $text = [System.IO.File]::ReadAllText(
        (Join-Path -Path $repositoryRoot -ChildPath $file))
    $beginCount = ([regex]::Matches(
        $text,
        [regex]::Escape('/- AXIOM_AUDIT_BEGIN -/'))).Count
    $endCount = ([regex]::Matches(
        $text,
        [regex]::Escape('/- AXIOM_AUDIT_END -/'))).Count

    if ($beginCount -ne 1 -or $endCount -ne 1) {
        $failures.Add(
            "Invalid axiom-audit block count: $file (begin=$beginCount, end=$endCount)")
    }

    foreach ($match in [regex]::Matches($text, $forbiddenPattern)) {
        $line = 1 + ($text.Substring(0, $match.Index) -split "`n").Count - 1
        $failures.Add("Forbidden Lean construct: ${file}:$line ($($match.Value))")
    }
}

if ($failures.Count -gt 0) {
    foreach ($failure in $failures) {
        [System.Console]::Error.WriteLine($failure)
    }
    exit 1
}

$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($null -ne $lakeCommand) {
    $lakeExecutable = $lakeCommand.Source
} else {
    $lakeExecutable = Join-Path -Path $env:USERPROFILE -ChildPath '.elan\bin\lake.exe'
}

$mainLines = @(& $lakeExecutable build 2>&1)
$mainStatus = $LASTEXITCODE
$mainLines | ForEach-Object { Write-Host $_ }

if ($mainStatus -ne 0) {
    exit $mainStatus
}

$auditLines = @(& $lakeExecutable build AuditRegression 2>&1)
$auditStatus = $LASTEXITCODE
$auditLines | ForEach-Object { Write-Host $_ }

if ($auditStatus -ne 0) {
    exit $auditStatus
}

$auditText = @($mainLines + $auditLines) -join [Environment]::NewLine
if ($auditText -match 'depends on axioms:|sorryAx') {
    [System.Console]::Error.WriteLine(
        'Axiom dependency detected in audited declarations.')
    exit 1
}

Write-Host 'All Lean audit blocks are present and axiom-free.'

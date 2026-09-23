param([string]$LeanBin)
$ErrorActionPreference = 'Stop'
$arguments = @()
if ($LeanBin) { $arguments += @('--lake', (Join-Path $LeanBin 'lake.exe')) }
& python (Join-Path $PSScriptRoot 'verify.py') @arguments
exit $LASTEXITCODE

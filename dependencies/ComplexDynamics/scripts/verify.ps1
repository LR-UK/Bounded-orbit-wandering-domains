param([string]$LeanBin = '')
$ErrorActionPreference = 'Stop'
$proofProject = Split-Path -Parent $PSScriptRoot
$proofModule = 'ComplexDynamics'
$proofOldLocation = Get-Location
$proofOldPath = $env:PATH
try {
  Set-Location -LiteralPath $proofProject
  if ($LeanBin) {
    $proofLake = Join-Path $LeanBin 'lake.exe'
    if (-not (Test-Path -LiteralPath $proofLake)) { throw 'LeanBin must contain lake.exe.' }
    $env:PATH = $LeanBin + [IO.Path]::PathSeparator + $env:PATH
  } else { $proofLake = (Get-Command lake -ErrorAction Stop).Source }
  New-Item -ItemType Directory -Force -Path verification | Out-Null
  & $proofLake build $proofModule 2>&1 | Tee-Object -FilePath verification/build.log
  if ($LASTEXITCODE -ne 0) { throw 'The proof library failed to build.' }
  $proofAudit = & $proofLake env lean scripts/Audit.lean 2>&1
  $proofExit = $LASTEXITCODE
  $proofAudit | Tee-Object -FilePath verification/axioms.log
  if ($proofExit -ne 0) { throw 'The axiom audit failed to run.' }
  $proofText = $proofAudit -join "`n"
  $proofReports = [regex]::Matches($proofText, 'depends on axioms:\s*\[([^\]]*)\]')
  $proofExpected = (Select-String -LiteralPath scripts/Audit.lean -Pattern '^#print axioms ').Count
  if ($proofReports.Count -ne $proofExpected) { throw 'Missing axiom reports.' }
  foreach ($proofReport in $proofReports) {
    foreach ($proofAxiom in ($proofReport.Groups[1].Value -split ',')) {
      if ($proofAxiom.Trim() -notin @('propext', 'Classical.choice', 'Quot.sound')) {
        throw ('Unexpected axiom: ' + $proofAxiom.Trim())
      }
    }
  }
  $proofSources = @(Get-ChildItem -LiteralPath $proofModule -Filter '*.lean' -Recurse) +
    @(Get-Item -LiteralPath ($proofModule + '.lean'))
  $proofForbidden = $proofSources | Select-String -Pattern '\b(sorry|admit|axiom|native_decide)\b'
  if ($proofForbidden) { throw ('Forbidden proof construct: ' + ($proofForbidden -join '; ')) }
  Write-Output ($proofModule + ': library, source integrity, and ' + $proofReports.Count + ' axiom audits passed.')
} finally {
  $env:PATH = $proofOldPath
  Set-Location -LiteralPath $proofOldLocation
}

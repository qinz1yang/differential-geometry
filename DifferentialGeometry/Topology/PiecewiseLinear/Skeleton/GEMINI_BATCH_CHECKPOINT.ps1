param(
    [Parameter(Mandatory = $true)][string]$Label,
    [Parameter(Mandatory = $true)][string[]]$Modules
)

$ErrorActionPreference = 'Stop'
$batchCheckout = 'D:\differential-geometry-moise-int'
$batchOutput = 'C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d'
$batchShared = 'C:\Users\liao9\AppData\Local\Temp\claude-moise-shared'
$batchToken = 'claude-agent-d-20260919'
$batchChecker = Join-Path $batchShared 'checker.ps1'
$batchPreparer = Join-Path $batchShared 'prepare-private-root.py'

if ($Label -notmatch '^[A-Za-z0-9][A-Za-z0-9_-]{0,70}$') {
    throw 'Use a short alphanumeric checkpoint label, with hyphens or underscores.'
}
if ($Modules.Count -eq 0 -or @($Modules | Select-Object -Unique).Count -ne $Modules.Count) {
    throw 'Supply a nonempty dependency-ordered list of distinct modules.'
}
foreach ($batchModule in $Modules) {
    if ($batchModule -notmatch '^DifferentialGeometry\.Topology\.[A-Za-z0-9_]+(\.[A-Za-z0-9_]+)*$' -or
        $batchModule -match '(^|\.)Skeleton(\.|$)') {
        throw "Not an authorized real Topology module: $batchModule"
    }
}

$batchStamp = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffffffZ')
$batchDirectory = Join-Path $batchOutput ("gemini-batch\checkpoints\$Label-$batchStamp")
if (Test-Path -LiteralPath $batchDirectory) { throw 'Checkpoint directory already exists.' }
New-Item -ItemType Directory -Path $batchDirectory | Out-Null
$batchModuleReceipts = @()
$batchModuleArchives = @()
$batchArchiveIndex = 0
$batchAuditPath = Join-Path $batchDirectory 'AuditGeminiBatch.lean'

function Read-BatchReceipt {
    param([string]$ReceiptPath, [string]$ExpectedSource)
    $batchReceipt = Get-Content -Raw -LiteralPath $ReceiptPath | ConvertFrom-Json
    $batchSourceHash = (Get-FileHash -LiteralPath $ExpectedSource -Algorithm SHA256).Hash
    if ($batchReceipt.source -ne $ExpectedSource -or
        $batchReceipt.sourceSha256 -ne $batchSourceHash -or
        $batchReceipt.exitCode -ne 0 -or $batchReceipt.diagnosticLines -ne 0 -or
        $batchReceipt.sourceStable -ne $true -or
        $batchReceipt.sharedArtifactsModified -ne $false) {
        throw "Receipt does not certify the current zero-diagnostic source: $ExpectedSource"
    }
    return $batchReceipt
}

try {
    foreach ($batchModule in $Modules) {
        $batchArchiveIndex++
        $batchArchiveStem = 'module-{0:D3}' -f $batchArchiveIndex
        $batchRelative = $batchModule.Replace('.', '\')
        $batchSource = Join-Path $batchCheckout ($batchRelative + '.lean')
        if (-not (Test-Path -LiteralPath $batchSource -PathType Leaf)) {
            throw "Missing source: $batchSource"
        }
        & python $batchPreparer $batchOutput $batchModule
        if ($LASTEXITCODE -ne 0) { throw "Private preparation failed: $batchModule" }
        & powershell -NoProfile -ExecutionPolicy Bypass -File $batchChecker `
            -Checkout $batchCheckout -Token $batchToken -OutputRoot $batchOutput `
            -Module $batchModule
        $batchExitCode = $LASTEXITCODE
        $batchReceiptBase = Join-Path $batchOutput $batchRelative
        foreach ($batchExtension in @('.json', '.log')) {
            if (Test-Path -LiteralPath ($batchReceiptBase + $batchExtension)) {
                Copy-Item -LiteralPath ($batchReceiptBase + $batchExtension) `
                    -Destination (Join-Path $batchDirectory ($batchArchiveStem + $batchExtension))
            }
        }
        if ($batchExitCode -ne 0) { throw "Module check failed: $batchModule" }
        $batchReceipt = Read-BatchReceipt ($batchReceiptBase + '.json') $batchSource
        Copy-Item -LiteralPath $batchSource `
            -Destination (Join-Path $batchDirectory ($batchArchiveStem + '.source.txt'))
        $batchSnapshot = Join-Path $batchDirectory ($batchArchiveStem + '.source.txt')
        if ((Get-FileHash -LiteralPath $batchSnapshot).Hash -ne $batchReceipt.sourceSha256) {
            throw "Source changed while archiving the checkpoint: $batchModule"
        }
        $batchModuleReceipts += $batchReceipt
        $batchModuleArchives += [ordered]@{
            module = $batchModule
            receiptFile = $batchArchiveStem + '.json'
            logFile = $batchArchiveStem + '.log'
            sourceFile = $batchArchiveStem + '.source.txt'
        }
    }

    $batchImports = ($Modules | ForEach-Object { 'import ' + $_ }) -join "`n"
    $batchConstants = ($Modules | ForEach-Object { '    `' + $_ }) -join ",`n"
    $batchAuditTemplate = @'
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

open Lean

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let modules : Array Name := #[
__MODULES__]
  let declarations := env.constants.map₁.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if modules.contains env.header.moduleNames[idx]! && !env.isAutoDecl name then
        names.push name else names
    | none => names
  for target in modules do
    let found := declarations.any fun name =>
      match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]! == target
      | none => false
    unless found do
      logError m!"no audited declarations from {target}"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter fun a => !allowed.contains a
    unless bad.isEmpty do
      logError m!"non-foundational axioms {bad.toList} in {name}"
  let linters := (← Batteries.Tactic.Lint.getChecks true none none).filter fun l =>
    l.name != `docBlame && l.name != `docBlameThm
  unless linters.size == 13 do
    logError "expected thirteen linters"
  for linter in linters do
    for name in declarations do
      if let some msg ← linter.test name then
        logError m!"{linter.name}: {name}: {msg}"
'@
    $batchAuditText = $batchImports + "`n" + $batchAuditTemplate.Replace('__MODULES__', $batchConstants)
    [IO.File]::WriteAllText($batchAuditPath, $batchAuditText, [Text.UTF8Encoding]::new($false))
    Copy-Item -LiteralPath $batchAuditPath `
        -Destination (Join-Path $batchDirectory 'audit-spec.txt')
    & powershell -NoProfile -ExecutionPolicy Bypass -File $batchChecker `
        -Checkout $batchCheckout -Token $batchToken -OutputRoot $batchOutput `
        -Audit $batchAuditPath
    $batchExitCode = $LASTEXITCODE
    foreach ($batchExtension in @('.json', '.log')) {
        $batchAuditReceiptPath = Join-Path $batchOutput ('external-audit' + $batchExtension)
        if (Test-Path -LiteralPath $batchAuditReceiptPath) {
            Copy-Item -LiteralPath $batchAuditReceiptPath `
                -Destination (Join-Path $batchDirectory ('audit' + $batchExtension))
        }
    }
    if ($batchExitCode -ne 0) { throw 'Batch axiom/linter audit failed.' }
    $batchAuditReceipt = Read-BatchReceipt (Join-Path $batchOutput 'external-audit.json') $batchAuditPath
    foreach ($batchReceipt in $batchModuleReceipts) {
        if ((Get-FileHash -LiteralPath $batchReceipt.source).Hash -ne $batchReceipt.sourceSha256) {
            throw "A source changed during the checkpoint: $($batchReceipt.source)"
        }
    }
    $batchSummary = [ordered]@{
        status = 'WORKER_PASS_PENDING_LEAD'
        label = $Label
        endedAtUtc = [DateTime]::UtcNow.ToString('o')
        checkout = $batchCheckout
        modules = $Modules
        moduleReceipts = $batchModuleReceipts
        moduleArchives = $batchModuleArchives
        auditReceipt = $batchAuditReceipt
        leadAccepted = $false
        fullAggregateBuilt = $false
    }
    $batchSummary | ConvertTo-Json -Depth 8 | Set-Content `
        -LiteralPath (Join-Path $batchDirectory 'checkpoint.json') -Encoding utf8
    Write-Output "Worker checkpoint passed; lead acceptance pending: $batchDirectory"
} catch {
    [ordered]@{
        status = 'FAILED_SELF_CHECK'
        endedAtUtc = [DateTime]::UtcNow.ToString('o')
        message = $_.Exception.Message
        modules = $Modules
        leadAccepted = $false
    } | ConvertTo-Json -Depth 4 | Set-Content `
        -LiteralPath (Join-Path $batchDirectory 'failed.json') -Encoding utf8
    throw
} finally {
    if (Test-Path -LiteralPath $batchAuditPath) {
        Remove-Item -LiteralPath $batchAuditPath
    }
}

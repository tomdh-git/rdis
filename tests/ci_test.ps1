#===============================================================================
# ci_test.ps1 - CI Integration Test Suite for rdis
#===============================================================================
[CmdletBinding()]
param(
    [string]$RdisExe = ""
)

$ErrorActionPreference = "Continue"

if (-not $RdisExe) {
    if ($PSScriptRoot -and (Test-Path "$PSScriptRoot/../target/release/rdis.exe")) {
        $RdisExe = "$PSScriptRoot/../target/release/rdis.exe"
    } elseif (Test-Path "target/release/rdis.exe") {
        $RdisExe = "target/release/rdis.exe"
    } else {
        $RdisExe = "rdis.exe"
    }
}

if (-not (Test-Path $RdisExe)) {
    Write-Error "rdis binary not found at $RdisExe"
    exit 1
}

$RdisExe = (Resolve-Path $RdisExe).Path
Write-Host "== Testing rdis binary: $RdisExe ==" -ForegroundColor Cyan

$passed = 0
$failed = 0

function Assert-Test([string]$name, [scriptblock]$check) {
    try {
        $result = & $check
        if ($result -eq $true) {
            Write-Host "  [PASS] $name" -ForegroundColor Green
            $script:passed++
        } else {
            Write-Host "  [FAIL] $name (assertion returned false)" -ForegroundColor Red
            $script:failed++
        }
    } catch {
        Write-Host "  [FAIL] $name (exception: $_)" -ForegroundColor Red
        $script:failed++
    }
}

$testTarget = $RdisExe

# 1. Help command
Assert-Test "Command 'help' outputs documentation" {
    $out = (& $RdisExe $testTarget help) -join "`n"
    ($out -match "commands" -and $out -match "walk" -and $out -match "dis")
}

# 2. PE Information JSON
Assert-Test "Command 'info' returns valid PE metadata" {
    $out = (& $RdisExe $testTarget info) -join "`n"
    $line = ($out -split "`n" | Where-Object { $_.Trim().StartsWith('{') } | Select-Object -First 1)
    $info = $line | ConvertFrom-Json
    ($info -ne $null -and $info.image_base -gt 0 -and $info.functions_pdata -gt 0)
}

# 3. Section listing
Assert-Test "Command 'sec' lists PE sections" {
    $out = (& $RdisExe $testTarget sec) -join "`n"
    ($out -match "\.text" -and $out -match "\.pdata")
}

# 4. Linear disassembly
Assert-Test "Command 'dis' disassembles code" {
    $out = (& $RdisExe $testTarget dis 0x1000 5) -join "`n"
    ($out.Length -gt 20)
}

# 5. Function analysis
Assert-Test "Command 'fn' analyzes function" {
    $fnOut = (& $RdisExe $testTarget fn 0x1000) -join "`n"
    ($fnOut.Length -gt 20)
}

# 6. SQLite overlay persistence (assert -> facts -> retract)
Assert-Test "Overlay persistence (assert, facts, retract)" {
    $testSubj = "0x1000"
    $testVal = "ci_verifier_mark"
    
    # Assert
    $assertOut = (& $RdisExe $testTarget assert name $testSubj $testVal) -join "`n"
    $assertObj = ($assertOut -split "`n" | Where-Object { $_.Trim().StartsWith('{') } | Select-Object -First 1) | ConvertFrom-Json
    if (-not $assertObj -or $assertObj.asserted -eq $null) { return $false }
    $factId = [int64]$assertObj.asserted

    # Facts query
    $factsOut = (& $RdisExe $testTarget facts) -join "`n"
    $factsObj = ($factsOut -split "`n" | Where-Object { $_.Trim().StartsWith('{') } | Select-Object -First 1) | ConvertFrom-Json
    $items = @($factsObj.facts.items)
    $matching = $items | Where-Object { [int64]$_.id -eq $factId }
    if (-not $matching -or $matching.Count -eq 0) { return $false }

    # Retract
    $retractOut = (& $RdisExe $testTarget retract "$factId") -join "`n"
    $retractObj = ($retractOut -split "`n" | Where-Object { $_.Trim().StartsWith('{') } | Select-Object -First 1) | ConvertFrom-Json
    
    ($retractObj -ne $null -and $retractObj.retracted -eq $factId)
}

Write-Host "`n== CI Test Summary: $passed passed, $failed failed ==" -ForegroundColor $(if ($failed -eq 0) { "Green" } else { "Red" })

if ($failed -gt 0) {
    exit 1
}
exit 0

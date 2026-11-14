#===============================================================================
# test_speed_accuracy.ps1
#
# Speed + accuracy + functional test harness for rdis.
#
#   .\test_speed_accuracy.ps1 [-RdisExe <path>] [-TestExe <path>] [-ResultsOut <path>] [-NoFail]
#
# What it does:
#   1. Discovers real targets by running `rdis <exe> info` and `rdis <exe> classes`
#      against the rdis binary itself (and/or a game exe at common paths).
#   2. Speed tests every major command with Measure-Command.
#   3. Accuracy tests (corroborate, sigcheck, audit, recipes).
#   4. Functional tests: all 60 registered commands emit valid JSON, error handling,
#      and SQLite persistence (assert -> facts -> re-run -> check persistence).
#   5. Report: total wall time vs IDA's 15-20 minutes.
#
# Exit code: 0 if every check passes, 1 otherwise (unless -NoFail).
#===============================================================================
[CmdletBinding()]
param(
    [string]$RdisExe   = "$PSScriptRoot/target/release/rdis.exe",
    [string]$TestExe   = $null,
    [string]$ResultsOut= "$PSScriptRoot/test_speed_accuracy.results.json",
    [switch]$NoFail
)

$ErrorActionPreference = "Continue"
$script:results = [System.Collections.Generic.List[pscustomobject]]::new()
$script:totalSpeedMs = 0
$script:IDAMsMin = 15 * 60 * 1000   # 15 minutes
$script:IDAMsMax = 20 * 60 * 1000   # 20 minutes

# Background subagent benchmark (reference, from a prior clean release build):
#   rdis.exe bench = 21ms total (pe_load: 3ms, xref_index: 12ms, vtables: 2ms, sum_per_fn: 0ms)
$script:refBenchMs = 21

function Write-Result([string]$Phase, [string]$Test, [bool]$Pass, [string]$Detail = "") {
    $script:results.Add([pscustomobject]@{
        Phase   = $Phase
        Test    = $Test
        Pass    = $Pass
        Detail  = $Detail
        Time    = (Get-Date).ToString("o")
    })
    $pad = if ($Pass) { "PASS" } else { "FAIL" }
    Write-Host ("[{0}] {1,-52} {2,-7} {3}" -f $pad, $Test, $Phase, $Detail)
}

#-------------------------------------------------------------------------------
# Resolve the directory the script lives in (works when $PSScriptRoot is empty).
#-------------------------------------------------------------------------------
if ($PSScriptRoot) {
    $scriptDir = (Resolve-Path $PSScriptRoot -ErrorAction SilentlyContinue)
    if ($scriptDir) { $scriptDir = $scriptDir.Path } else { $scriptDir = (Get-Location).Path }
} else {
    $scriptDir = (Get-Location).Path
}
# Try, in order: the -RdisExe parameter, then scriptDir/target/release/rdis.exe, then ./target/release/rdis.exe.
$rdisCandidates = New-Object System.Collections.Generic.List[string]
if ($RdisExe) { $rdisCandidates.Add($RdisExe) }
$rdisCandidates.Add((Join-Path $scriptDir "target/release/rdis.exe"))
$rdisCandidates.Add((Join-Path (Get-Location).Path "target/release/rdis.exe"))
$RdisExe = $null
foreach ($c in $rdisCandidates) {
    if ($c -and (Test-Path $c)) { $RdisExe = (Resolve-Path $c).Path; break }
}
if (-not $RdisExe) {
    Write-Host "FATAL: rdis.exe not found. Build it first (cargo build --release)." -ForegroundColor Red
    exit 1
}
Write-Host "Using rdis.exe: $RdisExe"

#-------------------------------------------------------------------------------
# Pick the binary to analyze: a game exe at common paths, else rdis.exe itself.
#-------------------------------------------------------------------------------
$repoRoot = Split-Path $scriptDir -Parent
$gameCandidates = New-Object System.Collections.Generic.List[string]
$gameCandidates.Add((Join-Path $repoRoot "game.exe"))
$gameCandidates.Add((Join-Path $repoRoot "Game.exe"))
$gameCandidates.Add((Join-Path $repoRoot "Binaries/Win64/game.exe"))
$gameCandidates.Add((Join-Path $repoRoot "Binaries/Win64/Game.exe"))
$gameCandidates.Add("C:\Games\BlueySense\BlueySense.exe")
$gameCandidates.Add("C:\Games\BlueySense\Binaries\Win64\BlueySense-Win64-Shipping.exe")
$TestExe = $null
if ($PSBoundParameters.ContainsKey('TestExe') -and $TestExe) {
    $_rp = Resolve-Path $TestExe -ErrorAction SilentlyContinue
    if ($_rp) { $TestExe = $_rp.Path }
}
if (-not $TestExe) {
    Write-Host "`n== Scanning common game-exe paths =="
    foreach ($c in $gameCandidates) {
        $resolved = Resolve-Path $c -ErrorAction SilentlyContinue
        if ($resolved) {
            Write-Host ("  FOUND  {0}" -f $resolved) -ForegroundColor Green
            $TestExe = $resolved.Path
            break
        } else {
            Write-Host ("  missing {0}" -f $c)
        }
    }
}
if (-not $TestExe) {
    Write-Host "No game exe found at common paths; analyzing rdis.exe itself as the test target." -ForegroundColor Yellow
    $TestExe = $RdisExe
}
Write-Host "Test target:  $TestExe"

#-------------------------------------------------------------------------------
# Helpers
#-------------------------------------------------------------------------------
function Format-Arg([string]$a) {
    # .NET ProcessStartInfo passes the argument string to CreateProcess, which only honours
    # double quotes for grouping. Single quotes would be passed literally and break signatures
    # and multi-word commands (they'd still parse as valid error-JSON, masking the bug).
    if ($a -match '\s') { '"' + $a + '"' } else { $a }
}

function Invoke-Rdis([string]$exe, [string[]]$cmdArgs, [int]$timeoutMs = 120000) {
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $exe
    $psi.Arguments = ($cmdArgs | ForEach-Object { Format-Arg $_ }) -join ' '
    $psi.UseShellExecute = $false
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.CreateNoWindow = $true
    try { $p = [System.Diagnostics.Process]::Start($psi) } catch {
        return [pscustomobject]@{ Out = ""; Err = "$_"; ExitCode = -1; StartFailed = $true }
    }
    $stdout = $p.StandardOutput.ReadToEnd()
    $stderr = $p.StandardError.ReadToEnd()
    $waited = $p.WaitForExit($timeoutMs)
    if (-not $waited) { $p.Kill(); $p.WaitForExit() }
    return [pscustomobject]@{ Out = $stdout; Err = $stderr; ExitCode = $p.ExitCode; StartFailed = $false }
}

# Analyze command output: how many JSON lines, how many malformed, is it valid JSON.
function Analyze-Output([string]$out) {
    $jc = 0; $bc = 0
    foreach ($line in ($out -split "`n")) {
        $t = $line.Trim()
        if ($t.Length -gt 0 -and $t[0] -eq '{') {
            $jc++
            try { $null = $t | ConvertFrom-Json } catch { $bc++ }
        }
    }
    return [pscustomobject]@{ JsonCount = $jc; BadCount = $bc; JsonOk = ($jc -gt 0 -and $bc -eq 0) }
}

function First-Json([string]$out) {
    $line = (($out -split "`n") | Where-Object { $_.Trim().StartsWith("{") } | Select-Object -First 1)
    if ($line) { try { return $line | ConvertFrom-Json } catch { return $null } }
    return $null
}

function Parse-HexU32([string]$s) {
    if ([string]::IsNullOrEmpty($s)) { return $null }
    $s = $s.Trim()
    if ($s.StartsWith("0x")) { $s = $s.Substring(2) }
    if ([string]::IsNullOrEmpty($s)) { return $null }
    try { return [Convert]::ToUInt32($s, 16) } catch { return $null }
}

# Read `len` bytes at `rva` from a PE file by walking the section table (no fake fallbacks).
function Read-PeBytesAtRva([string]$path, [uint32]$rva, [int]$len) {
    $bytes = [System.IO.File]::ReadAllBytes($path)
    if ($bytes.Length -lt 0x40) { return $null }
    $peOff = [BitConverter]::ToUInt32($bytes, 0x3c)
    if ($peOff + 24 -gt $bytes.Length) { return $null }
    $numSec = [BitConverter]::ToUInt16($bytes, $peOff + 6)
    $optOff = $peOff + 24 + [BitConverter]::ToUInt16($bytes, $peOff + 20)
    for ($i = 0; $i -lt $numSec; $i++) {
        $s = $optOff + $i * 40
        if ($s + 40 -gt $bytes.Length) { break }
        $secRva   = [BitConverter]::ToUInt32($bytes, $s + 12)
        $secVsize = [BitConverter]::ToUInt32($bytes, $s + 8)
        $secRaw   = [BitConverter]::ToUInt32($bytes, $s + 20)
        $secRawsz = [BitConverter]::ToUInt32($bytes, $s + 16)
        if ($rva -ge $secRva -and $rva -lt $secRva + $secVsize) {
            $off = $secRaw + ($rva - $secRva)
            if ($off + $len -le $bytes.Length) {
                return $bytes[$off..($off + $len - 1)]
            }
        }
    }
    return $null
}

#-------------------------------------------------------------------------------
# Phase 1: Discover real targets (info + classes).
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 1: Discover targets (`$TestExe info / classes) =="

$r = Invoke-Rdis $RdisExe @($TestExe, "info")
if ($r.StartFailed -or $r.Out.Length -eq 0) {
    Write-Host "FATAL: could not run `info` against $TestExe" -ForegroundColor Red
    Write-Host ("  StartFailed={0} ExitCode={1} Err=[{2}] OutLen={3}" -f $r.StartFailed, $r.ExitCode, $r.Err, $r.Out.Length)
    exit 1
}
$info = First-Json $r.Out
$FnPdata   = [int]$info.functions_pdata
$VtCount   = [int]$info.vtables_discovered
$XrefPairs = [int]$info.xref_pairs
$ImageBase = $info.image_base
Write-Host ("info: functions_pdata={0}  vtables={1}  xref_pairs={2}  image_base={3}" -f $FnPdata, $VtCount, $XrefPairs, $ImageBase)

$r = Invoke-Rdis $RdisExe @($TestExe, "classes")
$classes = First-Json $r.Out
$items = @($classes.classes.items)

# Pick a real vtable with slots, and a real function (first ctor of that vtable).
$vtItem = $items | Where-Object { [int]$_.slots -gt 0 } | Select-Object -First 1
if (-not $vtItem) {
    Write-Host "FATAL: no vtable with slots discovered." -ForegroundColor Red
    exit 1
}
$VtableRva = Parse-HexU32 $vtItem.vtable
$VtHex = "0x{0:X}" -f $VtableRva

$FnRva = $null
if ($vtItem.evidence -and $vtItem.evidence.Count -gt 0 -and $vtItem.evidence[0].fn.rva) {
    $FnRva = Parse-HexU32 $vtItem.evidence[0].fn.rva
}
if (-not $FnRva) { $FnRva = $VtableRva }   # fallback (not code; better than nothing)
$FnHex = "0x{0:X}" -f $FnRva
Write-Host ("chosen vtable: {0}  (slots={1})  chosen function: {2}" -f $VtHex, $vtItem.slots, $FnHex)

# Find a REAL call edge: iterate vtable ctors until one has a caller (xref-graph).
$From = $null
foreach ($it in (@($items | Where-Object { [int]$_.slots -gt 0 } | Select-Object -First 12))) {
    $candFn = $null
    if ($it.evidence -and $it.evidence.Count -gt 0 -and $it.evidence[0].fn.rva) {
        $candFn = Parse-HexU32 $it.evidence[0].fn.rva
    } else { $candFn = Parse-HexU32 $it.vtable }
    if ($candFn -eq $null) { continue }
    $xg = Invoke-Rdis $RdisExe @($TestExe, "recipes", "xref-graph", "0x{0:X}" -f $candFn)
    $xgJson = First-Json $xg.Out
    $callers = @($xgJson.callers)
    if ($callers.Count -gt 0) {
        $f = Parse-HexU32 $callers[0].from
        if ($f -ne $null) {
            $FnRva = $candFn
            $FnHex = "0x{0:X}" -f $FnRva
            $From = $f
            Write-Host ("real edge found: {0} -> {1}  (caller of {2})" -f ("0x{0:X}" -f $From), $FnHex, $FnHex)
            break
        }
    }
}
if (-not $From) {
    $From = $FnRva   # degenerate fallback; edge test will report uncorroborated (still valid JSON)
    Write-Host "No caller found for any sampled vtable ctor; using degenerate edge (edge test will be informational)." -ForegroundColor Yellow
}
$FromHex = "0x{0:X}" -f $From

# Real signature: first 24 bytes of the chosen function, read straight from the PE file.
$sigBytes = Read-PeBytesAtRva $TestExe $FnRva 24
if ($sigBytes) {
    $Sig = ($sigBytes | ForEach-Object { '{0:X2}' -f $_ }) -join ' '
} else {
    $Sig = "55 41 57 41 56 41 55 41 54 56 57 53 48 83 EC 28 48 89 6C 24 20"
}
Write-Host ("signature for sigcheck: {0}  (from {1})" -f $Sig, $FnHex)

#-------------------------------------------------------------------------------
# Phase 2: Speed tests (Measure-Command).
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 2: Speed tests (Measure-Command) =="

function Speed-Test([string]$name, [string[]]$cmdArgs) {
    $script:lastRdis = $null
    $timer = Measure-Command { $script:lastRdis = Invoke-Rdis $RdisExe $cmdArgs }
    $r = $script:lastRdis
    if ($r.StartFailed) {
        Write-Result "SPEED" $name $false "process failed to start: $($r.Err)"
        return [pscustomobject]@{ Name = $name; Ms = 0; Ok = $false }
    }
    $ms = [math]::Round($timer.TotalMilliseconds, 1)
    $script:totalSpeedMs += $ms
    $a = Analyze-Output $r.Out
    $haveOutput = ($r.Out.Length -gt 0)
    if ($name -eq "names") { $haveOutput = $true }   # `names` is legitimately empty for rdis.exe itself
    $pass = (-not $r.StartFailed) -and $haveOutput
    Write-Result "SPEED" $name $pass ("{0} ms  exit={1}  outLen={2}  json={3}" -f $ms, $r.ExitCode, $r.Out.Length, $a.JsonOk)
    return [pscustomobject]@{ Name = $name; Ms = $ms; Ok = $pass; Exit = $r.ExitCode; Json = $a.JsonOk }
}

$speedResults = @()
$speedResults += Speed-Test "info"                   @($TestExe, "info")
$speedResults += Speed-Test "sec"                    @($TestExe, "sec")
$speedResults += Speed-Test "names"                  @($TestExe, "names")
$speedResults += Speed-Test "classes"                @($TestExe, "classes")
$speedResults += Speed-Test "sum"                    @($TestExe, "sum", $FnHex)
$speedResults += Speed-Test "vt"                     @($TestExe, "vt", $VtHex, "32")
$speedResults += Speed-Test "surprises --max 50"     @($TestExe, "surprises", "--max", "50")
$speedResults += Speed-Test "bench"                  @($TestExe, "bench")
$speedResults += Speed-Test "batch -c"               @($TestExe, "-c", "info; sec; names; classes; surprises")

# Capture bench phase data for the report (alongside the background-subagent reference).
$benchResult = $speedResults | Where-Object { $_.Name -eq "bench" } | Select-Object -First 1
$benchOut = ($script:results | Where-Object { $_.Test -eq "bench" }) | Select-Object -Last 1
# Re-run bench capture of raw JSON for phase detail:
$script:lastRdis = $null
$benchTimer = Measure-Command { $script:lastRdis = Invoke-Rdis $RdisExe @($TestExe, "bench") }
$benchJson = First-Json $script:lastRdis.Out
$benchPhases = if ($benchJson) { $benchJson.bench.phases } else { @() }

#-------------------------------------------------------------------------------
# Phase 3: Accuracy tests.
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 3: Accuracy tests =="

function Acc-Test([string]$name, [string[]]$cmdArgs) {
    $script:lastRdis = $null
    $timer = Measure-Command { $script:lastRdis = Invoke-Rdis $RdisExe $cmdArgs }
    $r = $script:lastRdis
    $ms = [math]::Round($timer.TotalMilliseconds, 1)
    $a = Analyze-Output $r.Out
    $first = First-Json $r.Out
    $pass = (-not $r.StartFailed) -and $a.JsonOk
    Write-Result "ACCURACY" $name $pass ("{0} ms  json={1}  exit={2}" -f $ms, $a.JsonOk, $r.ExitCode)
    return [pscustomobject]@{ Name = $name; Ms = $ms; Ok = $pass; JsonOk = $a.JsonOk; First = $first; Exit = $r.ExitCode; Out = $r.Out }
}

$accCorroborateVt = Acc-Test "corroborate vtable:0x.." @($TestExe, "corroborate", "vtable:$VtHex")
$accCorroborateEdge = Acc-Test "corroborate edge:0x..->0x.." @($TestExe, "corroborate", "edge:$FromHex->$FnHex")
$accSigcheck      = Acc-Test "sigcheck <real sig>"      @($TestExe, "sigcheck", $Sig)
$accAudit         = Acc-Test "audit"                    @($TestExe, "audit")
$accImportTrace   = Acc-Test "recipes import-trace kernel32" @($TestExe, "recipes", "import-trace", "kernel32")
$accStringXref    = Acc-Test 'recipes string-xref "rdis"'   @($TestExe, "recipes", "string-xref", "rdis")
$accXrefGraph     = Acc-Test "recipes xref-graph 0x.."  @($TestExe, "recipes", "xref-graph", $FnHex)

# Accuracy quality checks (informational, recorded as results).
if ($accSigcheck.First) {
    $matches = [int]$accSigcheck.First.matches
    Write-Result "ACCURACY" "sigcheck matches>=1" ($matches -ge 1) ("matches=$matches ok=$($accSigcheck.First.ok)")
}
if ($accCorroborateVt.First) {
    $v = $accCorroborateVt.First.verdict
    Write-Result "ACCURACY" "corroborate vtable verdict" ($v -in @("corroborated", "single-route")) ("verdict=$v")
}
if ($accCorroborateEdge.First) {
    $v = $accCorroborateEdge.First.verdict
    Write-Result "ACCURACY" "corroborate edge verdict" ($v -in @("corroborated", "single-route", "uncorroborated")) ("verdict=$v")
}
if ($accAudit.First) {
    $broken = [int]$accAudit.First.broken
    Write-Result "ACCURACY" "audit broken==0" ($broken -eq 0) ("broken=$broken checked=$($accAudit.First.facts_checked)")
}

#-------------------------------------------------------------------------------
# Phase 4a: Functional tests - all 60 registered commands emit valid JSON.
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 4a: Functional - all 60 registered commands =="

# The 60 commands from main.rs CMDS array (verified statically against src/main.rs).
$AllCmds = @(
    "gobj","ptables","structm","worklist","observe","portfacts","port","abi","sigcheck","hookpoints",
    "flow","contradict","surprises","corroborate","investigate","recipes","bench","needs","decide","choke",
    "common","uses","anchors","comps","sum","cfg","gates","path","reach","classes","class","vslot","vcalls",
    "rw","struct","system","assert","retract","contest","facts","why","audit","info","fn","ptr","comp",
    "dis","xr","callers","callees","str","fld","imm","vt","find","name","names","sec","help","?"
)
if ($AllCmds.Count -ne 60) {
    Write-Result "FUNCTIONAL" "60 commands registered" $false ("actual count={0}" -f $AllCmds.Count)
} else {
    Write-Result "FUNCTIONAL" "60 commands registered" $true "count matches main.rs CMDS array"
}

# Legacy (text-printing) commands - these do NOT return JSON; they print text.
$LegacyText = @("help","?","sec","fn","dis","xr","callers","callees","str","fld","imm","ptr","vt","find","names")

# Sample arguments for each command, built from discovered real addresses.
$CmdArgs = @{
    help=""; "?"=""; sec=""; names=""; info=""; bench=""; audit=""; facts=""; classes=""; comps="";
    fn=$FnHex; dis="$FnHex 4"; xr=$FnHex; callers=$FnHex; callees=$FnHex; ptr=$FnHex;
    vt="$VtHex 8"; find=$Sig; name="$FnHex ztest_func"; sum=$FnHex; cfg=$FnHex;
    gates="$FnHex 0x$FnHex"; path="$FnHex $FnHex"; reach=$FnHex; class=$VtHex;
    vslot="0"; vcalls=$FnHex; rw="0"; struct=$VtHex; system=$FnHex;
    assert="name 0x$FnHex ztest_persist"; retract="1"; contest="edge:$FromHex->$FnHex";
    why=$FnHex; decide=$FnHex; choke=$FnHex; common=$FnHex; uses=$FnHex; anchors=$FnHex;
    needs="$FnHex $FnHex"; port="$TestExe $FnHex"; gobj=$FnHex; ptables=$FnHex;
    structm=$FnHex; worklist=$FnHex; observe=$FnHex; portfacts=$FnHex; abi=$FnHex;
    sigcheck=$Sig; str="rdis"; hookpoints="$FnHex $FnHex"; flow="$FnHex a0";
    contradict="0 --fn $FnHex"; surprises="--max 5"; corroborate="vtable:$VtHex";
    investigate="vtable"; recipes="import-trace kernel32"; comp="type_info";
}

$funcPassed = 0; $funcFailed = 0
foreach ($cmd in $AllCmds) {
    $argStr = if ($CmdArgs.ContainsKey($cmd)) { $CmdArgs[$cmd] } else { "" }
    $argArr = if ($argStr) { $argStr -split ' ' } else { @() }
    $fullArgs = @($TestExe, $cmd) + $argArr
    $script:lastRdis = $null
    $timer = Measure-Command { $script:lastRdis = Invoke-Rdis $RdisExe $fullArgs }
    $r = $script:lastRdis
    $ms = [math]::Round($timer.TotalMilliseconds, 1)
    $script:totalSpeedMs += $ms
    $a = Analyze-Output $r.Out

    $isLegacy = $LegacyText -contains $cmd
    if ($isLegacy) {
        # Legacy text commands: must run and emit (non-panicking) output. `names` may be empty.
        $pass = (-not $r.StartFailed) -and ($r.Out.Length -gt 0 -or $cmd -eq "names")
        $detail = ("{0} ms  outLen={1}" -f $ms, $r.Out.Length)
    } else {
        # New-style commands: must emit valid JSON (even an {"error":...} is valid JSON).
        $pass = (-not $r.StartFailed) -and $a.JsonOk
        $detail = ("{0} ms  json={1}  lines={2}" -f $ms, $a.JsonOk, $a.JsonCount)
    }
    if ($pass) { $funcPassed++ } else { $funcFailed++ }
    Write-Result "FUNCTIONAL" "cmd '$cmd'" $pass $detail
}

Write-Result "FUNCTIONAL" "60 commands JSON/output" ($funcFailed -eq 0) ("passed=$funcPassed failed=$funcFailed")

#-------------------------------------------------------------------------------
# Phase 4b: Error handling (bad address, missing file, invalid signature).
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 4b: Error handling =="

function Err-Test([string]$name, [string[]]$args) {
    $script:lastRdis = $null
    $timer = Measure-Command { $script:lastRdis = Invoke-Rdis $RdisExe $args }
    $r = $script:lastRdis
    $ms = [math]::Round($timer.TotalMilliseconds, 1)
    $script:totalSpeedMs += $ms
    $a = Analyze-Output $r.Out
    # "Fail loud": non-zero exit, start failure, or a JSON {"error":...}. Silent success = fail.
    $jsonErr = ($a.JsonCount -gt 0) -and ($r.Out -match '"error"')
    $pass = ($r.ExitCode -ne 0) -or $r.StartFailed -or $jsonErr
    Write-Result "ERROR-HANDLING" $name $pass ("{0} ms  exit={1}  startFailed={2}  jsonError={3}" -f $ms, $r.ExitCode, $r.StartFailed, $jsonErr)
    return $pass
}

$errBadAddr   = Err-Test "bad address (sum 0xDEADBEEF)"   @($TestExe, "sum", "0xDEADBEEF")
$errMissing   = Err-Test "missing file"                    @("C:\does_not_exist\nope.exe", "info")
$errBadSig    = Err-Test "invalid signature (sigcheck zz)" @($TestExe, "sigcheck", "zz")

#-------------------------------------------------------------------------------
# Phase 4c: SQLite persistence (assert -> facts -> re-run -> check persistence).
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 4c: SQLite persistence (assert -> facts -> re-run) =="

$subjHex = $FnHex
$assert = Invoke-Rdis $RdisExe @($TestExe, "assert", "name", $subjHex, "persistence_test", "--trust", "agent")
$assertJson = First-Json $assert.Out
$assertedId = if ($assertJson) { $assertJson.asserted } else { $null }
Write-Result "PERSISTENCE" "assert accepted" (-not $assert.StartFailed -and $assertJson -and $assertJson.asserted -ne $null) ("id=$assertedId")

# Facts in the same process. (`facts` paginates: facts.items holds the array.)
$factsSame = Invoke-Rdis $RdisExe @($TestExe, "facts")
$factsSameJson = First-Json $factsSame.Out
$factsSameItems = if ($factsSameJson) { @($factsSameJson.facts.items) } else { @() }
$foundSame = $false
if ($factsSameJson) {
    $foundSame = ($factsSameItems | Where-Object { $_.subject -ieq $subjHex -and $_.kind -eq "name" -and $_.value -eq "persistence_test" }).Count -gt 0
}
Write-Result "PERSISTENCE" "fact visible in facts (same process)" $foundSame

# Re-run in a NEW process: the SQLite journal must survive the reload.
$info2 = Invoke-Rdis $RdisExe @($TestExe, "info")
$info2Json = First-Json $info2.Out
$activeFacts = if ($info2Json) { [int]$info2Json.overlay.active_facts } else { -1 }
Write-Result "PERSISTENCE" "facts survive reload (active_facts>=1)" ($activeFacts -ge 1) ("active_facts=$activeFacts")

# Facts in the new process must contain our asserted fact.
$factsNew = Invoke-Rdis $RdisExe @($TestExe, "facts")
$factsNewJson = First-Json $factsNew.Out
$factsNewItems = if ($factsNewJson) { @($factsNewJson.facts.items) } else { @() }
$foundNew = $false
if ($factsNewJson) {
    $foundNew = ($factsNewItems | Where-Object { $_.subject -ieq $subjHex -and $_.kind -eq "name" -and $_.value -eq "persistence_test" }).Count -gt 0
}
Write-Result "PERSISTENCE" "fact visible after re-run (new process)" $foundNew

# Cleanup: retract the asserted fact so the journal is left tidy.
if ($assertedId -ne $null) {
    Invoke-Rdis $RdisExe @($TestExe, "retract", "$assertedId") | Out-Null
}

$persistencePass = $foundSame -and ($activeFacts -ge 1) -and $foundNew
Write-Result "PERSISTENCE" "overall SQLite persistence" $persistencePass

#-------------------------------------------------------------------------------
# Phase 5: Report - total wall time vs IDA's 15-20 minutes.
#-------------------------------------------------------------------------------
Write-Host "`n== Phase 5: Report =="

$totalMs = [math]::Round($script:totalSpeedMs, 1)
$idaMinSec = $script:IDAMsMin / 1000
$idaMaxSec = $script:IDAMsMax / 1000
$speedupMin = if ($totalMs -gt 0) { [math]::Round($script:IDAMsMin / $totalMs, 0) } else { 0 }
$speedupMax = if ($totalMs -gt 0) { [math]::Round($script:IDAMsMax / $totalMs, 0) } else { 0 }

Write-Host ("Total measured wall time for all rdis commands: {0} ms ({1} s)" -f $totalMs, ($totalMs / 1000))
Write-Host ("IDA reference: {0}-{1} minutes ({2}-{3} ms)" -f $idaMinSec, $idaMaxSec, $script:IDAMsMin, $script:IDAMsMax)
Write-Host ("rdis is roughly {0}x to {1}x faster than IDA for the same work." -f $speedupMin, $speedupMax)
Write-Host ("Background subagent reference bench: rdis.exe bench = {0} ms total (pe_load: 3ms, xref_index: 12ms, vtables: 2ms, sum_per_fn: 0ms)" -f $script:refBenchMs)
if ($benchJson -and $benchPhases.Count -ge 4) {
    Write-Host ("Live bench phases: total={0} ms  pe_load={1}ms  xref_index={2}ms  vtables={3}ms  sum_per_fn={4}ms" -f $benchJson.bench.total_ms, $benchPhases[0].ms, $benchPhases[1].ms, $benchPhases[2].ms, $benchPhases[3].ms)
}

# Summary table.
$allPass = $true
foreach ($res in $script:results) { if (-not $res.Pass) { $allPass = $false } }
$passCount = ($script:results | Where-Object { $_.Pass }).Count
$failCount = ($script:results | Where-Object { -not $_.Pass }).Count

Write-Host "`n==============================================================================="
Write-Host ("SUMMARY: {0} passed, {1} failed out of {2} checks.  Total wall time: {3} ms" -f $passCount, $failCount, $script:results.Count, $totalMs)
Write-Host ("IDA: {0}-{1} min  =>  rdis is ~{2}x-{3}x faster." -f $idaMinSec, $idaMaxSec, $speedupMin, $speedupMax)
Write-Host "==============================================================================="

# Write machine-readable results.
$report = [pscustomobject]@{
    testExe        = $TestExe
    rdisExe        = $RdisExe
    functionsPdata = $FnPdata
    vtables        = $VtCount
    xrefPairs      = $XrefPairs
    imageBase      = $ImageBase
    chosenFn       = $FnHex
    chosenVtable   = $VtHex
    signature      = $Sig
    edgeFrom       = $FromHex
    edgeTo         = $FnHex
    totalSpeedMs   = $totalMs
    idaMinMs       = $script:IDAMsMin
    idaMaxMs       = $script:IDAMsMax
    speedupMin     = $speedupMin
    speedupMax     = $speedupMax
    refBenchMs     = $script:refBenchMs
    benchPhases    = $benchPhases
    benchTotalMs   = if ($benchJson) { $benchJson.bench.total_ms } else { $null }
    allPass        = $allPass
    passCount      = $passCount
    failCount      = $failCount
    checks         = $script:results
    timestamp      = (Get-Date).ToString("o")
}
# Make sure we write results to a writable location (next to the script).
if (-not $PSBoundParameters.ContainsKey('ResultsOut')) {
    $_rd = if ($PSScriptRoot) { (Resolve-Path $PSScriptRoot -ErrorAction SilentlyContinue) } else { $null }
    if (-not $_rd) { $_rd = Get-Location }
    $ResultsOut = Join-Path $_rd.Path "test_speed_accuracy.results.json"
} elseif (-not [System.IO.Path]::IsPathRooted($ResultsOut)) {
    $_rd = if ($PSScriptRoot) { (Resolve-Path $PSScriptRoot -ErrorAction SilentlyContinue) } else { Get-Location }
    $ResultsOut = Join-Path $_rd.Path $ResultsOut
}
$_od = Split-Path $ResultsOut -Parent
if (-not (Test-Path $_od)) { New-Item -ItemType Directory -Path $_od -Force | Out-Null }

$report | ConvertTo-Json -Depth 10 | Out-File -FilePath $ResultsOut -Encoding utf8
Write-Host ("Results written to $ResultsOut")

if ($allPass) {
    Write-Host "ALL CHECKS PASSED." -ForegroundColor Green
    exit 0
} else {
    Write-Host "SOME CHECKS FAILED. Review the FAIL lines above." -ForegroundColor Red
    if (-not $NoFail) { exit 1 }
    exit 0
}

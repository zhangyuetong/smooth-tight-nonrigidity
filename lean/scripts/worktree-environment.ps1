[CmdletBinding()]
param(
    [string]$Packages,
    [switch]$SeedCache,
    [string]$SeedEngine
)
$ErrorActionPreference = 'Stop'
$taskEngine = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$taskRepository = Split-Path -Parent $taskEngine
$commonGitDirectory = (& git -C $taskEngine rev-parse --path-format=absolute --git-common-dir).Trim()
if ($LASTEXITCODE -ne 0) { throw 'This checkout must be a Git worktree.' }
$workspaceRepository = Split-Path -Parent $commonGitDirectory

# Packages are a shared READ-ONLY dependency input. Never seed into this directory.
# An explicit path is authoritative: an invalid supplied cache must not silently fall back.
if ($Packages) {
    $taskPackages = $Packages
} elseif ($env:VER401_PACKAGES) {
    $taskPackages = $env:VER401_PACKAGES
} else {
    $packageCandidates = @(
        (Join-Path $taskEngine '.lake/packages'),
        (Join-Path $workspaceRepository 'lean/.lake/packages'),
        (Join-Path $workspaceRepository 'old/html_system-before-ver21-2026-09-19/formalization/lean/.lake/packages'),
        (Join-Path $env:USERPROFILE 'Desktop/tight/old/html_system-before-ver21-2026-09-19/formalization/lean/.lake/packages')
    )
    $taskPackages = $packageCandidates | Where-Object {
        Test-Path -LiteralPath (Join-Path $_ 'mathlib/Mathlib')
    } | Select-Object -First 1
}
if (-not $taskPackages -or -not (Test-Path -LiteralPath (Join-Path $taskPackages 'mathlib/Mathlib'))) {
    throw 'The pinned shared Mathlib cache is unavailable. Supply -Packages or VER401_PACKAGES.'
}
$taskPackages = (Resolve-Path -LiteralPath $taskPackages).Path
$mathlibDirectory = Join-Path $taskPackages 'mathlib'
# Permit the selected dependency repository for this process only; do not mutate Git globals.
$trustIndex = 0
if ($env:GIT_CONFIG_COUNT) { $trustIndex = [int]$env:GIT_CONFIG_COUNT }
Set-Item -LiteralPath ('Env:GIT_CONFIG_KEY_' + $trustIndex) -Value 'safe.directory'
Set-Item -LiteralPath ('Env:GIT_CONFIG_VALUE_' + $trustIndex) -Value ($mathlibDirectory.Replace([char]92, [char]47))
$env:GIT_CONFIG_COUNT = [string]($trustIndex + 1)
$revision = (& git -C $mathlibDirectory rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $revision -ne 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1') {
    throw 'The shared Mathlib cache does not match the pinned revision.'
}
$env:VER401_PACKAGES = $taskPackages

if ($SeedCache) {
    if (-not $SeedEngine) { throw '-SeedCache requires an explicit -SeedEngine source.' }
    $sourceEngine = (Resolve-Path -LiteralPath $SeedEngine).Path
    if ($sourceEngine -eq $taskEngine) { throw 'The seed source must be another engine checkout.' }
    # This pin check is an initial guard, not certification of copied proof outputs.
    foreach ($relativePin in @('upstream-lock.json', 'schoenflies-lock.json')) {
        $sourcePin = Join-Path $sourceEngine $relativePin
        $targetPin = Join-Path $taskEngine $relativePin
        if (-not (Test-Path -LiteralPath $sourcePin) -or -not (Test-Path -LiteralPath $targetPin)) {
            throw "Missing seed pin: $relativePin"
        }
        if ((Get-FileHash -LiteralPath $sourcePin -Algorithm SHA256).Hash -ne
            (Get-FileHash -LiteralPath $targetPin -Algorithm SHA256).Hash) {
            throw "Seed engine has a different foundation pin: $relativePin"
        }
    }
    foreach ($relativeCache in @('.lake/build', '.lake/compatibility-source', 'build-logs')) {
        $sourceCache = Join-Path $sourceEngine $relativeCache
        $targetCache = Join-Path $taskEngine $relativeCache
        if ((Test-Path -LiteralPath $sourceCache) -and -not (Test-Path -LiteralPath $targetCache)) {
            if ((Get-Item -LiteralPath $sourceCache).Attributes -band [IO.FileAttributes]::ReparsePoint) {
                throw "Seed cache must be an actual private directory: $sourceCache"
            }
            New-Item -ItemType Directory -Path (Split-Path -Parent $targetCache) -Force | Out-Null
            Copy-Item -LiteralPath $sourceCache -Destination $targetCache -Recurse
        }
    }
    Write-Output 'Private cache copies seeded. Builder source, compatibility, dependency and object hash guards must validate each reused output; run the current full verify before claiming proof credit.'
}
Write-Output "Pinned read-only dependencies configured: $taskPackages"
Write-Output 'Generated proof outputs and audit logs remain private to this checkout.'

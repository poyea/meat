$root = $PSScriptRoot
$env:ELAN_HOME = Join-Path $root ".elan"
$env:MATHLIB_CACHE_DIR = Join-Path $root ".cache\mathlib"
$bin = Join-Path $env:ELAN_HOME "bin"
if (-not ($env:PATH -split ';' -contains $bin)) {
    $env:PATH = "$bin;$env:PATH"
}
$meatRoot = $root
function global:book {
    Push-Location $meatRoot
    try {
        lake exe manifest
        if ($?) { typst compile --root . book/main.typ .lake/build/meat.pdf @args }
    } finally {
        Pop-Location
    }
}

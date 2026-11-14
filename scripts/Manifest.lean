import scripts.Typst
import Lean

open Lean

namespace Manifest

def inPackage (env : Environment) (pkg n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => pkg.isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

partial def resultType : Expr → Expr
  | .forallE _ _ b _ => resultType b
  | e => e

def isMeta (ci : ConstantInfo) : Bool :=
  match (resultType ci.type).getAppFn with
  | .const n _ => (`Lean).isPrefixOf n
  | _ => false

def isListed (env : Environment) (pkg : Name) (n : Name) (ci : ConstantInfo) : CoreM Bool := do
  if !inPackage env pkg n || n.isInternalDetail || isMeta ci then return false
  if isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n then return false
  match ci with
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => return false
  | _ => return (← findDeclarationRanges? n).isSome

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : CoreM String := do
  match ci with
  | .thmInfo _ => return "theorem"
  | .defnInfo _ =>
    return if (← getReducibilityStatus n) == .reducible then "abbrev" else "def"
  | .inductInfo _ => return if isStructure env n then "structure" else "inductive"
  | .axiomInfo _ => return "axiom"
  | .opaqueInfo _ => return "opaque"
  | _ => return "other"

structure State where
  sorries : Std.HashMap Name Bool := {}
  deps : Std.HashMap Name NameSet := {}

abbrev M := StateT State CoreM

partial def usesSorry (pkg : Name) (n : Name) : M Bool := do
  if let some b := (← get).sorries[n]? then return b
  modify fun s => { s with sorries := s.sorries.insert n false }
  let env ← getEnv
  let some ci := env.find? n | return false
  let mut b := false
  for u in ci.getUsedConstantsAsSet do
    if u == ``sorryAx || (inPackage env pkg u && u != n && (← usesSorry pkg u)) then
      b := true
      break
  modify fun s => { s with sorries := s.sorries.insert n b }
  return b

partial def depsOf (pkg : Name) (listed : NameSet) (n : Name) : M NameSet := do
  if let some d := (← get).deps[n]? then return d
  modify fun s => { s with deps := s.deps.insert n {} }
  let env ← getEnv
  let some ci := env.find? n | return {}
  let mut d : NameSet := {}
  for u in ci.getUsedConstantsAsSet do
    if u == n || !inPackage env pkg u then continue
    if listed.contains u then
      d := d.insert u
    else if listed.contains u.getPrefix then
      d := d.insert u.getPrefix
    else
      for v in ← depsOf pkg listed u do
        d := d.insert v
  modify fun s => { s with deps := s.deps.insert n d }
  return d

def sourcePath (mod : Name) : String :=
  "/".intercalate (mod.components.map toString) ++ ".lean"

def str (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

def arr (items : Array String) : String :=
  if items.isEmpty then "()" else "(" ++ ", ".intercalate items.toList ++ ",)"

def manifest (pkg : Name) : CoreM String := do
  let env ← getEnv
  let mut listed : NameSet := {}
  for (n, ci) in env.constants.toList do
    if ← isListed env pkg n ci then
      listed := listed.insert n
  let names := listed.toArray.qsort Name.lt
  IO.println s!"[manifest] rendering {names.size} declarations"
  let run : M (Array String) := names.mapM fun n => do
    let some ci := env.find? n | throwError "unknown constant {n}"
    let some ranges ← findDeclarationRanges? n | throwError "no range for {n}"
    let mod := moduleOf env n
    let deps := (← depsOf pkg listed n).erase n |>.toArray.qsort Name.lt
    let (hyps, stmt, unmapped) ← if ci matches .thmInfo _ then do
        let s ← (Typst.statement ci.type).run'
        pure (s.hyps.map (s!"[{·}]"), s!"${s.body}$", s.unmapped.map (str ·.toString))
      else pure (#[], "none", #[])
    return s!"  {str n.toString}: (
    name: {str n.toString},
    kind: {str (← kindOf env n ci)},
    module: {str mod.toString},
    file: {str (sourcePath mod)},
    line: {ranges.range.pos.line},
    endLine: {ranges.range.endPos.line},
    prop: {(resultType ci.type).isProp},
    sorry: {← usesSorry pkg n},
    deps: {arr (deps.map (str ·.toString))},
    hyps: {arr hyps},
    statement: {stmt},
    unmapped: {arr unmapped},
  ),"
  let (entries, _) ← run.run {}
  return Typst.preamble ++ "\n#let decls = (\n" ++ "\n".intercalate entries.toList ++ "\n)\n"


def say (msg : String) : IO Unit := do
  IO.println s!"[manifest] {msg}"
  (← IO.getStdout).flush

def seconds (start : Nat) : IO String := do
  let ms := (← IO.monoMsNow) - start
  return s!"{ms / 1000}.{(ms % 1000) / 100}s"

def inputFiles : IO (Array System.FilePath) := do
  let mut fs : Array System.FilePath := #["lakefile.toml", "lake-manifest.json", "lean-toolchain", "Meat.lean"]
  for dir in ["Meat", "scripts"] do
    unless ← System.FilePath.pathExists dir do continue
    for f in ← System.FilePath.walkDir dir do
      if f.extension == some "lean" then fs := fs.push f
  return fs.qsort (·.toString < ·.toString)

def inputHash : IO String := do
  let mut h : UInt64 := 1469598103934665603
  for f in ← inputFiles do
    h := mixHash h (hash (f.toString.replace "\\" "/"))
    h := mixHash h (hash ((← IO.FS.readFile f).replace "\r\n" "\n"))
  return toString h

def withTicker {α : Type} (label : String) (act : IO α) : IO α := do
  let start ← IO.monoMsNow
  let done ← IO.mkRef false
  let ticker ← IO.asTask (prio := .dedicated) do
    let mut next := 15000
    while !(← done.get) do
      IO.sleep 250
      if (← IO.monoMsNow) - start ≥ next then
        say s!"{label}... {← seconds start}"
        next := next + 15000
  try act finally
    done.set true
    discard <| IO.wait ticker

def buildPackage (pkg : Name) : IO Unit := do
  say s!"building {pkg}"
  let child ← IO.Process.spawn {
    cmd := (← IO.getEnv "LAKE").getD "lake"
    args := #["build", pkg.toString]
    stdin := .null }
  let rc ← child.wait
  if rc != 0 then throw <| IO.userError s!"lake build {pkg} failed"

end Manifest

open Manifest in
unsafe def main (args : List String) : IO UInt32 := do
  let pkg := `Meat
  let force := args.contains "--force"
  let out : System.FilePath := (args.filter (· != "--force")).headD ".lake/build/lean.typ"
  let stamp := out.addExtension "inputs"
  let start ← IO.monoMsNow
  let h ← inputHash
  if !force && (← out.pathExists) && (← stamp.pathExists) then
    if (← IO.FS.readFile stamp) == h then
      say s!"{out} is up to date, nothing to do (use --force to regenerate)"
      return 0
  buildPackage pkg
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let loadStart ← IO.monoMsNow
  say s!"loading {pkg} and its imports"
  let env ← withTicker "still loading" <|
    importModules #[{ module := pkg }] {} (trustLevel := 1024) (loadExts := true)
  say s!"loaded {env.header.moduleNames.size} modules in {← seconds loadStart}"
  let text ← (Manifest.manifest pkg).toIO' { fileName := "", fileMap := default } { env }
  if let some dir := out.parent then IO.FS.createDirAll dir
  IO.FS.writeFile out text
  IO.FS.writeFile stamp h
  say s!"wrote {out} in {← seconds start}"
  return 0
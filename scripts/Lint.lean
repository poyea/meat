import Batteries.Tactic.Lint

open Lean Core Elab Command Batteries.Tactic.Lint

def skipped : List Name := [`docBlame]

unsafe def lint (module : Name) : IO Bool := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module }, { module := `Batteries.Tactic.Lint }] {}
    (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  Prod.fst <$> (CoreM.toIO · ctx { env }) do
    let decls ← getDeclsInPackage module.getRoot
    let linters := (← getChecks (slow := true) (runAlways := none) (runOnly := none)).filter
      (!skipped.contains ·.name)
    let results ← lintCore decls linters (inIO := true) (currentModule := module)
    if results.any (!·.2.isEmpty) then
      let fmt ← formatLinterResults results decls (groupByFilename := true)
        (useErrorFormat := true) s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmt.toString)
      return false
    IO.println s!"-- Linting passed for {module}."
    return true

unsafe def main (args : List String) : IO Unit := do
  let modules := if args.isEmpty then [`Meat] else args.map String.toName
  let mut ok := true
  for m in modules do
    ok := (← lint m) && ok
  IO.Process.exit (if ok then 0 else 1)

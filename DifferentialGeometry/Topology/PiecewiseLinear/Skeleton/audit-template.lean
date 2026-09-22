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

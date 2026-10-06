import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3
import Mathlib.Tactic.Linter
import Lean

set_option autoImplicit false

/-! # CH12-CX3: public signatures, transitive axioms, and declaration linters -/

namespace GC.LongTime.Ch12

#check @exists_CkSmall_transfer_field_CX3
#check @transfer_isotopy_Ck_bound_CX3
#check @transfer_isotopy_of_Ck_close_CX3
#print axioms exists_CkSmall_transfer_field_CX3
#print axioms transfer_isotopy_Ck_bound_CX3
#print axioms transfer_isotopy_of_Ck_close_CX3
#print axioms exists_graph_jet_bound_CX3
#print axioms exists_transferLog_domain_CX3
#print axioms CkCloseInAtlas_id_CX3

open Lean Elab Command Batteries.Tactic.Lint

run_cmd do
  let env ← getEnv
  let modules : List Name := [
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyJets_CX3,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyBounds_CX3,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyLog_CX3,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyLogChart_CX3,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyInput_CX3,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked declaration {name}"
    if info.isAxiom || info.isUnsafe then
      throwError "Unexpected axiom or unsafe declaration {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unexpected transitive axiom {ax} in {name}"
    if info.type.getUsedConstants.contains ``sorryAx ||
        (info.value? (allowOpaque := true)).any (fun e => e.getUsedConstants.contains ``sorryAx) then
      throwError "Admission in declaration {name}"
    names := names.push name
  if names.isEmpty then throwError "Empty CX3 audit"
  let checks ← liftCoreM <| getChecks true
    (some [`unusedArguments, `simpNF, `synTaut, `unusedHavesSuffices, `explicitVarsOfIff]) none
  unless checks.size == 5 do throwError "Expected five declaration linters"
  let results ← liftCoreM <| lintCore names checks
  for (linter, findings) in results do
    unless findings.isEmpty do
      throwError "{linter.name}: {← liftCoreM <| printWarnings findings}"
  logInfo m!"CX3_AUDIT_PASS: {names.size} checked declarations; five linters; only propext, Classical.choice, Quot.sound"

end GC.LongTime.Ch12

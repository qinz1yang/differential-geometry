import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitFinal_CX6
import Mathlib.Tactic.Linter
import Lean

set_option autoImplicit false

/-! # CH12-CX6: public signatures, transitive axioms, and declaration linters -/

namespace GC.LongTime.Ch12

#check @exists_hyperbolic_subsequence_CX6
#check @thickSequenceHasHyperbolicSubsequence_CX6
#check @actualThickLimitsSequentiallyCompact_CX6
#check @eventually_no_thick_points_CX6
#check @ltf05_CX6
#print axioms exists_hyperbolic_subsequence_CX6
#print axioms thickSequenceHasHyperbolicSubsequence_CX6
#print axioms actualThickLimitsSequentiallyCompact_CX6
#print axioms eventually_no_thick_points_CX6
#print axioms ltf05_CX6
#print axioms exists_actual_diagonal_CX6
#print axioms exists_convergence_of_diagonal_CX6
#print axioms canonical_limit_volume_bound_CX6
#print axioms canonical_limit_hyperbolic_CX6
#print axioms exists_ulift_hyperbolic_model_CX6

open Lean Elab Command Batteries.Tactic.Lint

run_cmd do
  let env ← getEnv
  let modules : List Name := [
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitApproximation_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitBasic_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitClosedness_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCompactness_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitComposition_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCurvature_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitDiagonal_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitExtraction_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitFinal_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSmall_CX6,
    `DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitTransport_CX6]
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
  if names.isEmpty then throwError "Empty CX6 audit"
  let checks ← liftCoreM <| getChecks true
    (some [`unusedArguments, `simpNF, `synTaut, `unusedHavesSuffices, `explicitVarsOfIff]) none
  unless checks.size == 5 do throwError "Expected five declaration linters"
  let results ← liftCoreM <| lintCore names checks
  for (linter, findings) in results do
    unless findings.isEmpty do
      throwError "{linter.name}: {← liftCoreM <| printWarnings findings}"
  logInfo m!"CX6_AUDIT_PASS: {names.size} checked declarations; five linters; only propext, Classical.choice, Quot.sound"

end GC.LongTime.Ch12

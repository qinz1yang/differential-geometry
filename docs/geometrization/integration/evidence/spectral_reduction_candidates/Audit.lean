import DifferentialGeometry.Tensor.LinearAlgebra.Dimension.FiniteSup
import DifferentialGeometry.Analysis.InnerProductSpace.NormalProjectionSpan
import DifferentialGeometry.Analysis.InnerProductSpace.NormalSpectralSection
import DifferentialGeometry.Analysis.InnerProductSpace.FiniteNormalReduction
import Lean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [`DifferentialGeometry.Tensor.LinearAlgebra.Dimension.FiniteSup, `DifferentialGeometry.Analysis.InnerProductSpace.NormalProjectionSpan, `DifferentialGeometry.Analysis.InnerProductSpace.NormalSpectralSection, `DifferentialGeometry.Analysis.InnerProductSpace.FiniteNormalReduction]
  let skeleton : List Name := []
  let authored : List Name := [`Submodule.finrank_finset_sup_le_sum, `Submodule.finrank_finset_sup_span_singleton_sup_le, `ContinuousLinearMap.range_id_sub_sum_smul_starProjection_orthogonal_le, `ContinuousLinearMap.finrank_range_id_sub_sum_smul_starProjection_orthogonal_le, `Submodule.sum_smul_starProjection_orthogonal_mapsTo, `Submodule.sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal, `Submodule.starProjection_eigenspace_iSup_of_fixed, `Submodule.starProjection_weighted_normal_section, `Submodule.finite_affine_family_normal_reduction]
  let expected : List Name := []
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in authored do
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked authored declaration {name}"
  let mut count : Nat := 0
  let mut direct : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless owned.contains mod do continue
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked declaration {name}"
    if info.isAxiom || info.isUnsafe then
      throwError "Unexpected axiom or unsafe declaration {name}"
    if info.type.getUsedConstants.contains ``sorryAx then
      throwError "Admission in declaration type {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax || (skeleton.contains mod && ax == ``sorryAx) do
        throwError "Unexpected transitive axiom {ax} in {name}"
    let directSorry := (info.value? (allowOpaque := true)).any
      (fun e => e.getUsedConstants.contains ``sorryAx)
    if directSorry then
      unless skeleton.contains mod && info.isTheorem && expected.contains name do
        throwError "Unregistered direct admission {name}"
      direct := direct + 1
    let fmt ← liftTermElabM <| Meta.ppExpr info.type
    let row := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("direct_sorry", toJson directSorry),
      ("theorem", toJson info.isTheorem),
      ("type", toJson fmt.pretty),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
      ("axioms", toJson (axs.toList.map Name.toString))]
    logInfo m!"INTEGRATION_DECL {row.compress}"
    count := count + 1
  unless direct == expected.length do
    throwError "Expected {expected.length} direct admissions; observed {direct}"
  if count == 0 then throwError "Empty integration audit"
  logInfo m!"INTEGRATION_AUDIT_PASS {count} declarations, {direct} direct admissions"

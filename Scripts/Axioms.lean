import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement
import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Pullback
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Tensor.Exterior.Leibniz
import DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm
import DifferentialGeometry.Tensor.Exterior.ZeroForm
import DifferentialGeometry.Analysis.Schauder.VariableCoefficient
import DifferentialGeometry.Analysis.Parabolic.Euclidean.BallInteriorSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.NondivergenceSchauder
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let heads : Array String := #[
    "ContinuousAlternatingMap.wedge_mul_assoc",
    "ContinuousAlternatingMap.wedge_antisymm",
    "ContinuousAlternatingMap.domDomCongr_finAddFlip_wedge_self",
    "ContinuousAlternatingMap.wedge_self_odd_zero",
    "ContinuousAlternatingMap.factorial_nsmul_wedge_product_eq_alternatization",
    "ContinuousAlternatingMap.wedge_product_eq_alternatization",
    "ContinuousAlternatingMap.elementaryCovector_wedge",
    "Equiv.Perm.ThreeShuffle.leftShuffle",
    "Equiv.Perm.ThreeShuffle.rightShuffle",
    "Equiv.Perm.ThreeShuffle.sign_canonicalLeft_canonicalRight",
    "DifferentialGeometry.DifferentialForm.wedge_assoc",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_sq",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_wedge",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_pullback",
    "DifferentialGeometry.ModelDifferentialForm.extDeriv_extDeriv",
    "DifferentialGeometry.ModelDifferentialForm.extDeriv_pullback",
    "DifferentialGeometry.DifferentialForm.deRhamCohomology",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap_comp",
    "DifferentialGeometry.DifferentialForm.zeroFormLinearEquiv",
    "DifferentialGeometry.Analysis.Schauder.variable_coefficient_schauder_estimate_of_small_oscillation",
    "DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolic_variable_coefficient_ball_interior_schauder_estimate",
    "DifferentialGeometry.Analysis.Parabolic.Euclidean.exists_parabolic_nondivergence_schauder_estimate",
    "DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_locally_lipschitz"
  ]
  let mut failed := false
  for s in heads do
    let parts := s.splitOn "."
    let nm := parts.foldl (fun acc p => Name.str acc p) Name.anonymous
    if !env.contains nm then
      failed := true
      logError m!"MISSING AXIOM-TARGET: {s}"
      continue
    let axioms ← liftCoreM <| Lean.collectAxioms nm
    if axioms.contains ``sorryAx then
      failed := true
      logError m!"{s} depends on sorryAx"
    let bad := axioms.filter fun a =>
      a != ``propext && a != ``Classical.choice && a != ``Quot.sound
    if !bad.isEmpty then
      failed := true
      for a in bad do
        logError m!"{s} depends on unapproved axiom {a}"
  if failed then
    throwError "axiom closure check failed"

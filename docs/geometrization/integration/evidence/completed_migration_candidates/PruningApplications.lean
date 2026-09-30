import DifferentialGeometry.Analysis.Calculus.PrunedGraph
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open ContinuousLinearMap

namespace PruningApplications

private abbrev H := EuclideanSpace ℝ (Fin 2)
private noncomputable def U (i : Fin 2) : ℝ →L[ℝ] H :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (PiLp.single 2 i (1 : ℝ))
private noncomputable def Q : H →L[ℝ] ℝ := innerSL ℝ (PiLp.single 2 0 (1 : ℝ))
private noncomputable def K : H →L[ℝ] H := (U 0).comp Q
private noncomputable def T : ℝ →L[ℝ] H := U 0 + (1 / 10 : ℝ) • U 1

private theorem norm_U (i : Fin 2) : ‖U i‖ = 1 := by
  simp [U, norm_smulRight_apply, PiLp.norm_single]
private theorem norm_Q : ‖Q‖ = 1 := by simp [Q, innerSL_apply_norm, PiLp.norm_single]
private theorem QT : Q.comp (K.comp T) = ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp [Q, K, T, U, EuclideanSpace.inner_single_left, PiLp.single_eq_of_ne]
private theorem KU : K.comp (U 0) = U 0 := by
  ext z
  simp [Q, K, U]

example : K (PiLp.single 2 (1 : Fin 2) (1 : ℝ)) = 0 := by
  simp [Q, K, U, EuclideanSpace.inner_single_left, PiLp.single_eq_of_ne]

example :
    Function.Surjective ((K.comp T).range.orthogonalProjectionOnto.comp (U 0)) := by
  have hK : ‖K‖ ≤ 1 := by
    exact (opNorm_comp_le _ _).trans (by rw [norm_U, norm_Q]; norm_num)
  have hT : ‖T‖ ≤ 11 / 10 := by
    have hh := norm_add_le (U 0) ((1 / 10 : ℝ) • U 1)
    norm_num [norm_smul, norm_U] at hh
    exact hh
  have he : ‖U 0 - T.comp (ContinuousLinearMap.id ℝ ℝ)‖ ≤ 1 / 10 := by
    have hid : U 0 - T.comp (ContinuousLinearMap.id ℝ ℝ) = (-1 / 10 : ℝ) • U 1 := by
      simp only [comp_id, T]
      module
    rw [hid, norm_smul, norm_U]
    norm_num
  exact (pruned_graph_range_surjective_of_approximation K Q T
    (ContinuousLinearMap.id ℝ ℝ) (U 0) hK (by rw [norm_Q]) QT KU
    (a := 1) (e := 1 / 10) (b := 11 / 10) (l := 1)
    (by norm_num) (by norm_num) (by intro z; rw [adjoint_id]; simp) hT (by simp) he).1

end PruningApplications

open PruningApplications

example :
    let A := fderiv ℝ (K ∘ T) (0 : ℝ)
    Function.Surjective (A.range.orthogonalProjectionOnto.comp (fderiv ℝ (U 0) 0)) := by
  have hK : ‖K‖ ≤ 1 := (opNorm_comp_le _ _).trans (by rw [norm_U, norm_Q]; norm_num)
  have hT : ‖T‖ ≤ 11 / 10 := by
    have hh := norm_add_le (U 0) ((1 / 10 : ℝ) • U 1)
    norm_num [norm_smul, norm_U] at hh
    exact hh
  have he : ‖U 0 - T.comp (ContinuousLinearMap.id ℝ ℝ)‖ ≤ 1 / 10 := by
    have hid : U 0 - T.comp (ContinuousLinearMap.id ℝ ℝ) = (-1 / 10 : ℝ) • U 1 := by
      simp only [comp_id, T]
      module
    rw [hid, norm_smul, norm_U]
    norm_num
  have hh := DifferentialGeometry.Analysis.pruned_graph_derivative_surjective_of_approximation
    K Q (f := U 0) (η := id) (Φ := T) (x := 0) (U 0).differentiableAt T.differentiableAt
    (Filter.Eventually.of_forall (fun z => congrArg (fun A : ℝ →L[ℝ] H => A z) KU))
    (Filter.Eventually.of_forall (fun z => congrArg (fun A : ℝ →L[ℝ] ℝ => A z) QT))
    hK (by rw [norm_Q]) (a := 1) (e := 1 / 10) (b := 11 / 10) (l := 1)
    (by norm_num) (by norm_num) (by intro z; rw [fderiv_id, adjoint_id]; simp)
    (by rwa [T.hasFDerivAt.fderiv]) (by simp)
    (by rwa [(U 0).hasFDerivAt.fderiv, T.hasFDerivAt.fderiv, fderiv_id])
  exact hh.1

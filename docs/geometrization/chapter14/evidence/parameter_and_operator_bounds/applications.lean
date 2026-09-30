import DifferentialGeometry.Analysis.ParameterSelection.Acyclic
import DifferentialGeometry.Geometry.Metric.MarkerRecovery
import DifferentialGeometry.Analysis.InnerProductSpace.BlockNormBounds
import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation
import DifferentialGeometry.Analysis.InnerProductSpace.AdjointRankMargin
import DifferentialGeometry.Analysis.Calculus.CompositionBounds
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set GC.MetricGeometry
open scoped InnerProductSpace
namespace AnalyticRegression

theorem decreasing_parameters_on_finite_dag :
    ∃ f : Fin 3 → ℝ, (∀ i, 0 < f i) ∧ StrictAnti f := by
  classical
  have hcyc : ∀ i : Fin 3, ¬ Relation.TransGen (fun a b : Fin 3 => a < b) i i := by
    intro i h
    rw [Relation.transGen_eq_self] at h
    exact lt_irrefl i h
  have hw := Relation.wellFounded_of_finite_acyclic hcyc
  obtain ⟨f, hf, horder⟩ := hw.exists_assignment (A := fun _ => ℝ) (fun _ => Ioi 0)
    (fun i v x => ∀ j hj, x < v j hj) (by
      intro i v hv
      let J := {j : Fin 3 // j < i}
      obtain ⟨x, hx, hxb⟩ := Finset.exists_pos_lt_bounds (Finset.univ : Finset J)
        (fun j => v j.val j.property) (fun j _ => hv j.val j.property)
      exact ⟨x, hx, fun j hj => hxb ⟨j, hj⟩ (Finset.mem_univ _)⟩)
  exact ⟨f, hf, fun i j hij => horder j i hij⟩

theorem directed_cycle_rejected :
    ¬ (∀ i : Fin 2, ¬ Relation.TransGen (fun _ _ : Fin 2 => True) i i) := by
  intro h
  exact h 0 (Relation.TransGen.single trivial)

theorem incompatible_mixed_interval_rejected : ¬ ∃ x : ℝ, 2 < x ∧ x < 1 := by
  rintro ⟨x, h1, h2⟩
  linarith

theorem original_marker_threshold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} {ζ : ℝ} (hu : ‖u‖ ≤ 7)
    (hd : dist (WithLp.toLp 2 (ζ • v, ζ)) (WithLp.toLp 2 (u, (1 : ℝ))) < 1 / 100) :
    0 < ζ ∧ ‖v‖ < 36 / 5 := by
  have h := norm_coordinate_sub_lt_of_block_dist (ε := 1 / 100)
    (by norm_num) (by norm_num) hu hd
  have ht := norm_sub_le (v - u) (-u)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  constructor <;> linarith [h.1, h.2]

private noncomputable def diagonal : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun _ : Fin 2 => x)
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

theorem diagonal_two_active_blocks : ‖diagonal‖ ≤ Real.sqrt 2 := by
  have h := diagonal.norm_le_sqrt_active_blocks Finset.univ (B := 1) (by norm_num)
    (by intro x i _; change ‖x‖ ≤ 1 * ‖x‖; simp)
    (by intro x i hi; exact (hi (Finset.mem_univ i)).elim)
  simpa using h

theorem exact_common_direction_forces_equality {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1)
    (w : E) (hw : ‖w‖ = 1) (hfw : 1 ≤ f w) (hgw : 1 ≤ g w) : f = g := by
  have h := f.norm_sub_le_of_common_unit_saturation g (ε := 0)
    le_rfl (by simpa using hf) (by simpa using hg) w hw
    (by simpa using hfw) (by simpa using hgw)
  simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_zero,
    norm_le_zero_iff, sub_eq_zero] using h

theorem zero_operator_fails_positive_adjoint_margin :
    ¬ (∀ w : ℝ, 1 * ‖w‖ ≤ ‖(0 : ℝ →L[ℝ] ℝ).adjoint w‖) := by
  intro h
  have hh := h 1
  norm_num at hh

theorem scalar_rank_survives_quarter_perturbation :
    let P : ℝ →L[ℝ] ℝ := (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
    Function.Surjective P ∧ ∀ v ∈ P.kerᗮ, (3 / 4 : ℝ) * ‖v‖ ≤ ‖P v‖ := by
  let A := ContinuousLinearMap.id ℝ ℝ
  let P : ℝ →L[ℝ] ℝ := (3 / 4 : ℝ) • A
  have hA : ∀ w, (1 : ℝ) * ‖w‖ ≤ ‖A.adjoint w‖ := by
    intro w
    simp only [A, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, one_mul, le_refl]
  have hd : ‖P - A‖ ≤ (1 / 4 : ℝ) := by
    have he : P - A = (-1 / 4 : ℝ) • A := by
      apply ContinuousLinearMap.ext
      intro x
      change (3 / 4 : ℝ) * x - x = (-1 / 4 : ℝ) * x
      ring
    rw [he, norm_smul]
    norm_num [A]
  have h := P.surjective_of_adjoint_margin A (a := 1) (e := 1 / 4) hA hd (by norm_num)
  norm_num at h
  exact h

theorem affine_composition_keeps_original_budget {U V : ℝ → ℝ} {x ε : ℝ}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) (hε : 0 ≤ ε)
    (hv : ‖U x - V x‖ ≤ ε) (hd : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ‖fderiv ℝ V x‖ ≤ 100) :
    let W : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
    max ‖W (U x) - W (V x)‖
      ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤ 2 * ε := by
  let W : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hwderiv : fderiv ℝ W = fun _ : ℝ => W :=
    funext fun y => W.hasFDerivAt.fderiv
  have hW : Differentiable ℝ (fderiv ℝ W) := by
    rw [hwderiv]
    exact differentiable_const W
  have h := DifferentialGeometry.Analysis.c1_comp_sub_le_of_derivative_bounds
    W.differentiable hW hU hV (A := 2) (B := 0) (L := 100)
    (by norm_num) le_rfl (by norm_num) hε
    (by intro y; rw [hwderiv]; norm_num [W, norm_smul])
    (by intro y; rw [hwderiv]; simp) hv hd hDV
  simpa only [zero_mul, add_zero] using h

#print axioms scalar_rank_survives_quarter_perturbation
#print axioms affine_composition_keeps_original_budget

#print axioms decreasing_parameters_on_finite_dag
#print axioms directed_cycle_rejected
#print axioms incompatible_mixed_interval_rejected
#print axioms original_marker_threshold
#print axioms diagonal_two_active_blocks
#print axioms exact_common_direction_forces_equality
#print axioms zero_operator_fails_positive_adjoint_margin
end AnalyticRegression

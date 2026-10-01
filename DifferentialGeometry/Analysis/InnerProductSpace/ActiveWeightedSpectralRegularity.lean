import DifferentialGeometry.Analysis.Normed.ActiveWeightedBounds
import DifferentialGeometry.Analysis.InnerProductSpace.RealSpectralProjectionRegularity

set_option autoImplicit false
noncomputable section
open Metric ContinuousLinearMap
open scoped ContDiff
variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem real_weighted_spectral_projection_regular_rank
    (S : Finset ι) {U : Set E} (w : ι → E → ℝ) {n : ℕ∞ω}
    (hw : ∀ i ∈ S, ContDiffOn ℝ n (w i) U)
    (hw0 : ∀ y ∈ U, ∀ i ∈ S, 0 ≤ w i y)
    (hw1 : ∀ y ∈ U, ∑ i ∈ S, w i y = 1)
    (A : ι → H →L[ℝ] H) (hA : ∀ i ∈ S, (A i).toLinearMap.IsSymmetric)
    (P : Submodule ℝ H) {δ : ℝ} (hδsmall : δ < 1 / 4)
    (hclose : ∀ y ∈ U, ∀ i ∈ S, w i y ≠ 0 → ‖A i - P.starProjection‖ ≤ δ) :
    let Q : E → Submodule ℝ H := fun y =>
      ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
        Module.End.eigenspace (∑ i ∈ S, w i y • A i).toLinearMap μ
    ContDiffOn ℝ n (fun y => (Q y).starProjection) U ∧
      ∀ y ∈ U, Module.finrank ℝ (Q y) = Module.finrank ℝ P ∧
        ‖(Q y).starProjection - P.starProjection‖ ≤ 4 * δ := by
  classical
  dsimp only
  let f : E → H →L[ℝ] H := fun y => ∑ i ∈ S, w i y • A i
  have hf : ContDiffOn ℝ n f U := ContDiffOn.sum (fun i hi => (hw i hi).smul_const (A i))
  have hself (y : E) (_hy : y ∈ U) : (f y).toLinearMap.IsSymmetric := by
    intro u v
    change inner ℝ (f y u) v = inner ℝ u (f y v)
    simp only [f, sum_apply, smul_apply, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left, real_inner_smul_right, (hA i hi).apply_clm]
  have hnorm (y : E) (hy : y ∈ U) : ‖f y - P.starProjection‖ ≤ δ :=
    norm_sum_smul_sub_le_of_nonzero_close S (fun i => w i y) A P.starProjection δ
      (hw0 y hy) (hw1 y hy) (hclose y hy)
  refine ⟨hf.real_starProjection_eigenspace_ball_of_norm_sub_le hself P
    (fun y hy => (hnorm y hy).trans hδsmall.le), ?_⟩
  intro y hy
  refine ⟨finrank_real_eigenspace_ball_eq_of_norm_sub_starProjection_lt
    (f y) (hself y hy) P ((hnorm y hy).trans_lt hδsmall), ?_⟩
  exact (norm_real_starProjection_eigenspace_ball_sub_le (f y) (hself y hy) P
    ((hnorm y hy).trans hδsmall.le)).trans
      (mul_le_mul_of_nonneg_left (hnorm y hy) (by norm_num))

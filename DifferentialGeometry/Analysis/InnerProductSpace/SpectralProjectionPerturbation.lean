import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WeightedSumBounds
import Mathlib.Analysis.Normed.Module.Convex
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionBounds
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionRegularity

set_option autoImplicit false

noncomputable section

open Complex Metric ContinuousLinearMap
open scoped NNReal Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem ContDiffOn.norm_iteratedFDeriv_starProjection_eigenspace_ball_sub_le
    {U : Set E} (hU : IsOpen U) {f : E → H →L[ℂ] H} {m : ℕ}
    (hf : ContDiffOn ℝ m f U) (hself : ∀ y ∈ U, (f y).toLinearMap.IsSymmetric)
    (P : Submodule ℂ H) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4) (hσ : 0 ≤ σ)
    (hclose : ∀ y ∈ U, ‖f y - P.starProjection‖ ≤ δ) {x : E} (hx : x ∈ U)
    (B : ℝ≥0) (hD : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ δ * B * σ ^ j) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n (fun y =>
        (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace (f y).toLinearMap μ).starProjection -
          P.starProjection) x‖ ≤
        max 4 ((resolventDerivativeBound 4 B n : ℝ) / 2) * δ * σ ^ n := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hgap {z : ℂ} (hz : z ∈ sphere (1 : ℂ) (1 / 2)) :
      1 / 2 ≤ min ‖z‖ ‖z - 1‖ := by
    rw [mem_sphere, dist_eq_norm] at hz
    have hn := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, norm_sub_rev, hz] at hn
    exact le_min (by linarith) hz.ge
  have hc (y : E) (hy : y ∈ U) : sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ (f y) := by
    intro z hz
    exact mem_resolventSet_of_norm_sub_starProjection_lt (f y) P
      ((hclose y hy).trans_lt (hδsmall.trans_lt (lt_of_lt_of_le (by norm_num) (hgap hz))))
  have hK (z : ℂ) (hz : z ∈ sphere (1 : ℂ) (1 / 2)) :
      ‖_root_.resolvent (f x) z‖ ≤ (4 : ℝ≥0) := by
    have hg : (1 : ℝ) / 4 < min ‖z‖ ‖z - 1‖ := lt_of_lt_of_le (by norm_num) (hgap hz)
    apply (norm_resolvent_le_of_norm_sub_starProjection_le (f x) P
      ((hclose x hx).trans hδsmall) hg).trans
    apply (div_le_iff₀ (sub_pos.mpr hg)).mpr
    have hh := hgap hz
    norm_num only [NNReal.coe_ofNat]
    linarith
  intro n hnm
  by_cases hn : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    apply (norm_starProjection_eigenspace_ball_sub_le (f x) (hself x hx) P
      ((hclose x hx).trans hδsmall)).trans
    exact (mul_le_mul_of_nonneg_left (hclose x hx) (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ)
  · have hq : ContDiffAt ℝ n (fun y =>
        (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace (f y).toLinearMap μ).starProjection) x :=
      (((hf.starProjection_eigenspace_ball hself (by norm_num) hc) x hx).contDiffAt
        (hU.mem_nhds hx)).of_le (by exact_mod_cast hnm)
    rw [fun_iteratedFDeriv_sub_apply hq contDiffAt_const,
      iteratedFDeriv_const_of_ne hn, Pi.zero_apply, sub_zero]
    have h := hf.norm_iteratedFDeriv_starProjection_eigenspace_ball_le hU hself
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hc hx hδ (by linarith) hσ 4 B hK hD n (by omega) hnm
    apply h.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (4 : ℝ) ((resolventDerivativeBound 4 B n : ℝ) / 2)) hδ)
      (pow_nonneg hσ n)
    nlinarith

theorem norm_iteratedFDeriv_starProjection_eigenspace_ball_sum_smul_sub_le
    {ι : Type*} (S : Finset ι) {U : Set E} (hU : IsOpen U) {w : ι → E → ℝ} {m : ℕ}
    (hw : ∀ i ∈ S, ContDiffOn ℝ m (w i) U)
    (hw0 : ∀ y ∈ U, ∀ i ∈ S, 0 ≤ w i y) (hw1 : ∀ y ∈ U, ∑ i ∈ S, w i y = 1)
    (A : ι → H →L[ℂ] H) (hA : ∀ i ∈ S, (A i).toLinearMap.IsSymmetric)
    (P : Submodule ℂ H) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4) (hσ : 0 ≤ σ)
    (hclose : ∀ i ∈ S, ‖A i - P.starProjection‖ ≤ δ) {x : E} (hx : x ∈ U) (B : ℝ≥0)
    (hD : ∀ j, 1 ≤ j → j ≤ m → (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) ≤ B * σ ^ j) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n (fun y =>
        (⨆ μ ∈ ball (1 : ℂ) (1 / 2),
          Module.End.eigenspace (∑ i ∈ S, w i y • A i).toLinearMap μ).starProjection -
            P.starProjection) x‖ ≤
        max 4 ((resolventDerivativeBound 4 B n : ℝ) / 2) * δ * σ ^ n := by
  classical
  let f : E → H →L[ℂ] H := fun y => ∑ i ∈ S, w i y • A i
  have hf : ContDiffOn ℝ m f U := ContDiffOn.sum (fun i hi => (hw i hi).smul_const (A i))
  have hself (y : E) (_hy : y ∈ U) : (f y).toLinearMap.IsSymmetric := by
    intro u v
    change inner ℂ (f y u) v = inner ℂ u (f y v)
    simp only [f, sum_apply, smul_apply, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul, (hA i hi).apply_clm]
  have hdiff (y : E) (hy : y ∈ U) : f y - P.starProjection =
      ∑ i ∈ S, w i y • (A i - P.starProjection) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1 y hy, one_smul, f]
  have hfc (y : E) (hy : y ∈ U) : ‖f y - P.starProjection‖ ≤ δ := by
    rw [hdiff y hy]
    exact norm_sum_smul_le (hw0 y hy) (hw1 y hy) hclose
  have hfd (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ δ * B * σ ^ j := by
    have hfx : ContDiffAt ℝ j f x :=
      ((hf x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm)
    have heq : iteratedFDeriv ℝ j (fun y => f y - P.starProjection) x =
        iteratedFDeriv ℝ j f x := by
      rw [fun_iteratedFDeriv_sub_apply hfx contDiffAt_const,
        iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    rw [← heq]
    have h := norm_iteratedFDeriv_sum_smul_sub_le (𝕜 := ℝ) (w := w) (n := j) (x := x) S A P.starProjection
      (fun i hi => (((hw i hi) x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm))
      (Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hw1 y hy))
    apply h.trans
    calc
      _ ≤ ∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖ * δ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hclose i hi) (norm_nonneg _)
      _ = (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) * δ := (Finset.sum_mul _ _ _).symm
      _ ≤ (B * σ ^ j) * δ := mul_le_mul_of_nonneg_right (hD j hj hjm) hδ
      _ = δ * B * σ ^ j := by ring
  exact hf.norm_iteratedFDeriv_starProjection_eigenspace_ball_sub_le
    hU hself P hδ hδsmall hσ hfc hx B hfd

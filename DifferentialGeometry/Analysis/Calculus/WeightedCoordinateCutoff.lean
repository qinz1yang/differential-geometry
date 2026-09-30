import DifferentialGeometry.Analysis.Calculus.WeightedAffineCutoff
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def weightedCoordinateCutoff (s : ℝ) (φ : E → ℝ) (u : E →L[ℝ] ℝ)
    (x : E) : WithLp 2 (ℝ × ℝ) := φ x • WithLp.toLp 2 (s * u x, s)

theorem contDiff_weightedCoordinateCutoff {φ : E → ℝ} {n : WithTop ℕ∞}
    (hφ : ContDiff ℝ n φ) (s : ℝ) (u : E →L[ℝ] ℝ) :
    ContDiff ℝ n (weightedCoordinateCutoff s φ u) :=
  hφ.smul ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.contDiff.comp
    ((contDiff_const.mul u.contDiff).prodMk contDiff_const))

theorem weightedCoordinateCutoff_bounds {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (u : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1) {s Δ K : ℝ}
    (hs : |s| ≤ 2) (hΔ : 1 ≤ Δ) (hK : 0 ≤ K)
    (hvalue : ∀ y, φ y ∈ Set.Icc 0 1)
    (hfirst : ∀ y, ‖fderiv ℝ φ y‖ ≤ K / Δ)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ K / Δ ^ 2)
    (hsupport : ∀ y ∈ tsupport φ, |u y| ≤ 9 * Δ) (x : E) :
    ‖weightedCoordinateCutoff s φ u x‖ ≤ 20 * Δ ∧
      ‖fderiv ℝ (weightedCoordinateCutoff s φ u) x‖ ≤ 2 + 20 * K ∧
      ‖fderiv ℝ (fderiv ℝ (weightedCoordinateCutoff s φ u)) x‖ ≤ 24 * K / Δ := by
  have hΔ0 : 0 < Δ := by linarith
  let L : E →L[ℝ] WithLp 2 (ℝ × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp ((s • u).prod 0)
  let b : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (0, s)
  have hLy (y : E) : ‖L y‖ = |s| * |u y| := by
    change ‖WithLp.toLp 2 (s * u y, (0 : ℝ))‖ = _
    rw [WithLp.norm_toLp_fst, Real.norm_eq_abs, abs_mul]
  have hL : ‖L‖ ≤ 2 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    rw [hLy]
    have hy : |u y| ≤ ‖y‖ := (u.le_opNorm y).trans
      ((mul_le_mul_of_nonneg_right hu (norm_nonneg y)).trans_eq (one_mul _))
    exact mul_le_mul hs hy (abs_nonneg _) (by norm_num)
  have hb : ‖b‖ = |s| := by
    change ‖WithLp.toLp 2 ((0 : ℝ), s)‖ = _
    rw [WithLp.norm_toLp_snd, Real.norm_eq_abs]
  have hweight (y : E) (hy : y ∈ tsupport φ) : ‖L y + b‖ ≤ 20 * Δ := by
    have ht := norm_add_le (L y) b
    rw [hLy, hb] at ht
    have hm := mul_le_mul hs (hsupport y hy) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have heq : (fun y => φ y • (L y + b)) = weightedCoordinateCutoff s φ u := by
    funext y
    apply (WithLp.equiv 2 (ℝ × ℝ)).injective
    simp [L, b, weightedCoordinateCutoff]
  have hbnd := weighted_affine_cutoff_derivative_bounds L b hφ (M := 1) (by norm_num)
    (C := 20 * Δ) (by positivity) (div_nonneg hK hΔ0.le) (div_nonneg hK (sq_nonneg Δ))
    (fun y => by rw [abs_of_nonneg (hvalue y).1]; exact (hvalue y).2)
    hfirst hsecond hweight x
  dsimp only at hbnd
  rw [heq] at hbnd
  have h1 : K / Δ * (20 * Δ) = 20 * K := by field_simp
  have h2 : K / Δ ^ 2 * (20 * Δ) = 20 * K / Δ := by field_simp
  rw [h1, h2] at hbnd
  refine ⟨?_, ?_, ?_⟩
  · rw [← congrFun heq x, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hvalue x).1]
    by_cases hx : x ∈ tsupport φ
    · exact (mul_le_mul (hvalue x).2 (hweight x hx) (norm_nonneg _) (by norm_num)).trans_eq
        (one_mul _)
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      positivity
  · nlinarith [hbnd.1]
  · have hm := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * (K / Δ) by positivity)
    calc
      _ ≤ 2 * (K / Δ) * 2 + 20 * K / Δ := by nlinarith [hbnd.2]
      _ = _ := by ring

end DifferentialGeometry.Analysis

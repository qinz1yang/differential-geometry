import DifferentialGeometry.Analysis.Calculus.Cutoff.SmoothTransition
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The fixed sublevel profile of the edge packets (LFR24, LFR27, LFR28, LFR34)

Blueprint 207A, LFR27 (`lem:collapse-edge-scaled-core-smoothing`, A:27151): "Fix a smooth nondecreasing
profile `ψ`, constant zero on `(-∞, 1]`, equal to the identity on `[2, ∞)`, with `0 ≤ ψ ≤ 2` on `[1, 2]`
and `Lip ψ ≤ 4`." LFR24 (A:26862) uses such a profile without the Lipschitz bound, and LFR28/LFR33/LFR34
use "the SAME profile". This module fixes one: `edgeSublevelProfile` is the primitive (from `1`) of
`φ = (7/2) s((t-1)/(1/2)) - (5/2) s((t-3/2)/(1/2))`, `s` the smooth transition. Then `0 ≤ φ ≤ 7/2`,
`φ = 0` on `(-∞, 1]`, `φ = 1` on `[2, ∞)` and `∫₁² φ = 2`, so `Lip ψ ≤ 7/2 ≤ 4`.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis

/-- The derivative of the edge sublevel profile. -/
def edgeSublevelProfileDeriv (t : ℝ) : ℝ :=
  7 / 2 * smoothTransition ((t - 1) / (3 / 2 - 1)) -
    5 / 2 * smoothTransition ((t - 3 / 2) / (2 - 3 / 2))

/-- The fixed profile `ψ` of LFR27: smooth, zero on `(-∞, 1]`, the identity on `[2, ∞)`. -/
def edgeSublevelProfile (q : ℝ) : ℝ := ∫ t in (1 : ℝ)..q, edgeSublevelProfileDeriv t

theorem contDiff_edgeSublevelProfileDeriv : ContDiff ℝ ∞ edgeSublevelProfileDeriv :=
  (contDiff_const.mul (smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _))).sub
    (contDiff_const.mul (smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)))

theorem continuous_edgeSublevelProfileDeriv : Continuous edgeSublevelProfileDeriv :=
  contDiff_edgeSublevelProfileDeriv.continuous

theorem edgeSublevelProfileDeriv_eq_zero {t : ℝ} (ht : t ≤ 1) : edgeSublevelProfileDeriv t = 0 := by
  unfold edgeSublevelProfileDeriv
  rw [smoothTransition.zero_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith),
    smoothTransition.zero_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith)]
  ring

theorem edgeSublevelProfileDeriv_eq_one {t : ℝ} (ht : 2 ≤ t) : edgeSublevelProfileDeriv t = 1 := by
  unfold edgeSublevelProfileDeriv
  rw [smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith),
    smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)]
  ring

theorem edgeSublevelProfileDeriv_mem_Icc (t : ℝ) : edgeSublevelProfileDeriv t ∈ Icc 0 (7 / 2) := by
  have hmono : smoothTransition ((t - 3 / 2) / (2 - 3 / 2)) ≤
      smoothTransition ((t - 1) / (3 / 2 - 1)) :=
    smoothTransition.monotone (by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith)
  have h0 := smoothTransition.nonneg ((t - 3 / 2) / (2 - 3 / 2))
  have h1 := smoothTransition.le_one ((t - 1) / (3 / 2 - 1))
  unfold edgeSublevelProfileDeriv
  constructor <;> nlinarith

theorem hasDerivAt_edgeSublevelProfile (q : ℝ) :
    HasDerivAt edgeSublevelProfile (edgeSublevelProfileDeriv q) q :=
  (continuous_edgeSublevelProfileDeriv.integral_hasStrictDerivAt 1 q).hasDerivAt

theorem differentiable_edgeSublevelProfile : Differentiable ℝ edgeSublevelProfile :=
  fun q => (hasDerivAt_edgeSublevelProfile q).differentiableAt

theorem deriv_edgeSublevelProfile : deriv edgeSublevelProfile = edgeSublevelProfileDeriv :=
  funext fun q => (hasDerivAt_edgeSublevelProfile q).deriv

theorem contDiff_edgeSublevelProfile : ContDiff ℝ ∞ edgeSublevelProfile :=
  contDiff_infty_iff_deriv.mpr ⟨differentiable_edgeSublevelProfile,
    deriv_edgeSublevelProfile ▸ contDiff_edgeSublevelProfileDeriv⟩

theorem monotone_edgeSublevelProfile : Monotone edgeSublevelProfile :=
  monotone_of_deriv_nonneg differentiable_edgeSublevelProfile fun q => by
    rw [deriv_edgeSublevelProfile]
    exact (edgeSublevelProfileDeriv_mem_Icc q).1

/-- `Lip ψ ≤ 4` (in fact `7/2`). -/
theorem lipschitzWith_edgeSublevelProfile : LipschitzWith 4 edgeSublevelProfile := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_edgeSublevelProfile
  intro q
  rw [deriv_edgeSublevelProfile, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (edgeSublevelProfileDeriv_mem_Icc q).1]
  have := (edgeSublevelProfileDeriv_mem_Icc q).2
  norm_num
  linarith

theorem edgeSublevelProfile_eq_zero {q : ℝ} (hq : q ≤ 1) : edgeSublevelProfile q = 0 := by
  unfold edgeSublevelProfile
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
    rw [uIcc_of_ge hq] at ht
    exact edgeSublevelProfileDeriv_eq_zero ht.2)]
  simp

private theorem integral_transition_one_two :
    (∫ t in (1 : ℝ)..2, smoothTransition ((t - 1) / (3 / 2 - 1))) = 3 / 4 := by
  have hc : Continuous fun t : ℝ => smoothTransition ((t - 1) / (3 / 2 - 1)) :=
    smoothTransition.continuous.comp ((continuous_id.sub continuous_const).div_const _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    smoothTransition.integral_comp_sub_div,
    intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun t ht => by
      rw [uIcc_of_le (by norm_num)] at ht
      exact smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith [ht.1]))]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  norm_num

private theorem integral_transition_three_halves_two :
    (∫ t in (1 : ℝ)..2, smoothTransition ((t - 3 / 2) / (2 - 3 / 2))) = 1 / 4 := by
  have hc : Continuous fun t : ℝ => smoothTransition ((t - 3 / 2) / (2 - 3 / 2)) :=
    smoothTransition.continuous.comp ((continuous_id.sub continuous_const).div_const _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    smoothTransition.integral_comp_sub_div,
    intervalIntegral.integral_congr (a := 1) (b := 3 / 2) (g := fun _ => (0 : ℝ)) (fun t ht => by
      rw [uIcc_of_le (by norm_num)] at ht
      exact smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (by norm_num)))]
  norm_num

theorem edgeSublevelProfile_two : edgeSublevelProfile 2 = 2 := by
  have hc1 : Continuous fun t : ℝ => smoothTransition ((t - 1) / (3 / 2 - 1)) :=
    smoothTransition.continuous.comp ((continuous_id.sub continuous_const).div_const _)
  have hc2 : Continuous fun t : ℝ => smoothTransition ((t - 3 / 2) / (2 - 3 / 2)) :=
    smoothTransition.continuous.comp ((continuous_id.sub continuous_const).div_const _)
  unfold edgeSublevelProfile edgeSublevelProfileDeriv
  rw [intervalIntegral.integral_sub ((hc1.intervalIntegrable _ _).const_mul _)
      ((hc2.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_transition_one_two, integral_transition_three_halves_two]
  norm_num

theorem edgeSublevelProfile_eq_self {q : ℝ} (hq : 2 ≤ q) : edgeSublevelProfile q = q := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a := 1) (b := 2) (c := q)
    (continuous_edgeSublevelProfileDeriv.intervalIntegrable 1 2)
    (continuous_edgeSublevelProfileDeriv.intervalIntegrable 2 q)
  change (∫ t in (1 : ℝ)..2, edgeSublevelProfileDeriv t) +
      (∫ t in (2 : ℝ)..q, edgeSublevelProfileDeriv t) = edgeSublevelProfile q at h
  have h2 : (∫ t in (1 : ℝ)..2, edgeSublevelProfileDeriv t) = 2 := edgeSublevelProfile_two
  rw [h2, intervalIntegral.integral_congr (a := 2) (b := q) (g := fun _ => (1 : ℝ)) (fun t ht => by
    rw [uIcc_of_le hq] at ht
    exact edgeSublevelProfileDeriv_eq_one ht.1)] at h
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  linarith

theorem edgeSublevelProfile_nonneg (q : ℝ) : 0 ≤ edgeSublevelProfile q := by
  rcases le_total q 1 with hq | hq
  · exact (edgeSublevelProfile_eq_zero hq).ge
  · exact (edgeSublevelProfile_eq_zero le_rfl).symm.le.trans (monotone_edgeSublevelProfile hq)

theorem edgeSublevelProfile_le_two {q : ℝ} (hq : q ≤ 2) : edgeSublevelProfile q ≤ 2 :=
  (monotone_edgeSublevelProfile hq).trans edgeSublevelProfile_two.le

/-- The profile fixes every sublevel of level at least two: `ψ q ≤ s ↔ q ≤ s` for `s ≥ 2`. -/
theorem edgeSublevelProfile_le_iff {q s : ℝ} (hs : 2 ≤ s) : edgeSublevelProfile q ≤ s ↔ q ≤ s := by
  rcases le_total 2 q with hq | hq
  · rw [edgeSublevelProfile_eq_self hq]
  · exact ⟨fun _ => hq.trans hs, fun _ => (edgeSublevelProfile_le_two hq).trans hs⟩

/-- Near a point above two the profile is the identity. -/
theorem edgeSublevelProfile_eventuallyEq_self {q : ℝ} (hq : 2 < q) :
    edgeSublevelProfile =ᶠ[nhds q] id := by
  filter_upwards [Ioi_mem_nhds hq] with t ht using edgeSublevelProfile_eq_self (le_of_lt ht)

/-- Near a point below one the profile vanishes. -/
theorem edgeSublevelProfile_eventuallyEq_zero {q : ℝ} (hq : q < 1) :
    edgeSublevelProfile =ᶠ[nhds q] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hq] with t ht using edgeSublevelProfile_eq_zero (le_of_lt ht)

/-- LFR27's profile contract, verbatim: there is a smooth nondecreasing profile, zero on `(-∞, 1]`,
the identity on `[2, ∞)`, with values in `[0, 2]` on `[1, 2]` and Lipschitz constant at most `4`. -/
theorem exists_edgeSublevelProfile :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧ (∀ q ≤ 1, ψ q = 0) ∧ (∀ q, 2 ≤ q → ψ q = q) ∧
      (∀ q ∈ Icc (1 : ℝ) 2, ψ q ∈ Icc 0 2) ∧ LipschitzWith 4 ψ :=
  ⟨edgeSublevelProfile, contDiff_edgeSublevelProfile, monotone_edgeSublevelProfile,
    fun _ hq => edgeSublevelProfile_eq_zero hq, fun _ hq => edgeSublevelProfile_eq_self hq,
    fun _ hq => ⟨edgeSublevelProfile_nonneg _, edgeSublevelProfile_le_two hq.2⟩,
    lipschitzWith_edgeSublevelProfile⟩

end DifferentialGeometry.Analysis

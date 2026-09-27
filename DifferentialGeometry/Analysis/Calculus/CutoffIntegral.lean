import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem CutoffProfile.integral_deriv_sq_add_weighted_le_of_bound_near_zero
    {R : ℝ → ℝ} {L r n K : ℝ} (hr : 0 < r) (hrL : r ≤ L)
    (hn : 0 ≤ n) (hK : 0 ≤ K)
    (hR : IntervalIntegrable R volume 0 L)
    (hRic : ∀ s ∈ Icc (0 : ℝ) r, R s ≤ K) :
    let φ := fun s => 1 - CutoffProfile.value (1 + s / r)
    (∫ s in (0 : ℝ)..L,
      (n * deriv φ s ^ 2 + (1 - φ s ^ 2) * R s)) ≤
        n * CutoffProfile.derivBound ^ 2 / r + K * r := by
  let φ : ℝ → ℝ := fun s => 1 - CutoffProfile.value (1 + s / r)
  have hφ : ContDiff ℝ ∞ φ :=
    contDiff_const.sub (CutoffProfile.contDiff.comp (contDiff_const.add (contDiff_id.div_const r)))
  have hφd : deriv φ = fun s => -deriv CutoffProfile.value (1 + s / r) / r := by
    funext s
    have harg : HasDerivAt (fun s : ℝ => 1 + s / r) (1 / r) s :=
      ((hasDerivAt_id s).div_const r).const_add 1
    have hcomp := ((CutoffProfile.contDiff.differentiable (by simp) (1 + s / r)).hasDerivAt.comp s harg).const_sub 1
    simpa only [φ, Function.comp_def, zero_sub, div_eq_mul_inv, one_mul, neg_mul] using hcomp.deriv
  have hφrange (s : ℝ) : φ s ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨h0, h1⟩ := CutoffProfile.mem_Icc (1 + s / r)
    constructor <;> dsimp only [φ] <;> linarith
  have hφone (s : ℝ) (hs : r ≤ s) : φ s = 1 := by
    have harg : 2 ≤ 1 + s / r := by
      have : 1 ≤ s / r := (le_div_iff₀ hr).mpr (by simpa using hs)
      linarith
    simp only [φ, CutoffProfile.zero_of_two_le harg, sub_zero]
  have hφd0 (s : ℝ) (hs : r ≤ s) : deriv φ s = 0 := by
    have harg : 2 ≤ 1 + s / r := by
      have : 1 ≤ s / r := (le_div_iff₀ hr).mpr (by simpa using hs)
      linarith
    simp only [hφd, CutoffProfile.deriv_zero_of_ge harg, neg_zero, zero_div]
  have hbound (s : ℝ) : deriv φ s ^ 2 ≤ CutoffProfile.derivBound ^ 2 / r ^ 2 := by
    rw [hφd, div_pow, neg_sq]
    have hsq : (deriv CutoffProfile.value (1 + s / r)) ^ 2 ≤ CutoffProfile.derivBound ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) CutoffProfile.derivBound_nonneg).mpr
          (CutoffProfile.abs_deriv_le_derivBound (1 + s / r))
    exact div_le_div_of_nonneg_right hsq (sq_nonneg r)
  let f := fun s => n * deriv φ s ^ 2 + (1 - φ s ^ 2) * R s
  have hf : IntervalIntegrable f volume 0 L := by
    apply IntervalIntegrable.add
    · exact ((contDiff_infty_iff_deriv.mp hφ).2.continuous.pow 2).intervalIntegrable 0 L |>.const_mul n
    · exact hR.continuousOn_mul (continuous_const.sub (hφ.continuous.pow 2)).continuousOn
  have h0L : 0 ≤ L := hr.le.trans hrL
  have hf0r : IntervalIntegrable f volume 0 r := hf.mono_set (by
    simpa only [uIcc_of_le h0L, uIcc_of_le hr.le] using Icc_subset_Icc le_rfl hrL)
  have hfrL : IntervalIntegrable f volume r L := hf.mono_set (by
    simpa only [uIcc_of_le h0L, uIcc_of_le hrL] using Icc_subset_Icc hr.le le_rfl)
  have htail : ∫ s in r..L, f s = 0 := by
    have hz : (∫ s in r..L, f s) = ∫ s in r..L, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : r ≤ s := (by simpa [uIcc_of_le hrL] using hs : s ∈ Icc r L).1
      simp only [f, hφone s hs', hφd0 s hs', zero_pow (by decide : 2 ≠ 0),
        mul_zero, one_pow, sub_self, zero_mul, add_zero]
    simpa using hz
  have hlocal : ∫ s in (0 : ℝ)..r, f s ≤
      r * (n * CutoffProfile.derivBound ^ 2 / r ^ 2 + K) := by
    have h := intervalIntegral.integral_mono_on hr.le hf0r
      (intervalIntegrable_const (c := n * CutoffProfile.derivBound ^ 2 / r ^ 2 + K))
      (fun s hs => by
        have hsq0 : 0 ≤ 1 - φ s ^ 2 := by nlinarith [(hφrange s).1, (hφrange s).2]
        have hric := mul_le_mul_of_nonneg_left (hRic s hs) hsq0
        have hsqK : (1 - φ s ^ 2) * K ≤ K := by nlinarith [mul_nonneg (sq_nonneg (φ s)) hK]
        have hd := mul_le_mul_of_nonneg_left (hbound s) hn
        dsimp only [f]
        calc
          n * deriv φ s ^ 2 + (1 - φ s ^ 2) * R s ≤
              n * (CutoffProfile.derivBound ^ 2 / r ^ 2) + K := add_le_add hd (hric.trans hsqK)
          _ = n * CutoffProfile.derivBound ^ 2 / r ^ 2 + K := by ring)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
  change (∫ s in (0 : ℝ)..L, f s) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hf0r hfrL, htail, add_zero]
  convert hlocal using 1
  field_simp [hr.ne']

end DifferentialGeometry.Analysis

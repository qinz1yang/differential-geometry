import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# CX-SPINE G7: dimensionless constants for the seed first-exit window

This is an elementary numerical construction, not a new external geometric result.
Choose `k = max 1 (max J H⁻¹)`, then choose `lambda` below the four positive
radius bounds. Finally choose `delta` below the seed depth, the quadratic time
budget, and half the distance-drift budget. Every variable denominator has a positive
`+ 1` buffer. The constants are selected before any history, curvature scale,
or physical seed radius is introduced.
-/

set_option autoImplicit false

open scoped NNReal

namespace GC.LongTime.Ch11

/-- Positive dimensionless constants pay the seed radius, spatial derivative,
curvature, time derivative, and strict first-exit distance budgets simultaneously. -/
theorem exists_seed_window_constants_CXSP
    {H M Δ γ : ℝ} (hH : 4 ≤ H) (hM : 0 < M)
    (Ctime Cgrad : ℝ≥0) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    ∃ k lam delta : ℝ, 0 < k ∧ 0 < lam ∧ 0 < delta ∧
      2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4)) ≤ k ∧
      H⁻¹ ≤ k ∧ lam ≤ Real.sqrt H / 50 ∧ 2 * lam < γ * Real.sqrt H ∧
      (Cgrad : ℝ) * lam * Real.sqrt (2 * M) ≤ 1 / 4 ∧ k * lam ^ 2 ≤ 1 ∧
      delta ≤ H / 4 ∧ (Ctime : ℝ) * M * delta ≤ 1 / 2 ∧
      8 * delta / lam < Δ * Real.sqrt H := by
  have hH0 : 0 < H := by linarith
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH0
  have hsM : 0 ≤ Real.sqrt (2 * M) := Real.sqrt_nonneg _
  have hCg : 0 ≤ (Cgrad : ℝ) := Cgrad.coe_nonneg
  have hCt : 0 ≤ (Ctime : ℝ) := Ctime.coe_nonneg
  let J := 2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4))
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = max 1 (max J H⁻¹) := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by rw [hkdef]; exact le_max_left _ _
  have hk : 0 < k := zero_lt_one.trans_le hk1
  have hJ : J ≤ k := by
    rw [hkdef]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hHi : H⁻¹ ≤ k := by
    rw [hkdef]
    exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ,
      lam = min (Real.sqrt H / 100) (min (γ * Real.sqrt H / 4)
        (min (1 / (4 * ((Cgrad : ℝ) + 1) * (Real.sqrt (2 * M) + 1)))
          (1 / (k + 1)))) := ⟨_, rfl⟩
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlamH : lam ≤ Real.sqrt H / 100 := by
    rw [hlamdef]
    exact min_le_left _ _
  have hlamRest : lam ≤ min (γ * Real.sqrt H / 4)
      (min (1 / (4 * ((Cgrad : ℝ) + 1) * (Real.sqrt (2 * M) + 1)))
        (1 / (k + 1))) := by
    rw [hlamdef]
    exact min_le_right _ _
  have hlamγ : lam ≤ γ * Real.sqrt H / 4 := hlamRest.trans (min_le_left _ _)
  have hlamSmall : lam ≤
      min (1 / (4 * ((Cgrad : ℝ) + 1) * (Real.sqrt (2 * M) + 1)))
        (1 / (k + 1)) := hlamRest.trans (min_le_right _ _)
  have hlamGrad := hlamSmall.trans (min_le_left _ _)
  have hlamK := hlamSmall.trans (min_le_right _ _)
  obtain ⟨delta, hdeltaDef⟩ : ∃ delta : ℝ,
      delta = min (H / 4) (min (1 / (2 * ((Ctime : ℝ) + 1) * (M + 1)))
        (lam * Δ * Real.sqrt H / 16)) := ⟨_, rfl⟩
  have hdelta : 0 < delta := by rw [hdeltaDef]; positivity
  have hdeltaH : delta ≤ H / 4 := by
    rw [hdeltaDef]
    exact min_le_left _ _
  have hdeltaRest : delta ≤ min (1 / (2 * ((Ctime : ℝ) + 1) * (M + 1)))
      (lam * Δ * Real.sqrt H / 16) := by
    rw [hdeltaDef]
    exact min_le_right _ _
  have hdeltaTime := hdeltaRest.trans (min_le_left _ _)
  have hdeltaDrift := hdeltaRest.trans (min_le_right _ _)
  refine ⟨k, lam, delta, hk, hlam, hdelta, hJ, hHi, ?_, ?_, ?_, ?_, hdeltaH, ?_, ?_⟩
  · nlinarith only [hlamH, hsH]
  · have hpos : 0 < γ * Real.sqrt H := mul_pos hγ hsH
    nlinarith only [hlamγ, hpos]
  · have hden : 0 < 4 * ((Cgrad : ℝ) + 1) * (Real.sqrt (2 * M) + 1) := by
      positivity
    have hbound := (le_div_iff₀ hden).mp hlamGrad
    have hprod : (Cgrad : ℝ) * Real.sqrt (2 * M) ≤
        ((Cgrad : ℝ) + 1) * (Real.sqrt (2 * M) + 1) := by
      nlinarith only [hCg, hsM]
    have hprodLam := mul_le_mul_of_nonneg_left hprod hlam.le
    nlinarith only [hbound, hprodLam]
  · have hbound := (le_div_iff₀ (by positivity : 0 < k + 1)).mp hlamK
    have hkLam : k * lam ≤ 1 := by nlinarith only [hbound, hlam.le]
    have hnonneg : 0 ≤ k * lam := mul_nonneg hk.le hlam.le
    have hlamOne : lam ≤ 1 := by nlinarith only [hbound, hnonneg]
    calc
      k * lam ^ 2 = (k * lam) * lam := by ring
      _ ≤ 1 * lam := mul_le_mul_of_nonneg_right hkLam hlam.le
      _ ≤ 1 := by simpa only [one_mul] using hlamOne
  · have hden : 0 < 2 * ((Ctime : ℝ) + 1) * (M + 1) := by positivity
    have hbound := (le_div_iff₀ hden).mp hdeltaTime
    have hprod : (Ctime : ℝ) * M ≤ ((Ctime : ℝ) + 1) * (M + 1) := by
      nlinarith only [hCt, hM.le]
    have hprodDelta := mul_le_mul_of_nonneg_right hprod hdelta.le
    nlinarith only [hbound, hprodDelta]
  · apply (div_lt_iff₀ hlam).mpr
    have hpos : 0 < lam * Δ * Real.sqrt H := mul_pos (mul_pos hlam hΔ) hsH
    nlinarith only [hdeltaDrift, hpos]

end GC.LongTime.Ch11

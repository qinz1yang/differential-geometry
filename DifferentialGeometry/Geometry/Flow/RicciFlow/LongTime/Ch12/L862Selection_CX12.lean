import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Set

namespace GC.LongTime.Ch12

/-- A positive scale floor makes a strict radius reduction quantitative.
This is the slack needed when an infimum of bad times need not be attained. -/
theorem time_radius_slack_CX12 {t u r q ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hr : ρ ≤ r) (hq : 0 ≤ q) (ht : u ≤ t) (hqr : q ≤ θ * r) :
    u + q ^ 2 ≤ t + r ^ 2 - (1 - θ ^ 2) * ρ ^ 2 := by
  have hr0 : 0 ≤ r := hρ.le.trans hr
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hq2 := pow_le_pow_left₀ hq hqr 2
  rw [mul_pow] at hq2
  have hρ2 := pow_le_pow_left₀ hρ.le hr 2
  have hgap := mul_le_mul_of_nonneg_left hρ2 (by linarith : 0 ≤ 1 - θ ^ 2)
  nlinarith

/-- Approximate minimization with definite slack selects a bad configuration
whose earlier, strictly smaller-scale configurations are all good. No
compactness, continuity, or attainment of a first bad time is assumed. -/
theorem exists_bad_without_smaller_predecessor_CX12
    {ι : Type*} (time radius : ι → ℝ) (bad : Set ι)
    (hne : bad.Nonempty) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (htime : ∀ i ∈ bad, 0 ≤ time i) (hfloor : ∀ i ∈ bad, ρ ≤ radius i) :
    ∃ i ∈ bad, ∀ j, time j ≤ time i → 0 ≤ radius j → radius j ≤ θ * radius i → j ∉ bad := by
  let f : ι → ℝ := fun i => time i + radius i ^ 2
  let S : Set ℝ := f '' bad
  have hS : S.Nonempty := hne.image f
  have hbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro z ⟨i, hi, rfl⟩
    exact add_nonneg (htime i hi) (sq_nonneg _)
  let d : ℝ := (1 - θ ^ 2) * ρ ^ 2
  have hd : 0 < d := mul_pos (by nlinarith) (sq_pos_of_pos hρ)
  obtain ⟨z, hz, hzlt⟩ := exists_lt_of_csInf_lt hS
    (show sInf S < sInf S + d / 2 by linarith)
  obtain ⟨i, hi, rfl⟩ := hz
  refine ⟨i, hi, fun j hji hj0 hjr hj => ?_⟩
  have hjinf : sInf S ≤ f j := csInf_le hbelow ⟨j, hj, rfl⟩
  have hstep := time_radius_slack_CX12 hρ hθ hθ1 (hfloor i hi) hj0 hji hjr
  change f j ≤ f i - d at hstep
  linarith

/-- A uniform extension increment contradicts a putative maximal backward
depth below the target. This isolates the order-theoretic part of Sublemma
86.6; callers must construct each extended geometric window. -/
theorem depth_sup_ge_of_extension_CX12 (S : Set ℝ) {τ c : ℝ}
    (hbounded : BddAbove S) (hc : 0 < c)
    (hτ : 0 ≤ sSup S)
    (hextend : ∀ v : ℝ, 0 ≤ v → v < sSup S → v < τ → v + c ∈ S)
    (hzero : 0 ∈ S → c ∈ S) (hzero_mem : sSup S = 0 → 0 ∈ S) :
    τ ≤ sSup S := by
  by_contra hn
  have hsupτ : sSup S < τ := lt_of_not_ge hn
  by_cases hz : sSup S = 0
  · have hcmem := hzero (hzero_mem hz)
    have := le_csSup hbounded hcmem
    rw [hz] at this
    linarith
  · have hsup : 0 < sSup S := lt_of_le_of_ne hτ (Ne.symm hz)
    let d := min (sSup S / 2) (c / 2)
    have hd : 0 < d := lt_min (by positivity) (by positivity)
    have hdS : d ≤ sSup S / 2 := min_le_left _ _
    have hdc : d ≤ c / 2 := min_le_right _ _
    have hmem := hextend (sSup S - d) (by linarith) (by linarith) (by linarith)
    have := le_csSup hbounded hmem
    linarith

end GC.LongTime.Ch12

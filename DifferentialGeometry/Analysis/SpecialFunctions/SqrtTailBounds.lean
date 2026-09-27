import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith


namespace Real

theorem min_sqrt_sub_le_sqrt_sub_max_half {δ tau a : ℝ} (h : δ ≤ tau) :
    min (sqrt δ - a) (sqrt δ / 2) ≤ sqrt tau - max a (sqrt tau / 2) := by
  have hsqrt := sqrt_le_sqrt h
  rcases le_total a (sqrt tau / 2) with ha | ha
  · rw [max_eq_right ha]
    have hm := min_le_right (sqrt δ - a) (sqrt δ / 2)
    linarith
  · rw [max_eq_left ha]
    exact (min_le_left _ _).trans (sub_le_sub_right hsqrt a)

theorem min_sqrt_sub_half_pos {δ a : ℝ} (hδ : 0 < δ) (ha : a < sqrt δ) :
    0 < min (sqrt δ - a) (sqrt δ / 2) :=
  lt_min (sub_pos.mpr ha) (half_pos (sqrt_pos.mpr hδ))

theorem sqrt_midpoint_one_lt {δ : ℝ} (hδ : 1 < δ) :
    sqrt ((1 + δ) / 2) < sqrt δ := by
  apply sqrt_lt_sqrt
  · linarith
  · linarith

theorem one_sub_sq_mem_Icc_of_mem_final_tail
    {δ T tau s : ℝ} (hδ : 1 < δ) (htau : tau ∈ Set.Icc δ T)
    (hs : s ∈ Set.Icc (max (sqrt ((1 + δ) / 2)) (sqrt tau / 2)) (sqrt tau)) :
    1 - s ^ 2 ∈ Set.Icc (1 - T) (-(δ - 1) / 2) := by
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  have htaupos : 0 < tau := hδpos.trans_le htau.1
  have hmidpos : 0 ≤ (1 + δ) / 2 := by linarith
  have hlo : sqrt ((1 + δ) / 2) ≤ s := (le_max_left _ _).trans hs.1
  have hs0 : 0 ≤ s := (sqrt_nonneg _).trans hlo
  have hsquareLower := mul_self_le_mul_self (sqrt_nonneg ((1 + δ) / 2)) hlo
  have hsquareUpper := mul_self_le_mul_self hs0 hs.2
  have hmid := sq_sqrt hmidpos
  have htop := sq_sqrt htaupos.le
  constructor <;> nlinarith only [hsquareLower, hsquareUpper, hmid, htop, htau.2]

end Real

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem exists_radial_shortening {v : H} {R e : ℝ}
    (hR : 0 ≤ R) (he : 0 ≤ e) (hv : ‖v‖ ≤ R + e) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖t • v‖ ≤ R ∧ ‖v - t • v‖ ≤ e := by
  by_cases hi : ‖v‖ ≤ R
  · exact ⟨1, by norm_num, le_rfl, by simpa using hi, by simpa using he⟩
  have hpos : 0 < ‖v‖ := by linarith [norm_nonneg v]
  let t := R / ‖v‖
  have ht : 0 ≤ t := div_nonneg hR hpos.le
  have ht1 : t ≤ 1 := (div_le_one hpos).mpr (le_of_lt (lt_of_not_ge hi))
  have hmul : t * ‖v‖ = R := div_mul_cancel₀ R hpos.ne'
  refine ⟨t, ht, ht1, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hmul]
  · have heq : v - t • v = (1 - t) • v := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)]
    nlinarith

theorem hausdorffDist_truncated_range_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E →L[ℝ] H)
    (hT : ∀ v, ‖v‖ ≤ ‖T v‖) (X : Set H) (x : H) (hx : x ∈ X)
    {R q : ℝ} (hR : 0 < R) (hq : 0 ≤ q)
    (hforward : ∀ y ∈ X ∩ closedBall x R, ∃ v, dist y (x + T v) ≤ q)
    (hbackward : ∀ v, ‖v‖ ≤ R → ∃ y ∈ X, dist y (x + T v) ≤ q) :
    hausdorffDist (X ∩ closedBall x R)
      ((fun v => x + T v) '' (univ : Set E) ∩ closedBall x R) ≤ 3 * q := by
  apply hausdorffDist_le_of_mem_dist (by positivity)
  · intro y hy
    obtain ⟨v, hv⟩ := hforward y hy
    have hr : ‖T v‖ ≤ R + q := by
      have ht := dist_triangle (x + T v) y x
      have hd : dist (x + T v) x = ‖T v‖ := by simp [dist_eq_norm]
      rw [hd, dist_comm (x + T v) y] at ht
      have hyR : dist y x ≤ R := hy.2
      linarith
    obtain ⟨t, ht0, ht1, htR, hte⟩ := exists_radial_shortening hR.le hq hr
    refine ⟨x + T (t • v), ⟨⟨t • v, mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · simpa only [mem_closedBall, map_smul, dist_eq_norm, add_sub_cancel_left] using htR
    · have hd : dist (x + T v) (x + T (t • v)) = ‖T v - t • T v‖ := by
        rw [map_smul, dist_eq_norm, add_sub_add_left_eq_sub]
      have hh := dist_triangle y (x + T v) (x + T (t • v))
      rw [hd] at hh
      linarith
  · intro z hz
    by_cases hsmall : R ≤ 2 * q
    · refine ⟨x, ⟨hx, mem_closedBall_self hR.le⟩, ?_⟩
      have hr : dist z x ≤ R := hz.2
      linarith
    obtain ⟨v, _, rfl⟩ := hz.1
    have hnorm : ‖T v‖ ≤ (R - 2 * q) + 2 * q := by
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_add_cancel] using hz.2
    obtain ⟨t, ht0, ht1, htR, hte⟩ :=
      exists_radial_shortening (by linarith : 0 ≤ R - 2 * q) (by positivity) hnorm
    have htest : ‖t • v‖ ≤ R := by
      have hh := hT (t • v)
      rw [map_smul] at hh
      linarith
    obtain ⟨y, hy, hyd⟩ := hbackward (t • v) htest
    have hcenter : dist (x + T (t • v)) x ≤ R - 2 * q := by
      simpa only [map_smul, dist_eq_norm, add_sub_cancel_left] using htR
    have hyball : y ∈ closedBall x R := by
      have hh := dist_triangle y (x + T (t • v)) x
      change dist y x ≤ R
      linarith
    refine ⟨y, ⟨hy, hyball⟩, ?_⟩
    have hshort : dist (x + T v) (x + T (t • v)) ≤ 2 * q := by
      simpa only [map_smul, dist_eq_norm, add_sub_add_left_eq_sub] using hte
    have hh := dist_triangle (x + T v) (x + T (t • v)) y
    rw [dist_comm (x + T (t • v)) y] at hh
    linarith

end GC.MetricGeometry

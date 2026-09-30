import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_equal_radius_endpoints_with_excess_le
    (hsegments : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    (p a b : X) {r : ℝ} (hr : 0 ≤ r) (hra : r ≤ dist p a) (hrb : r ≤ dist p b) :
    ∃ a' b' : X, dist p a' = r ∧ dist p b' = r ∧
      dist a' a = dist p a - r ∧ dist b' b = dist p b - r ∧
      0 ≤ 2 * r - dist a' b' ∧
      2 * r - dist a' b' ≤ dist p a + dist p b - dist a b := by
  obtain ⟨ca, hca0, hca1, hca⟩ := hsegments p a
  obtain ⟨cb, hcb0, hcb1, hcb⟩ := hsegments p b
  obtain ⟨α, hα, hα0, hα1⟩ := exists_isometric_segment_of_dist_eq_mul hca0 hca1 hca
  obtain ⟨β, hβ, hβ0, hβ1⟩ := exists_isometric_segment_of_dist_eq_mul hcb0 hcb1 hcb
  let a' := α ⟨r, hr, hra⟩
  let b' := β ⟨r, hr, hrb⟩
  have ha' : dist p a' = r := by
    rw [← hα0, hα.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hr]
  have hb' : dist p b' = r := by
    rw [← hβ0, hβ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hr]
  have hta : dist a' a = dist p a - r := by
    conv_lhs => rw [← hα1, hα.dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hra)]
    ring
  have htb : dist b' b = dist p b - r := by
    conv_lhs => rw [← hβ1, hβ.dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hrb)]
    ring
  refine ⟨a', b', ha', hb', hta, htb, ?_, ?_⟩
  · have h := dist_triangle_left a' b' p
    rw [ha', hb'] at h
    linarith
  · have h := dist_triangle a a' b
    have h' := dist_triangle a' b' b
    rw [dist_comm a a', hta] at h
    rw [htb] at h'
    linarith

end Metric

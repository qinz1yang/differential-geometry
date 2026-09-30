import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Topology.MetricSpace.EqualRadiusEndpoints

set_option autoImplicit false

open Metric Set

namespace GC.MetricGeometry.KleinerLottApprox

variable {X : Type*} [MetricSpace X] {p q : X} {o δ r : ℝ}

theorem exists_opposite_line_lifts (f : KleinerLottApprox p o δ)
    (hq : q ∈ ball p δ⁻¹) (hr : 0 < r)
    (hbuffer : dist (f.toFun q) o + r < δ⁻¹ - δ) :
    ∃ a b : X, a ∈ ball p δ⁻¹ ∧ b ∈ ball p δ⁻¹ ∧
      dist (f.toFun a) (f.toFun q - r) < 2 * δ ∧
      dist (f.toFun b) (f.toFun q + r) < 2 * δ ∧
      |dist q a - r| < 3 * δ ∧ |dist q b - r| < 3 * δ ∧
      |dist a b - 2 * r| < 5 * δ := by
  have hm : dist (f.toFun q - r) (f.toFun q) = r := by
    rw [Real.dist_eq]; simp [abs_of_pos hr]
  have hp : dist (f.toFun q + r) (f.toFun q) = r := by
    rw [Real.dist_eq]; simp [abs_of_pos hr]
  have hmc : dist (f.toFun q - r) o < δ⁻¹ - δ := by
    have h := dist_triangle (f.toFun q - r) (f.toFun q) o
    rw [hm] at h
    linarith
  have hpc : dist (f.toFun q + r) o < δ⁻¹ - δ := by
    have h := dist_triangle (f.toFun q + r) (f.toFun q) o
    rw [hp] at h
    linarith
  obtain ⟨a, ha, ha'⟩ := f.coverage_witness (f.toFun q - r) hmc
  obtain ⟨b, hb, hb'⟩ := f.coverage_witness (f.toFun q + r) hpc
  rw [dist_comm] at ha' hb'
  have hqa : |dist q a - r| < 3 * δ := by
    have hd := abs_le.mp (f.distortion q hq a ha)
    have h := abs_dist_sub_le (f.toFun a) (f.toFun q - r) (f.toFun q)
    rw [hm, dist_comm (f.toFun a) (f.toFun q)] at h
    have h' := abs_le.mp h
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hqb : |dist q b - r| < 3 * δ := by
    have hd := abs_le.mp (f.distortion q hq b hb)
    have h := abs_dist_sub_le (f.toFun b) (f.toFun q + r) (f.toFun q)
    rw [hp, dist_comm (f.toFun b) (f.toFun q)] at h
    have h' := abs_le.mp h
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hab : |dist a b - 2 * r| < 5 * δ := by
    have hd := abs_le.mp (f.distortion a ha b hb)
    have h := dist_dist_dist_le (f.toFun a) (f.toFun b) (f.toFun q - r) (f.toFun q + r)
    have hm' : dist (f.toFun q - r) (f.toFun q + r) = 2 * r := by
      rw [Real.dist_eq, show f.toFun q - r - (f.toFun q + r) = -(2 * r) by ring,
        abs_neg, abs_of_pos (by positivity)]
    rw [Real.dist_eq, hm'] at h
    have h' := abs_le.mp h
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact ⟨a, b, ha, hb, ha', hb', hqa, hqb, hab⟩


theorem exists_equal_radius_line_lifts (f : KleinerLottApprox p o δ)
    (hsegments : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    (hq : q ∈ ball p δ⁻¹) (hr : 0 < r)
    (hbuffer : dist (f.toFun q) o + r < δ⁻¹ - δ) :
    ∃ (D : ℝ) (a b : X), r - 3 * δ < D ∧ D < r + 3 * δ ∧
      dist q a = D ∧ dist q b = D ∧
      0 ≤ 2 * D - dist a b ∧ 2 * D - dist a b < 11 * δ := by
  obtain ⟨a, b, _, _, _, _, ha, hb, hab⟩ := f.exists_opposite_line_lifts hq hr hbuffer
  let D := min (dist q a) (dist q b)
  obtain ⟨a', b', ha', hb', _, _, hzero, hexcess⟩ :=
    exists_equal_radius_endpoints_with_excess_le hsegments q a b
      (le_min dist_nonneg dist_nonneg) (min_le_left _ _) (min_le_right _ _)
  have ha'bound := abs_lt.mp ha
  have hb'bound := abs_lt.mp hb
  have hab'bound := abs_lt.mp hab
  refine ⟨D, a', b', ?_, ?_, ha', hb', hzero, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · exact (min_le_left _ _).trans_lt (by linarith)
  · linarith

end GC.MetricGeometry.KleinerLottApprox

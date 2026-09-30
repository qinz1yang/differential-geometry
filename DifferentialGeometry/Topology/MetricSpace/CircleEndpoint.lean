import DifferentialGeometry.Topology.MetricSpace.MetricEndpoint
import DifferentialGeometry.Topology.MetricSpace.CircleDistance
import Mathlib.Topology.MetricSpace.IsometricSMul

set_option autoImplicit false


namespace Metric

theorem not_isEndpoint_addCircle {L : ℝ} (hL : 0 < L) (p : AddCircle L) :
    ¬ IsEndpoint p := by
  have hzero : ¬ IsEndpoint (0 : AddCircle L) := by
    intro h
    let x : AddCircle L := ((L / 4 : ℝ) : AddCircle L)
    let y : AddCircle L := ((-L / 4 : ℝ) : AddCircle L)
    have hx : dist x 0 = L / 4 := by
      change dist ((L / 4 : ℝ) : AddCircle L) ((0 : ℝ) : AddCircle L) = L / 4
      rw [AddCircle.dist_coe_eq_abs_of_le_half_period hL (by
        rw [sub_zero, abs_of_pos (by positivity)]; linarith), sub_zero,
        abs_of_pos (by positivity)]
    have hy : dist 0 y = L / 4 := by
      change dist ((0 : ℝ) : AddCircle L) ((-L / 4 : ℝ) : AddCircle L) = L / 4
      rw [AddCircle.dist_coe_eq_abs_of_le_half_period hL (by
        rw [abs_of_nonneg (by linarith)]; linarith), abs_of_nonneg (by linarith)]
      ring
    have hxy : dist x y = L / 2 := by
      change dist ((L / 4 : ℝ) : AddCircle L) ((-L / 4 : ℝ) : AddCircle L) = L / 2
      rw [AddCircle.dist_coe_eq_abs_of_le_half_period hL (by
        rw [abs_of_nonneg (by linarith)]; linarith), abs_of_nonneg (by linarith)]
      ring
    rcases h x y (by rw [hx, hy, hxy]; ring) with he | he
    · rw [he, dist_self] at hx
      linarith
    · rw [he, dist_self] at hy
      linarith
  intro hp
  apply hzero
  apply (isEndpoint_isometryEquiv_iff (IsometryEquiv.addRight p) 0).mp
  simpa using hp

end Metric

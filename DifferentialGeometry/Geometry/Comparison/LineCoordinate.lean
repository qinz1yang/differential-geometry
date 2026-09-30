import DifferentialGeometry.Geometry.Comparison.LineDistance
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem lineCoordinate_sub_le_dist
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x y : X) : lineCoordinate γ x - lineCoordinate γ y ≤ dist x y := by
  let δ := lineCoordinate γ x - lineCoordinate γ y - dist x y
  let C := dist y (γ 0) ^ 2 + 2 * dist x y * dist y (γ 0) + dist x y ^ 2 -
    dist x (γ 0) ^ 2
  have hbound (r : ℝ) (hr : 0 ≤ r) : 2 * r * δ ≤ C := by
    have htri := dist_triangle x y (γ (-r))
    have htri₂ := dist_triangle y (γ 0) (γ (-r))
    rw [hγ.dist_eq, Real.dist_eq] at htri₂
    simp only [zero_sub, neg_neg, abs_of_nonneg hr] at htri₂
    have hsq := mul_self_le_mul_self (dist_nonneg (x := x) (y := γ (-r))) htri
    have hmul := mul_le_mul_of_nonneg_left htri₂ (show 0 ≤ 2 * dist x y by positivity)
    have hx := sq_dist_isometry_line hs hγ x (-r)
    have hy := sq_dist_isometry_line hs hγ y (-r)
    dsimp [δ, C]
    nlinarith
  by_contra h
  have hd : 0 < δ := by dsimp [δ]; linarith
  have hh := hbound ((|C| + 1) / (2 * δ)) (by positivity)
  have heq : 2 * ((|C| + 1) / (2 * δ)) * δ = |C| + 1 := by field_simp
  rw [heq] at hh
  linarith [le_abs_self C]

theorem lipschitzWith_lineCoordinate
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) : LipschitzWith 1 (lineCoordinate γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := lineCoordinate_sub_le_dist hs hγ y x
    rw [dist_comm y x] at h
    linarith
  · exact lineCoordinate_sub_le_dist hs hγ x y

end DifferentialGeometry.Geometry.Comparison.Toponogov

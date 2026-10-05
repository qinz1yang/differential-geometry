import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
Minimizing lenses lie within the sum of their two radial lengths. Two actual metrics satisfying
global bilipschitz inequalities give the fixed ambient radius used in local hinge approximation.
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem minimizingLens_dist_le_sum {X : Type*} [metricX : PseudoMetricSpace X]
    (o p q y : X) (hy : dist p y + dist y q = dist p q) :
    dist o y ≤ dist o p + dist o q := by
  have hp := dist_triangle o p y
  have hq := dist_triangle o q y
  have hpq := dist_triangle p o q
  rw [dist_comm q y] at hq
  rw [dist_comm p o] at hpq
  linarith

theorem bilipschitz_minimizingLens_dist_le {X : Type*} (m₁ m₂ : MetricSpace X)
    {epsilon : ℝ} (hepsilon : epsilon < 1)
    (hlow : ∀ x y : X,
      (1 - epsilon) * @dist X m₁.toDist x y ≤ @dist X m₂.toDist x y)
    (hup : ∀ x y : X,
      @dist X m₂.toDist x y ≤ (1 + epsilon) * @dist X m₁.toDist x y)
    (o a b p q y : X)
    (hp : @dist X m₂.toDist o p ≤ @dist X m₂.toDist o a)
    (hq : @dist X m₂.toDist o q ≤ @dist X m₂.toDist o b)
    (hy : @dist X m₂.toDist p y + @dist X m₂.toDist y q = @dist X m₂.toDist p q) :
    @dist X m₁.toDist o y ≤
      (1 + epsilon) / (1 - epsilon) * (@dist X m₁.toDist o a + @dist X m₁.toDist o b) := by
  have hraw := @minimizingLens_dist_le_sum X m₂.toPseudoMetricSpace o p q y hy
  have hupper : @dist X m₂.toDist o y ≤
      (1 + epsilon) * (@dist X m₁.toDist o a + @dist X m₁.toDist o b) := by
    calc
      @dist X m₂.toDist o y ≤ @dist X m₂.toDist o p + @dist X m₂.toDist o q := hraw
      _ ≤ @dist X m₂.toDist o a + @dist X m₂.toDist o b := add_le_add hp hq
      _ ≤ (1 + epsilon) * @dist X m₁.toDist o a +
          (1 + epsilon) * @dist X m₁.toDist o b := add_le_add (hup o a) (hup o b)
      _ = _ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ (show 0 < 1 - epsilon by linarith)]
  nlinarith [hlow o y]

theorem bilipschitzLens_radius_lt_twice {epsilon A : ℝ}
    (hepsilon : epsilon < 1 / 3) (hA : 0 < A) :
    (1 + epsilon) / (1 - epsilon) * A < 2 * A := by
  rw [div_mul_eq_mul_div, div_lt_iff₀ (show 0 < 1 - epsilon by linarith)]
  nlinarith

theorem real_minimizingLens_radius (y : ℝ) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    dist (0 : ℝ) y ≤ 2 := by
  have hp : dist (-1 : ℝ) y = y + 1 := by
    rw [Real.dist_eq, abs_of_nonpos (show -1 - y ≤ 0 by linarith [hy.1])]
    ring
  have hq : dist y (1 : ℝ) = 1 - y := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.2)]
    ring
  have hlens : dist (-1 : ℝ) y + dist y 1 = dist (-1 : ℝ) 1 := by
    rw [hp, hq]
    norm_num [Real.dist_eq]
    ring
  have hbound := minimizingLens_dist_le_sum (0 : ℝ) (-1) 1 y hlens
  norm_num at hbound
  simpa only [Real.dist_eq, zero_sub, abs_neg] using hbound

end DifferentialGeometry.Geometry.Comparison.Toponogov

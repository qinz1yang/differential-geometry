import DifferentialGeometry.Geometry.Comparison.ModelAngleContinuity
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false

open Filter Set Real
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPoint_distance_matrix_limit {I ι : Type*} {l : Filter I} [l.NeBot]
    {d : I → ι → ι → ℝ} {d₀ : ι → ι → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hd : ∀ i j, Tendsto (fun n => d n i j) l (𝓝 (d₀ i j)))
    (hcomp : ∀ n q x y z, 0 < d n q x → 0 < d n q y → 0 < d n q z →
      comparisonAngleNegCurvature κ (d n q x) (d n q y) (d n x y) +
        comparisonAngleNegCurvature κ (d n q y) (d n q z) (d n y z) +
        comparisonAngleNegCurvature κ (d n q z) (d n q x) (d n z x) ≤ 2 * Real.pi) :
    ∀ q x y z, 0 < d₀ q x → 0 < d₀ q y → 0 < d₀ q z →
      comparisonAngleNegCurvature κ (d₀ q x) (d₀ q y) (d₀ x y) +
        comparisonAngleNegCurvature κ (d₀ q y) (d₀ q z) (d₀ y z) +
        comparisonAngleNegCurvature κ (d₀ q z) (d₀ q x) (d₀ z x) ≤ 2 * Real.pi := by
  intro q x y z hx hy hz
  have hx' := (tendsto_order.mp (hd q x)).1 0 hx
  have hy' := (tendsto_order.mp (hd q y)).1 0 hy
  have hz' := (tendsto_order.mp (hd q z)).1 0 hz
  have hxy := tendsto_comparisonAngleNegCurvature_of_pos hκ (hd q x) (hd q y) (hd x y) hx hy
  have hyz := tendsto_comparisonAngleNegCurvature_of_pos hκ (hd q y) (hd q z) (hd y z) hy hz
  have hzx := tendsto_comparisonAngleNegCurvature_of_pos hκ (hd q z) (hd q x) (hd z x) hz hx
  apply le_of_tendsto ((hxy.add hyz).add hzx)
  filter_upwards [hx', hy', hz'] with n hnx hny hnz
  exact hcomp n q x y z hnx hny hnz

end DifferentialGeometry.Geometry.Comparison.Toponogov

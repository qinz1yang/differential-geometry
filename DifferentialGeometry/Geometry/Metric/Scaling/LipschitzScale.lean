import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open Metric
namespace GC.MetricGeometry

theorem abs_scale_ratio_sub_one_le {X : Type*} [MetricSpace X]
    {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p a : X} (hp : 0 < ρ p) :
    |ρ a / ρ p - 1| ≤ Λ * (dist a p / ρ p) := by
  have h := hρ.dist_le_mul a p
  rw [Real.dist_eq] at h
  have heq : ρ a / ρ p - 1 = (ρ a - ρ p) / ρ p := by field_simp
  rw [heq, abs_div, abs_of_pos hp]
  exact (div_le_div_of_nonneg_right h hp.le).trans_eq (by ring)

end GC.MetricGeometry

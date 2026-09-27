import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_infDist_gt_of_not_isCompact_closure {K U : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hU : ¬ IsCompact (closure U)) (R : ℝ) :
    ∃ x ∈ U, R < infDist x K := by
  classical
  by_contra hnone
  have hsub : U ⊆ cthickening R K := by
    intro x hx
    have hbound : infDist x K ≤ R := le_of_not_gt (fun h => hnone ⟨x, hx, h⟩)
    obtain ⟨y, hy, hdist⟩ := hK.exists_infDist_eq_dist hKne x
    exact mem_cthickening_of_dist_le x y R K hy (hdist ▸ hbound)
  exact hU (hK.cthickening.of_isClosed_subset isClosed_closure
    (closure_minimal hsub isClosed_cthickening))

theorem exists_tendsto_infDist_atTop_of_not_isCompact_closure {K U : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hU : ¬ IsCompact (closure U)) :
    ∃ x : ℕ → X, (∀ n, x n ∈ U) ∧ (∀ n : ℕ, (n : ℝ) < infDist (x n) K) ∧
      Tendsto (fun n => infDist (x n) K) atTop atTop := by
  classical
  choose x hx hdist using fun n : ℕ =>
    exists_infDist_gt_of_not_isCompact_closure hK hKne hU (n : ℝ)
  refine ⟨x, hx, hdist, tendsto_atTop.2 fun R => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  exact (hN.trans_le hcast).le.trans (hdist n).le

end DifferentialGeometry.Geometry.Topology

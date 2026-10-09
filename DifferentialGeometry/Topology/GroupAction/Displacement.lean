import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.MetricSpace.Basic

namespace ProperlyDiscontinuousSMul

variable (G : Type*) {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SMul G X] [ProperlyDiscontinuousSMul G X] [ContinuousConstSMul G X]

theorem exists_pos_le_dist_smul (x : X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : G, γ • x ≠ x → δ ≤ dist (γ • x) x := by
  obtain ⟨U, hU, hdisjoint⟩ := exists_nhds_disjoint_image G x
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hxU : x ∈ U := hball (Metric.mem_ball_self hδ)
  refine ⟨δ, hδ, ?_⟩
  intro γ hγ
  by_contra h
  exact Set.disjoint_left.mp (hdisjoint γ hγ) ⟨x, hxU, rfl⟩
    (hball (lt_of_not_ge h))

end ProperlyDiscontinuousSMul

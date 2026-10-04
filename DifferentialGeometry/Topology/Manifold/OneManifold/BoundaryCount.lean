import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalApplications

/-! # Boundary degree of actual compact connected one-manifolds -/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M]

theorem ncard_boundary_eq_zero_or_two :
    ((𝓡∂ 1).boundary M).ncard = 0 ∨ ((𝓡∂ 1).boundary M).ncard = 2 := by
  rcases ((𝓡∂ 1).boundary M).eq_empty_or_nonempty with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (ncard_boundary_eq_two_of_boundary_nonempty h)

end DifferentialGeometry.Topology.Manifold.OneManifold

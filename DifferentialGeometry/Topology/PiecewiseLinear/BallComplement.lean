import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedron.sdiff_interior_of_isPLBall {n : ℕ}
    {P D : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPolyhedron P)
    (hD : IsPLBall (n + 1) D) : IsPolyhedron (P \ interior D) := by
  have heq : P \ interior D = closure (P \ D) ∪ (P ∩ frontier D) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inr ⟨hx.1, subset_closure hxD, hx.2⟩
      · exact Or.inl (subset_closure ⟨hx.1, hxD⟩)
    · refine union_subset ?_ (fun _ hx => ⟨hx.1, hx.2.2⟩)
      exact closure_minimal (fun _ hx => ⟨hx.1, fun h => hx.2 (interior_subset h)⟩)
        (hP.isClosed.sdiff isOpen_interior)
  rw [heq]
  exact (hP.closure_sdiff hD.isPolyhedron).union (hP.inter hD.isPLSphere_frontier.isPolyhedron)

end DifferentialGeometry.Topology.PiecewiseLinear

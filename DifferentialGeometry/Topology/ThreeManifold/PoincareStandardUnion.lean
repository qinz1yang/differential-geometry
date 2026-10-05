import DifferentialGeometry.Topology.Manifold.DisjointUnionComponent
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology
universe u
variable {ι : Type u} [Fintype ι] (M : ι → ClosedOrientedManifold.{u} 3)

theorem componentwise_isOrientedStandardConnectedSum_closedOrientedUnion
    (hM : ∀ i, ∀ C : ConnectedComponents (M i).Carrier,
      isOrientedStandardConnectedSum ((M i).component C).toClosedOrientedManifold)
    (C : ConnectedComponents (closedOrientedUnion M).Carrier) :
    isOrientedStandardConnectedSum ((closedOrientedUnion M).component C).toClosedOrientedManifold := by
  obtain ⟨⟨i, x⟩, rfl⟩ := ConnectedComponents.surjective_coe C
  exact isOrientedStandardConnectedSum_of_orientedDiffeomorph
    (closedOrientedUnionComponent M i x).symm (hM i (ConnectedComponents.mk x))

end DifferentialGeometry.Topology

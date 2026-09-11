import DifferentialGeometry.Topology.Handle.SimplyConnected

namespace DifferentialGeometry.Topology.Handle

theorem not_joined_distinct_feet_of_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    {l : ℕ} (φ : AttachingRegion 1 l → X)
    [SimplyConnectedSpace (AdjunctionSpace 1 l φ)]
    {u v : CellBoundary 1} (huv : u ≠ v) :
    ¬ Joined (φ (u, closedCellCenter l)) (φ (v, closedCellCenter l)) := by
  intro hjoined
  exact (not_simplyConnectedSpace_adjunction_of_joined_feet φ huv hjoined)
    (inferInstance : SimplyConnectedSpace (AdjunctionSpace 1 l φ))

end DifferentialGeometry.Topology.Handle

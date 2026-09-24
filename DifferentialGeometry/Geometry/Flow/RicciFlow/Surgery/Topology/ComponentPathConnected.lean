import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

variable (P : OrientedThreeStage.{u})

theorem component_pathConnectedSpace (c : ConnectedComponents P.Carrier) :
    PathConnectedSpace (P.component c).Carrier := by
  let : LocallyPathConnectedSpace P.Carrier :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace P.Carrier
  obtain ⟨x₀, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : ({y : P.Carrier | ConnectedComponents.mk y = ConnectedComponents.mk x₀} :
      Set P.Carrier) = connectedComponent x₀ := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  change PathConnectedSpace ↥({y : P.Carrier |
    ConnectedComponents.mk y = ConnectedComponents.mk x₀})
  rw [hset, ← pathComponent_eq_connectedComponent x₀]
  exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_pathComponent (x := x₀))

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

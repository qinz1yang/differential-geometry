import DifferentialGeometry.Topology.Manifold.CountableAtlas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Homotopy.Lifting

namespace DifferentialGeometry.Topology.Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

include E in
theorem pathConnectedSpace_of_connected [ConnectedSpace M] : PathConnectedSpace M := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

theorem paths_homotopicRel [SimplyConnectedSpace M] {x y : M} (γ δ : Path x y) :
    γ.toContinuousMap.HomotopicRel δ.toContinuousMap {0, 1} :=
  SimplyConnectedSpace.paths_homotopic γ δ

end DifferentialGeometry.Topology.Manifold

import DifferentialGeometry.Topology.ThreeManifold.Model
import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure OrientedBallEmbedding (U : Type u) [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace U ∞
  closedBall_subset_source : Metric.closedBall (0 : ThreeSpace) 2 ⊆ chart.source
  preserves_orientation : ∀ x, ∀ hx : x ∈ chart.source,
    Orientation.map (Fin 3)
      (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ chart hx)
        (by simp)).toLinearEquiv
      (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
      o.orientation (chart x)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

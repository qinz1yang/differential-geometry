import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}


structure SpatialNeck (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M) where
  eps_pos : 0 < eps
  eps_small : eps < 1 / 11
  Q_pos : 0 < metricScalarAt g x
  cylinder : CylinderReference
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  center : Sphere 2
  center_eq : map (center, 0) = x
  domain : Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ map.source
  comparison : MetricComparisonOn (fun _ => cylinder.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) Q_pos g) map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) {0} (⌈eps⁻¹⌉₊) eps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

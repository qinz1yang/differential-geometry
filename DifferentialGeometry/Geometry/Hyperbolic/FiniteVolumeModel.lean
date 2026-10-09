import DifferentialGeometry.Geometry.Hyperbolic.Rigidity
import DifferentialGeometry.Topology.Manifold.Orientation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic
open Set
open Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Hyperbolic
universe u

structure FiniteVolumeHyperbolicModel where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Carrier]
  [smooth : IsManifold (𝓡 3) ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [sigmaCompact : SigmaCompactSpace Carrier]
  [connected : ConnectedSpace Carrier]
  orientation : ManifoldOrientation (𝓡 3) Carrier 3
  metric : SmoothRiemannianMetric (𝓡 3) Carrier
  basepoint : Carrier
  curvature : hasConstantSectionalCurvature metric (-(1 / 4 : ℝ))
  complete : RiemannianMetricComplete metric
  finite_volume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) Carrier metric univ < ⊤

attribute [instance] FiniteVolumeHyperbolicModel.topology FiniteVolumeHyperbolicModel.charts FiniteVolumeHyperbolicModel.smooth
  FiniteVolumeHyperbolicModel.hausdorff FiniteVolumeHyperbolicModel.sigmaCompact FiniteVolumeHyperbolicModel.connected

end DifferentialGeometry.Geometry.Hyperbolic

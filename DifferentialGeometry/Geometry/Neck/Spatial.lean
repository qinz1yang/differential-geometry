import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

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

end

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

def SpatialNeck.scaleMetric (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    SpatialNeck (DifferentialGeometry.scaleMetric c hc g) eps p := by
  have hscalar : 0 < metricScalarAt (DifferentialGeometry.scaleMetric c hc g) p := by
    rw [metricScalarAt_scaleMetric]
    exact mul_pos (inv_pos.mpr hc) nk.Q_pos
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hscalar
    cylinder := nk.cylinder
    map := nk.map
    center := nk.center
    center_eq := nk.center_eq
    domain := nk.domain
    comparison := ?_ }
  have hnorm : DifferentialGeometry.scaleMetric
      (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) p) hscalar
      (DifferentialGeometry.scaleMetric c hc g) =
      DifferentialGeometry.scaleMetric (metricScalarAt g p) nk.Q_pos g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, metricScalarAt_scaleMetric]
    field_simp
  rw [hnorm]
  exact nk.comparison

@[simp] theorem SpatialNeck.scaleMetric_map (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    (nk.scaleMetric c hc).map = nk.map := rfl

@[simp] theorem SpatialNeck.scaleMetric_center (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    (nk.scaleMetric c hc).center = nk.center := rfl

@[simp] theorem SpatialNeck.scaleMetric_cylinder (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    (nk.scaleMetric c hc).cylinder = nk.cylinder := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

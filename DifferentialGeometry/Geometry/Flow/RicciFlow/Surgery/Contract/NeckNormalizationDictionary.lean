import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckContractReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u uE uH

theorem two_mul_spatialNeckScale_sq_inv {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (h : SmoothRiemannianMetric I N) (p : N) (hscalar : 0 < metricScalarAt h p) :
    2 * ((spatialNeckScale h p) ^ 2)⁻¹ = metricScalarAt h p := by
  rw [spatialNeckScale_inv_sq h p hscalar]
  ring

theorem roundCylinderMetric_scalar_eq_one (x : SpatialNeckCylinder) :
    metricScalarAt DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundCylinderMetric x = 1 := by
  rw [DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundCylinderMetric_eq_geometry,
    DifferentialGeometry.Geometry.Curvature.metricScalarAt_roundCylinder]
  norm_num

theorem two_mul_spatialNeckScale_sq_inv_roundCylinder (x : SpatialNeckCylinder) :
    2 * ((spatialNeckScale
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundCylinderMetric x) ^ 2)⁻¹ = 1 := by
  rw [two_mul_spatialNeckScale_sq_inv
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundCylinderMetric x
      (by rw [roundCylinderMetric_scalar_eq_one x]; norm_num),
    roundCylinderMetric_scalar_eq_one x]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

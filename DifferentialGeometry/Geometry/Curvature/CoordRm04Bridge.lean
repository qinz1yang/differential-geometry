import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricRm04StdAt_eq_chartRiemannCLM
    (g : SmoothRiemannianMetric I M) (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) g x X Y Z W
      = g.inner x W (chartRiemannCLM (I := I) g x X Y Z) := by
  rw [metricRm04StdAt_apply,
    show metricRm04At (I := I) g x
        = riemannCurvature04At g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl,
    riemannCurvature04At_apply_const]
  have : ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ := LeviCivita_isContMDiff g
  rw [riemannCurvatureAux_tangentConst_eq_riemannOp (metricCov (I := I) g)
      (metricCov_smooth (I := I) g) x X Y Z,
    show riemannOp (cov := metricCov (I := I) g) x X Y Z
        = riemannOp (cov := LeviCivita (I := I) g) x X Y Z from rfl,
    riemannOp_eq_chartRiemannCLM_apply]

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rm04_eq_inner_riem
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) g x X Y Z W =
      g.inner x W (riemannOp (cov := LeviCivita (I := I) g) x X Y Z) := by
  rw [metricRm04StdAt_eq_chartRiemannCLM,
    riemannOp_eq_chartRiemannCLM_apply]

end DifferentialGeometry

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Manifold
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricScalarAt_eq_zero_of_metricRm04At_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hRm : metricRm04At (I := I) g x = 0) :
    metricScalarAt (I := I) g x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hOp (u v w : TangentSpace I x) :
      riemannOp (LeviCivita (I := I) g) x u v w = 0 := by
    let R := riemannOp (LeviCivita (I := I) g) x u v w
    have hinner : g.inner x R R = 0 := by
      rw [← DifferentialGeometry.rm04_eq_inner_riem (I := I) g x u v w R]
      rw [metricRm04StdAt_apply, hRm]
      rfl
    by_contra hR
    exact (ne_of_gt (g.pos x R hR)) hinner
  apply metricScalarAt_eq_zero_of_ricciTensor_eq_zero (I := I) g x
  intro v w
  have hEndo : ricciEndo (I := I) g x v w = 0 := by
    ext u
    exact hOp u v w
  rw [ricciTensor_apply, hEndo, map_zero]

end DifferentialGeometry.Geometry.Curvature

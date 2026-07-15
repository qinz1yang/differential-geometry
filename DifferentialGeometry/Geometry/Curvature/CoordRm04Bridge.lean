import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity

/-!
# The (0,4) coordinate bridge for the metric Riemann tensor

The metric Riemann tensor `metricRm04StdAt g x X Y Z W = ⟨R(X,Y)Z, W⟩_g` (abstract,
Koszul) is expressed through the chart-Christoffel Riemann operator `chartRiemannCLM`,
the `(0,4)` analogue of `metricRicciAt_apply_eq_ricciTensor`.  Composing this with the
explicit chart-coordinate formula for `chartRiemannCLM` (Christoffel symbols of the
metric) lets one COMPUTE the curvature of an explicit metric — e.g. the round sphere.

## Main result

* `metricRm04StdAt_eq_chartRiemannCLM` :
  `metricRm04StdAt g x X Y Z W = g.inner x W (chartRiemannCLM g x X Y Z)`.
-/

namespace DifferentialGeometry

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- **The (0,4) coordinate bridge.**  The metric Riemann tensor in the standard slot
order equals the metric pairing of `W` with the chart-Christoffel Riemann operator
`chartRiemannCLM g x X Y Z = R(X,Y)Z` (in coordinates).  Reduces the abstract Koszul
curvature to the explicit Christoffel formula. -/
theorem metricRm04StdAt_eq_chartRiemannCLM
    (g : SmoothRiemannianMetric I M) (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) g x X Y Z W
      = g.inner x W (chartRiemannCLM (I := I) g x X Y Z) := by
  rw [metricRm04StdAt_apply,
    show metricRm04At (I := I) g x
        = riemannCurvature04At g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl,
    riemannCurvature04At_apply_const]
  haveI : ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ := LeviCivita_isContMDiff g
  rw [riemannCurvatureAux_tangentConst_eq_riemannOp (metricCov (I := I) g)
      (metricCov_smooth (I := I) g) x X Y Z,
    show riemannOp (cov := metricCov (I := I) g) x X Y Z
        = riemannOp (cov := LeviCivita (I := I) g) x X Y Z from rfl,
    riemannOp_eq_chartRiemannCLM_apply]

end DifferentialGeometry

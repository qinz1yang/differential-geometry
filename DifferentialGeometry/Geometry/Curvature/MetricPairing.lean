import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private instance instContMDiffMetricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ :=
  CovariantDerivative.contMDiffCovariantDerivativeOn_univ_iff.mp
    (metricCov_smooth (I := I) g isOpen_univ)

omit [SigmaCompactSpace M] in
theorem metricRm04At_inner (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04At (I := I) g x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      g.inner x
        (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g) x X Y Z)
        W := by
  have h :=
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const
      (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) X Y Z W
  rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
    (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g) x X Y Z] at h
  rw [show metricRm04At (I := I) g x =
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl, h]
  exact g.symm x W _


end DifferentialGeometry.PDE.RicciFlow

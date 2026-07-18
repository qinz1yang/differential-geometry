import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Operator.RoughLaplacianScaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false




namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


theorem metricCov_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    metricCov (I := I) (M := M) (scaleMetric (I := I) c hc g) =
      metricCov (I := I) (M := M) g := by
  unfold metricCov
  exact lcConn_scaleMetric (I := I) c hc g


private theorem riemannCurvatureAt_congr
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (hcov' : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov' ∞)
    (x : M) (h : cov = cov') :
    CovariantDerivative.riemannCurvatureAt (I := I) cov hcov x =
      CovariantDerivative.riemannCurvatureAt (I := I) cov' hcov' x := by
  subst h
  rfl


theorem metricRm13At_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13At (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      metricRm13At (I := I) (M := M) g x := by
  unfold metricRm13At
  exact riemannCurvatureAt_congr (I := I)
    (metricCov_smooth (I := I) (M := M) (scaleMetric (I := I) c hc g))
    (metricCov_smooth (I := I) (M := M) g)
    x (metricCov_scaleMetric (I := I) (M := M) c hc g)


theorem metricRicciAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      metricRicciAt (I := I) (M := M) g x := by
  rw [metricRicciAt_eq_trace, metricRicciAt_eq_trace, metricRm13At_scaleMetric]


theorem metricRm04At_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • metricRm04At (I := I) (M := M) g x := by
  rw [← metricRm04_apply, ← metricRm04_apply]
  ext v
  have hv :
      v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hv]
  simp [metricRm04, metricCov, scaleMetric_inner,
    lcConn_scaleMetric, smul_eq_mul]


theorem metricScalarAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricScalarAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c⁻¹ * metricScalarAt (I := I) (M := M) g x := by
  rw [metricScalarAt_def, metricScalarAt_def, metricRicciAt_scaleMetric,
    metricTracePair0SAt_scaleMetric]

end

end DifferentialGeometry.Integral.Connection

import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricDifference
import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section Carriers

def rmDiffLowAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
      (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x -
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
      (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x

omit [SigmaCompactSpace M] [T2Space M] in
theorem rmDiffLowAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 -> TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x v =
      metricRm04At (I := I) g₁ x v -
        DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x v :=
  Tensor0SSpace.sub_apply (I := I) 4 x _ _ v

omit [SigmaCompactSpace M] [T2Space M] in
theorem rmDiffLowAt_standard (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      metricRm13At (I := I) g₁ x
          (dualToCotangent (I := I) (tangentFlatLinear (I := I) g₁ x W))
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) -
        metricRm13At (I := I) g₂ x
          (dualToCotangent (I := I) (tangentFlatLinear (I := I) g₁ x W))
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) := by
  have hsub : rmDiffLowAt (I := I) g₁ g₂ x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) -
        DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) :=
    Tensor0SSpace.sub_apply (I := I) 4 x _ _ _
  rw [hsub,
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
      (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) X Y Z W,
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
      (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) X Y Z W]
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem rmDiffLowAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    rmDiffLowAt (I := I) g g x = 0 :=
  sub_self _

end Carriers

section Norms

def rmDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x)

omit [SigmaCompactSpace M] [T2Space M] in
theorem rmDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    rmDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x) := rfl

end Norms

end DifferentialGeometry.PDE.RicciFlow

end

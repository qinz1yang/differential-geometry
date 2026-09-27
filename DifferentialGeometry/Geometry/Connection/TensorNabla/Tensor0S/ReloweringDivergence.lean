import DifferentialGeometry.Geometry.Connection.MetricTrace.Relowering
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Relowering

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem covariant_divergence_relowering_defect
    (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) :
    covDiv0SField (I := I) g₁
        (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ T) -
          metricNabla0S (I := I) g₁ T) =
      (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ T) -
        roughLap0SField (I := I) g₁ T) +
      metricTraceFirstTwoField (I := I) g₁
        (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ T)
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) := by
  have hmetric : metricNabla0S (I := I) g₁ (metricTensorField (I := I) g₂) =
      lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) := by
    rw [lapDiffFlux, metricNabla0S_self, sub_zero]
  rw [covDiv0SField_sub, covDiv0SField, nabla_reLower, metricTraceFirstTwoField_add,
    trace_reLower, hmetric]
  change (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ T) +
    metricTraceFirstTwoField (I := I) g₁
      (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ T)
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)))) -
      roughLap0SField (I := I) g₁ T = _
  abel

end DifferentialGeometry.Geometry.Connection

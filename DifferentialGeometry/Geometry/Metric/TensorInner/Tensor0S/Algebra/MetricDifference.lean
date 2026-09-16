import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

def metricDiffAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  metricTensorField (I := I) g₁ x - metricTensorField (I := I) g₂ x

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem metricDiffAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricDiffAt (I := I) g₁ g₂ x v =
      g₁.inner x (v 0) (v 1) - g₂.inner x (v 0) (v 1) := by
  have h : metricDiffAt (I := I) g₁ g₂ x v =
      metricTensorField (I := I) g₁ x v - metricTensorField (I := I) g₂ x v :=
    Tensor0SSpace.sub_apply (I := I) 2 x
      (metricTensorField (I := I) g₁ x) (metricTensorField (I := I) g₂ x) v
  rw [h, metricTensorField_apply, metricTensorField_apply]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem metricDiffAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    metricDiffAt (I := I) g g x = 0 :=
  sub_self _

def metricDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x)

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x) := rfl


end DifferentialGeometry.PDE.RicciFlow

end

import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normSq0S_differential1FormFun_mul_le
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    normSq0S (I := I) g x 1 (differential1FormFun (I := I) (fun y => f y * h y) x) ≤
      2 * f x ^ 2 * normSq0S (I := I) g x 1 (differential1FormFun (I := I) h x) +
        2 * h x ^ 2 * normSq0S (I := I) g x 1 (differential1FormFun (I := I) f x) := by
  have heq : differential1FormFun (I := I) (fun y => f y * h y) x =
      f x • differential1FormFun (I := I) h x +
        h x • differential1FormFun (I := I) f x := by
    unfold differential1FormFun
    rw [_root_.mvfderiv_fun_mul hf hh]
    change dualToCotangentLinear (I := I)
      (f x • (mvfderiv (I := I) h x).toLinearMap +
        h x • (mvfderiv (I := I) f x).toLinearMap) = _
    rw [map_add, map_smul, map_smul]
    rfl
  rw [heq]
  simpa only [normSq0S_smul, mul_assoc] using
    _root_.Tensor0SBundle.normSq0S_add_le (I := I) g x 1
      (f x • differential1FormFun (I := I) h x)
      (h x • differential1FormFun (I := I) f x)

end DifferentialGeometry.Geometry.Operator

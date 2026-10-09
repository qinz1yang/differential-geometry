import DifferentialGeometry.Geometry.Curvature.Algebraic.SectionalLowerBound
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le
    (g : SmoothRiemannianMetric I M) (x : M) {C : ℝ}
    (hC : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ C) :
    SectionalBoundedBelowAt g x (-C) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  have hA : IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      metricRm04StandardAt g x u v w z) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  apply hA.sectional_lower_bound_of_orthogonal
    (g.inner x).toLinearMap₁₂ (g.inner x).toLinearMap₁₂ (g.pos x) (g.symm x)
  intro v w hvw
  change g.inner x v w = 0 at hvw
  change -C * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) ≤ _
  rw [hvw, zero_pow (by decide : 2 ≠ 0), sub_zero]
  have hvv := metric_inner_self_nonneg g x v
  have hww := metric_inner_self_nonneg g x w
  have hprod : (∏ a : Fin 4, Real.sqrt (g.inner x (vec4 v w w v a)
      (vec4 v w w v a))) = g.inner x v v * g.inner x w w := by
    rw [Fin.prod_univ_four]
    change Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
      Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v) = _
    calc
      _ = Real.sqrt (g.inner x v v) ^ 2 * Real.sqrt (g.inner x w w) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hvv, Real.sq_sqrt hww]
  have hCS := abs_apply_le_norm0S g x 4 (metricRm04At g x) (vec4 v w w v)
  rw [hprod] at hCS
  have hbound : |metricRm04StandardAt g x v w w v| ≤
      C * (g.inner x v v * g.inner x w w) :=
    hCS.trans (mul_le_mul_of_nonneg_right hC (mul_nonneg hvv hww))
  simpa only [neg_mul] using neg_le_of_abs_le hbound

end DifferentialGeometry.Geometry.Curvature

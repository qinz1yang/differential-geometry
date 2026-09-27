import DifferentialGeometry.Geometry.Metric.Conformal.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gradientFun_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (f : M → Real) (x : M) :
    gradientFun (conformalMetric g u) f x =
      Real.exp (-(2 * u x)) • gradientFun g f x := by
  apply metricFlatLinear_injective (conformalMetric g u) x
  ext v
  rw [metricFlatLinear_apply, metricFlatLinear_apply, inner_gradientFun,
    conformalMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [inner_gradientFun, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_mul]

theorem inner_gradientFun_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (f h : M → Real) (x : M) :
    (conformalMetric g u).inner x
        (gradientFun (conformalMetric g u) f x)
        (gradientFun (conformalMetric g u) h x) =
      Real.exp (-(2 * u x)) * g.inner x (gradientFun g f x) (gradientFun g h x) := by
  rw [gradientFun_conformalMetric, gradientFun_conformalMetric, conformalMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  calc
    _ = (Real.exp (2 * u x) * Real.exp (-(2 * u x))) *
        (Real.exp (-(2 * u x)) * g.inner x (gradientFun g f x) (gradientFun g h x)) := by ring
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

theorem normGradSqFun_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (f : M → Real) (x : M) :
    normGradSqFun (conformalMetric g u) f x =
      Real.exp (-(2 * u x)) * normGradSqFun g f x := by
  exact inner_gradientFun_conformalMetric g u f f x

end DifferentialGeometry.Geometry.Operator

import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem tensor02_cov_deriv_eq_cov_deriv_of_field
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    ∀ a : ℕ,
      tensor02CovDeriv (I := I) A gRef a =
        covDerivOfField (I := I) gRef A a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
      change metricCovDerivStep (I := I) gRef a
          (tensor02CovDeriv (I := I) A gRef a) =
        covDerivOfField (I := I) gRef A (a + 1)
      rw [ih, covDerivOfField_succ]

end HCGCompactness
end DifferentialGeometry

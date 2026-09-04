import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor

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
theorem tensor02CovDerivNormWith_eq_iterCov
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) {x : M}
    (basis : Module.Basis Idx ℝ (TangentSpace I x))
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    tensor02CovDerivNormWith (I := I) a A gRef gRef x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + a)
        (iterCov (I := I) gRef 2 A a x)) := by
  unfold tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_eq_iterCov]
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      ((iterCov (I := I) gRef 2 A a x).domDomCongr (acEquiv a))) =
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + a)
      (iterCov (I := I) gRef 2 A a x))
  rw [Tensor0SBundle.normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv a)
      (iterCov (I := I) gRef 2 A a x)]

end HCGCompactness
end DifferentialGeometry

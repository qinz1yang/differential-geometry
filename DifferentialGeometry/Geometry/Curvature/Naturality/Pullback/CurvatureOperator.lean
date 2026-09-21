import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {JH : Type*} [TopologicalSpace JH] {J : ModelWithCorners ℝ F JH}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace JH N] [IsManifold J ∞ N] [T2Space N]

theorem curvatureOperatorLowerBoundAt_localPullMetric_iff
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (K : ℝ) :
    curvatureOperatorLowerBoundAt (localPullMetric g f hf) x
      (metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x) K ↔
    curvatureOperatorLowerBoundAt g (f x) (metricAlgebraicCurvatureTensorAt g (f x)) K := by
  have he (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
      algebraicCurvatureOperatorQuadraticEval
          (metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x) c v w +
        K * algebraicCurvatureIdentityQuadraticEval (localPullMetric g f hf) c v w =
      algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g (f x)) c
          (fun i => mfderiv I J f x (v i)) (fun i => mfderiv I J f x (w i)) +
        K * algebraicCurvatureIdentityQuadraticEval g c
          (fun i => mfderiv I J f x (v i)) (fun i => mfderiv I J f x (w i)) := by
    simp only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt_coe,
      show ∀ h : SmoothRiemannianMetric I M, ∀ a b c d : TangentSpace I x,
        tensor04StandardAt (metricRm04At h x) a b c d = metricRm04StandardAt h x a b c d from
        fun _ _ _ _ _ => rfl,
      metricRm04StandardAt_localPullMetric, algebraicCurvatureIdentityQuadraticEval,
      localPullMetric_inner]
    rfl
  constructor
  · intro h n c v w
    have hs : Function.Surjective (mfderiv I J f x) := by
      exact (hf.mfderivToContinuousLinearEquiv (x := x) (by simp)).surjective
    choose v' hv using fun i => hs (v i)
    choose w' hw using fun i => hs (w i)
    have hh := h n c v' w'
    rw [he] at hh
    simpa only [hv, hw] using hh
  · intro h n c v w
    rw [he]
    exact h n c _ _
end DifferentialGeometry.Geometry.Curvature

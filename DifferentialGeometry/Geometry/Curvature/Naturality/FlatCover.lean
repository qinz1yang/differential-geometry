import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.Euclidean.Curvature
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

private theorem metricRm04StandardAt_eq_zero_of_surjective_localDiffeomorph
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hflat : ∀ (x : M) (v w z u : TangentSpace I x),
      metricRm04StandardAt (localPullMetric g f hf) x v w z u = 0)
    (y : N) (v w z u : TangentSpace J y) :
    metricRm04StandardAt g y v w z u = 0 := by
  obtain ⟨x, rfl⟩ := hsurj y
  let D := hf.mfderivToContinuousLinearEquiv (by simp) x
  have hD (V : TangentSpace J (f x)) :
      mfderiv I J f x (D.symm V) = V := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact D.apply_symm_apply V
  have h := hflat x (D.symm v) (D.symm w) (D.symm z) (D.symm u)
  rw [metricRm04StandardAt_localPullMetric, hD, hD, hD, hD] at h
  exact h

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

variable {E F K N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem metricRm04StandardAt_eq_zero_of_euclidean_cover
    (g : SmoothRiemannianMetric J N) (f : E → N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) J ∞ f) (hsurj : Function.Surjective f)
    (c : ℝ) (hc : 0 < c)
    (hmetric : ∀ (x v w : E),
      g.inner (f x)
        (mfderiv 𝓘(ℝ, E) J f x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v))
        (mfderiv 𝓘(ℝ, E) J f x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm w)) =
      c * inner ℝ v w)
    (y : N) (v w z u : TangentSpace J y) :
    metricRm04StandardAt g y v w z u = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq : localPullMetric g f hf = scaleMetric c hc euclideanMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x V W
    rw [localPullMetric_inner, scaleMetric_inner]
    change g.inner (f x) (mfderiv 𝓘(ℝ, E) J f x V)
      (mfderiv 𝓘(ℝ, E) J f x W) =
      c * inner ℝ ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) V)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) W)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      hmetric x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) V)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) W)
  apply metricRm04StandardAt_eq_zero_of_surjective_localDiffeomorph g f hf hsurj
    (fun x V W Z U => ?_) y v w z u
  rw [heq, metricRmStandard_scale]
  simp only [metricRm04StandardAt_apply, Geometry.euclideanMetric_metricRm04At_eq_zero,
    zero_apply, mul_zero]

end DifferentialGeometry.Geometry.Curvature

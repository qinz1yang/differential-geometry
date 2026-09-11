import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Bundle.PartialMfderiv.Composition

namespace DifferentialGeometry.Geometry.Operator

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem mfderiv_gradientFun_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    mfderiv I J φ x (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x) =
      gradientFun g f (φ x) := by
  apply (metricFlatEquiv g (φ x)).injective
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, inner_gradientFun]
  have hinner := inner_gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x w
  rw [SmoothRiemannianMetric.pullback_inner] at hinner
  rw [hinner, mvfderiv_comp_apply x hf (hφ x |>.mdifferentiableAt (by simp)) w]

theorem normGradSqFun_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    normGradSqFun (g.pullback φ hφ hinj) (f ∘ φ) x = normGradSqFun g f (φ x) := by
  change (g.pullback φ hφ hinj).inner x
    (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x)
    (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x) =
    g.inner (φ x) (gradientFun g f (φ x)) (gradientFun g f (φ x))
  rw [SmoothRiemannianMetric.pullback_inner,
    mfderiv_gradientFun_pullback g φ hφ hinj f x hf hsurj]

end

end DifferentialGeometry.Geometry.Operator

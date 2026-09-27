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

omit [T2Space M] in
theorem mfderiv_gradientFun_eq_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M → N) (x : M) (hΦ : MDifferentiableAt I J Φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (hsurj : Function.Surjective (mfderiv I J Φ x))
    (f : N → ℝ) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (Φ x)) :
    mfderiv I J Φ x (gradientFun g (f ∘ Φ) x) = gradientFun h f (Φ x) := by
  apply (metricFlatEquiv h (Φ x)).injective
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, inner_gradientFun, ← hinner,
    inner_gradientFun, mvfderiv_comp_apply x hf hΦ w]

omit [T2Space M] in
theorem normGradSqFun_eq_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M → N) (x : M) (hΦ : MDifferentiableAt I J Φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (hsurj : Function.Surjective (mfderiv I J Φ x))
    (f : N → ℝ) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (Φ x)) :
    normGradSqFun g (f ∘ Φ) x = normGradSqFun h f (Φ x) := by
  change g.inner x (gradientFun g (f ∘ Φ) x) (gradientFun g (f ∘ Φ) x) =
    h.inner (Φ x) (gradientFun h f (Φ x)) (gradientFun h f (Φ x))
  rw [hinner, mfderiv_gradientFun_eq_of_pullback_inner g h Φ x hΦ hinner hsurj f hf]

theorem mfderiv_gradientFun_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    mfderiv I J φ x (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x) =
      gradientFun g f (φ x) := by
  exact mfderiv_gradientFun_eq_of_pullback_inner (g.pullback φ hφ hinj) g φ x
    (hφ.mdifferentiableAt (by simp))
    (SmoothRiemannianMetric.pullback_inner g φ hφ hinj x) hsurj f hf

theorem normGradSqFun_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    normGradSqFun (g.pullback φ hφ hinj) (f ∘ φ) x = normGradSqFun g f (φ x) := by
  exact normGradSqFun_eq_of_pullback_inner (g.pullback φ hφ hinj) g φ x
    (hφ.mdifferentiableAt (by simp))
    (SmoothRiemannianMetric.pullback_inner g φ hφ hinj x) hsurj f hf

end

end DifferentialGeometry.Geometry.Operator

import DifferentialGeometry.Geometry.Operator.GradientPullback


namespace DifferentialGeometry.Geometry.Operator

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem mfderiv_gradientFun_comp_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {φ : M → N} {x : M} (hφ : MDifferentiableAt I J φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (φ x) (mfderiv I J φ x v) (mfderiv I J φ x w))
    (hsurj : Function.Surjective (mfderiv I J φ x))
    {f : N → ℝ} (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x)) :
    mfderiv I J φ x (gradientFun g (f ∘ φ) x) = gradientFun h f (φ x) := by
  apply (metricFlatEquiv h (φ x)).injective
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, inner_gradientFun,
    ← hinner, inner_gradientFun, mvfderiv_comp_apply x hf hφ w]

theorem normGradSqFun_comp_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {φ : M → N} {x : M} (hφ : MDifferentiableAt I J φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (φ x) (mfderiv I J φ x v) (mfderiv I J φ x w))
    (hsurj : Function.Surjective (mfderiv I J φ x))
    {f : N → ℝ} (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x)) :
    normGradSqFun g (f ∘ φ) x = normGradSqFun h f (φ x) := by
  change g.inner x (gradientFun g (f ∘ φ) x) (gradientFun g (f ∘ φ) x) =
    h.inner (φ x) (gradientFun h f (φ x)) (gradientFun h f (φ x))
  rw [hinner, mfderiv_gradientFun_comp_of_pullback_inner g h hφ hinner hsurj hf]

end

end DifferentialGeometry.Geometry.Operator

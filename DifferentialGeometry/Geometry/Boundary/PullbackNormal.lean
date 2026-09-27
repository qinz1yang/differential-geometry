import DifferentialGeometry.Geometry.Operator.GradientPullback
import DifferentialGeometry.Geometry.Boundary.DefiningFunction.Basic

namespace DifferentialGeometry.Geometry.Operator

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem mfderiv_levelSetOutwardNormal_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    mfderiv I J φ x (Boundary.levelSetOutwardNormal (g.pullback φ hφ hinj) (f ∘ φ) x) =
      Boundary.levelSetOutwardNormal g f (φ x) := by
  have hnorm := normGradSqFun_pullback g φ hφ hinj f x hf hsurj
  change (g.pullback φ hφ hinj).inner x
    (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x)
    (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x) =
    g.inner (φ x) (gradientFun g f (φ x)) (gradientFun g f (φ x)) at hnorm
  unfold Boundary.levelSetOutwardNormal
  rw [hnorm]
  split_ifs
  · rw [map_smul, mfderiv_gradientFun_pullback g φ hφ hinj f x hf hsurj]
  · exact map_zero _

end

end DifferentialGeometry.Geometry.Operator

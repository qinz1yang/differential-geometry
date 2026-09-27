import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Defs

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem paramGramMatrix_comp_of_metric_inner_eq
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {φ : E → M} {x : E}
    (hf : MDifferentiableAt I J f (φ x)) (hφ : MDifferentiableAt 𝓘(ℝ, E) I φ x)
    (hmetric : ∀ v w : TangentSpace I (φ x),
      h.inner (f (φ x)) (mfderiv I J f (φ x) v) (mfderiv I J f (φ x) w) =
        g.inner (φ x) v w) :
    paramGramMatrix h (f ∘ φ) x = paramGramMatrix g φ x := by
  ext i j
  simp only [paramGramMatrix_apply, mfderiv_comp x hf hφ, Function.comp_apply]
  exact hmetric _ _

theorem paramDensity_comp_of_metric_inner_eq
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {φ : E → M} {x : E}
    (hf : MDifferentiableAt I J f (φ x)) (hφ : MDifferentiableAt 𝓘(ℝ, E) I φ x)
    (hmetric : ∀ v w : TangentSpace I (φ x),
      h.inner (f (φ x)) (mfderiv I J f (φ x) v) (mfderiv I J f (φ x) w) =
        g.inner (φ x) v w) :
    paramDensity h (f ∘ φ) x = paramDensity g φ x := by
  rw [paramDensity_apply, paramDensity_apply,
    paramGramMatrix_comp_of_metric_inner_eq g h hf hφ hmetric]

end DifferentialGeometry.Integral.Measure

import DifferentialGeometry.Geometry.Comparison.Variation.EndpointGerms

open Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem centralVariationAcceleration_eq_of_endpoint_germ
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (b : ℝ)
    {beta : ℝ → M} (heq : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta) :
    (centralVariationAcceleration g f b : E) =
      (covDerivAlong g beta (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) 0 : E) := by
  have hvel : ∀ᶠ u in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r b) u (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ) : E) := by
    filter_upwards [heq.eventually_nhds] with u hu
    have hueq : (fun r ↦ f r b) =ᶠ[𝓝 u] beta := hu
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) (u : ℝ) →L[ℝ] TangentSpace I (f u b) ↦ L (1 : ℝ))
      (hueq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
  exact covDerivAlong_congr_curve g
    (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r b) u (1 : ℝ))
    (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) heq hvel

end DifferentialGeometry.Geometry.Riemannian.Variation

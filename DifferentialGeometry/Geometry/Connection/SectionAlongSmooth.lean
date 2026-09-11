import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields



noncomputable section

open Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem contMDiff_covDerivAlong (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E (γ t) (V t))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E (γ t) (covDerivAlong g γ V t)) := by
  have h := cov_snd_smooth g (fun _ t : ℝ => γ t) (fun _ t => V t)
    (hV.comp contMDiff_snd)
  exact h.comp (contMDiff_const.prodMk contMDiff_id :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)))

end DifferentialGeometry.Geometry

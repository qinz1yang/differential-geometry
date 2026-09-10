import DifferentialGeometry.Topology.Ehresmann.ProductEnds
import DifferentialGeometry.Geometry.Boundary.EmbeddedParametrization
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Topology Poincare.Geometry.Boundary
open Poincare.Topology.SphereSeparation
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_regular_height_of_labeled_sphere_product
    {E H W M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    (D : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞)
    (ι : W → M) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁) :
    ∃ u : W → ℝ, ∃ h : RegularIntervalDatum I u 0 1,
      ι '' (u ⁻¹' {0}) = range e₀ ∧ ι '' (u ⁻¹' {1}) = range e₁ ∧
      ∃ η₀ : SphereTwo ≃ₘ⟮𝓡 2, hI.boundaryI⟯
          boundaryLevel u 0 1 zero_ne_one h.smooth.continuous h.boundary_values,
      ∃ η₁ : SphereTwo ≃ₘ⟮𝓡 2, hI.boundaryI⟯
          boundaryLevel u 1 0 one_ne_zero h.smooth.continuous
            (fun w hw ↦ (h.boundary_values w hw).symm),
        (∀ p, ι (η₀ p).1.1 = e₀ p) ∧ (∀ p, ι (η₁ p).1.1 = e₁ p) := by
  obtain ⟨D', h₀, h₁⟩ := exists_intervalProduct_with_labeled_ends D ι hι.continuous
    hemb.injective (range e₀) (range e₁)
    (isPreconnected_range he₀.contMDiff.continuous) (isPreconnected_range he₁.contMDiff.continuous) hbdy
  let u := heightOfIntervalProduct D'
  have h : RegularIntervalDatum I u 0 1 := regularIntervalDatum_heightOfIntervalProduct D'
  have hfib₀ : ι '' (u ⁻¹' {0}) = range e₀ := by
    change ι '' (heightOfIntervalProduct D' ⁻¹' {((0 : unitInterval) : ℝ)}) = range e₀
    rw [preimage_heightOfIntervalProduct_singleton D' 0, ← range_comp]
    exact h₀
  have hfib₁ : ι '' (u ⁻¹' {1}) = range e₁ := by
    change ι '' (heightOfIntervalProduct D' ⁻¹' {((1 : unitInterval) : ℝ)}) = range e₁
    rw [preimage_heightOfIntervalProduct_singleton D' 1, ← range_comp]
    exact h₁
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ EuclideanThree := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨η₀, hη₀⟩ := exists_boundaryLevel_diffeomorph_of_smooth_embedding
    ι hι hemb hinj hdim' e₀ he₀ u 0 1 zero_ne_one h.smooth.continuous h.boundary_values
      (by rw [h.boundary_level_left]; exact hfib₀)
  obtain ⟨η₁, hη₁⟩ := exists_boundaryLevel_diffeomorph_of_smooth_embedding
    ι hι hemb hinj hdim' e₁ he₁ u 1 0 one_ne_zero h.smooth.continuous
      (fun w hw ↦ (h.boundary_values w hw).symm) (by rw [h.boundary_level_right]; exact hfib₁)
  exact ⟨u, h, hfib₀, hfib₁, η₀, η₁, hη₀, hη₁⟩

end Poincare.Topology.Ehresmann

import DifferentialGeometry.Geometry.Boundary.TwoSphereAnnulus
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology DifferentialGeometry.Topology.SphereSeparation

theorem exists_diffeomorph_sphere_prod_interval_of_range_subset_chart
    {E H W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    [TopologicalSpace M] [ChartedSpace EuclideanThree M]
    (hSch : smoothSchoenfliesThree)
    (ι : W → M) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3) (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁)
    (hd : Disjoint (range e₀) (range e₁))
    (φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M EuclideanThree ∞)
    (hsub : range ι ⊆ φ.source) :
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  have h₀ : range e₀ ⊆ φ.source := by
    intro x hx
    have hxB : x ∈ ι '' I.boundary W := hbdy ▸ Or.inl hx
    exact hsub (image_subset_range _ _ hxB)
  have h₁ : range e₁ ⊆ φ.source := by
    intro x hx
    have hxB : x ∈ ι '' I.boundary W := hbdy ▸ Or.inr hx
    exact hsub (image_subset_range _ _ hxB)
  have hbdy' : (φ ∘ ι) '' I.boundary W = range (φ ∘ e₀) ∪ range (φ ∘ e₁) := by
    rw [image_comp, hbdy, image_union, ← range_comp, ← range_comp]
  have hd' : Disjoint (range (φ ∘ e₀)) (range (φ ∘ e₁)) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have hab := φ.injOn (h₀ (mem_range_self a)) (h₁ (mem_range_self b)) (ha.trans hb.symm)
    exact hd.le_bot ⟨mem_range_self a, ⟨b, hab.symm⟩⟩
  exact exists_diffeomorph_sphere_prod_interval_of_two_spherical_boundaries hSch (φ ∘ ι)
    (contMDiff_comp_partialDiffeomorph φ hι hsub)
    (isEmbedding_comp_partialDiffeomorph φ hemb hsub)
    (injective_mfderiv_comp_partialDiffeomorph φ hι hinj hsub) hdim
    (φ ∘ e₀) (φ ∘ e₁) (isSmoothEmbedding_comp_partialDiffeomorph φ he₀ h₀)
    (isSmoothEmbedding_comp_partialDiffeomorph φ he₁ h₁) hbdy' hd'

end DifferentialGeometry.Geometry.Boundary

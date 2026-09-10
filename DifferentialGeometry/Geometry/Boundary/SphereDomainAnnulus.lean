import DifferentialGeometry.Geometry.Boundary.ChartAnnulus
import DifferentialGeometry.Topology.Manifold.PuncturedSphereChart

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Topology Poincare.Topology.SphereSeparation

theorem exists_diffeomorph_sphere_prod_interval_of_two_boundaries_in_sphere
    {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    (hSch : smoothSchoenfliesThree)
    (ι : W → SphereThree) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3) (e₀ e₁ : SphereTwo → SphereThree)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁)
    (hd : Disjoint (range e₀) (range e₁)) :
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ EuclideanThree := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hclosed : IsClosedEmbedding ι := hι.continuous.isClosedEmbedding hemb.injective
  have hfront : frontier (range ι) = range e₀ ∪ range e₁ :=
    (image_boundary_eq_frontier_of_fullRank_closedEmbedding ι hι hclosed hinj hdim').symm.trans hbdy
  have hproper : range ι ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := range_nonempty e₀
    have hxf : x ∈ frontier (range ι) := hfront ▸ Or.inl hx
    simp only [h, frontier_univ, mem_empty_iff_false] at hxf
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem (range ι)).mp hproper
  obtain ⟨φ, hφ, _⟩ := Poincare.Topology.Manifold.exists_smooth_punctured_sphere_chart 3 v
  apply exists_diffeomorph_sphere_prod_interval_of_range_subset_chart hSch ι hι hemb hinj hdim
    e₀ e₁ he₀ he₁ hbdy hd φ
  rw [hφ]
  intro x hx hxeq
  have hxe : x = v := hxeq
  exact hv (hxe ▸ hx)

end Poincare.Geometry.Boundary

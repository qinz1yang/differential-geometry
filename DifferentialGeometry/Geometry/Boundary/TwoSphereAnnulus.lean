import DifferentialGeometry.Topology.SphereSeparation.TwoSphereDomain
import DifferentialGeometry.Geometry.Boundary.NestedBallAnnulus
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology DifferentialGeometry.Topology.SphereSeparation

theorem exists_diffeomorph_sphere_prod_interval_of_two_spherical_boundaries
    {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    (hSch : smoothSchoenfliesThree)
    (ι : W → EuclideanThree) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3)
    (e₀ e₁ : SphereTwo → EuclideanThree)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁)
    (hd : Disjoint (range e₀) (range e₁)) :
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  have : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ EuclideanThree := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hclosed : IsClosedEmbedding ι := hι.continuous.isClosedEmbedding hemb.injective
  have hregular := closure_interior_range_of_fullRank_closedEmbedding ι hι hclosed hinj hdim'
  have hconn := isPreconnected_interior_range_of_fullRank_embedding ι hι hemb hinj hdim'
  have hfront : frontier (range ι) = range e₀ ∪ range e₁ :=
    (image_boundary_eq_frontier_of_fullRank_closedEmbedding ι hι hclosed hinj hdim').symm.trans hbdy
  obtain ⟨outer, inner, hnest, hrange⟩ := exists_nested_ball_shell_of_two_spherical_boundaries
    hSch (isCompact_range hι.continuous) hregular hconn e₀ e₁ he₀ he₁ hfront hd
  exact exists_diffeomorph_sphere_prod_interval_of_nested_balls (n := 2)
    ι hι hemb hinj hdim' outer.toPartialDiffeomorph inner.toPartialDiffeomorph zero_lt_one
    (subset_univ _) (subset_univ _) hnest hrange (Classical.arbitrary SphereTwo)

end DifferentialGeometry.Geometry.Boundary

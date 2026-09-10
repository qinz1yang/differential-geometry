import DifferentialGeometry.Geometry.Boundary.SphereDomainAnnulus
import DifferentialGeometry.Topology.Covering.EmbeddedBoundaryLift

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Topology Poincare.Topology.SphereSeparation

theorem exists_diffeomorph_sphere_prod_interval_of_spherical_cover
    {E H W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [SimplyConnectedSpace W]
    [TopologicalSpace M] [ChartedSpace EuclideanThree M]
    (hSch : smoothSchoenfliesThree)
    (p : SphereThree → M) (hp : IsCoveringMap p) (hponto : Function.Surjective p)
    (hps : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (ι : W → M) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3) (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁)
    (hd : Disjoint (range e₀) (range e₁)) :
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  let w₀ := Classical.arbitrary W
  obtain ⟨x₀, hx₀⟩ := hponto (ι w₀)
  obtain ⟨g, _, hpg, hgs, hge, hgi⟩ :=
    exists_embedded_smooth_lift_of_simplyConnected hp hps ι hι hemb hinj w₀ x₀ hx₀
  obtain ⟨f₀, f₁, hf₀, hf₁, _, _, hgbdy, hgdisj⟩ :=
    exists_two_smooth_boundary_lifts hps hemb g hpg e₀ e₁ he₀ he₁ hbdy hd
  exact exists_diffeomorph_sphere_prod_interval_of_two_boundaries_in_sphere hSch g hgs hge hgi hdim
    f₀ f₁ hf₀ hf₁ hgbdy hgdisj

end Poincare.Geometry.Boundary

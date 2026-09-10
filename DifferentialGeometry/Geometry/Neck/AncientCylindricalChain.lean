import DifferentialGeometry.Geometry.Curvature.AncientCover
import DifferentialGeometry.Geometry.Neck.CylindricalChainAnnulus
import DifferentialGeometry.Topology.Ehresmann.SphereAnnulus
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Neck

open DifferentialGeometry DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Topology Poincare.Topology.SphereSeparation Poincare.Topology.Ehresmann

theorem sphereAnnulusWithBoundaryMatching_of_ancient_cylindrical_chain
    {E H W M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [ConnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcomplete : RiemannianMetricComplete g)
    (hsplit : ancientKappaSolutionSpatialSplitting g)
    (hCG : NoncompactSpace M → cheegerGromollSoulTheorem g)
    (hSch : smoothSchoenfliesThree)
    (ι : W → M) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3) (w₀ : W)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁)
    (hboundary : Disjoint (range e₀) (range e₁))
    {n : ℕ} (e : Fin (n + 1) → OpenPartialHomeomorph (SphereTwo × ℝ) M)
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, (univ : Set SphereTwo) ×ˢ Icc (a i) (b i) ⊆ (e i).source)
    (hmeet : ∀ i : Fin n,
      (e i.castSucc '' ((univ : Set SphereTwo) ×ˢ Icc (a i.castSucc) (b i.castSucc)) ∩
        e i.succ '' ((univ : Set SphereTwo) ×ˢ Icc (a i.succ) (b i.succ))).Nonempty)
    (hd : ∀ i j, i.val + 1 < j.val → Disjoint
      (e i '' ((univ : Set SphereTwo) ×ˢ Icc (a i) (b i)))
      (e j '' ((univ : Set SphereTwo) ×ˢ Icc (a j) (b j))))
    (hcover : range ι ⊆ ⋃ i, e i '' ((univ : Set SphereTwo) ×ˢ Icc (a i) (b i))) :
    sphereAnnulusWithBoundaryMatching (I := I) ι e₀ e₁ ∧
      ∀ Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞,
        range (ι ∘ Ψ) ⊆ ⋃ i, e i '' ((univ : Set SphereTwo) ×ˢ Icc (a i) (b i)) := by
  let : LocallyPathConnectedSpace W :=
    Poincare.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let : PathConnectedSpace W := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨hfinite, hmodels⟩ := exists_standard_cover_of_ancient_spatial_splitting hcomplete hsplit hCG
  let : Finite (FundamentalGroup M (ι w₀)) := hfinite (ι w₀)
  have hann : Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
    rcases hmodels with ⟨p, hp, hs, hl⟩ | ⟨p, hp, hs, hl⟩ | ⟨U, p, hp, hs, hl⟩
    · exact exists_annulus_of_cylindrical_chain_of_euclidean_cover hSch p hp hs hl
        ι hι hemb hinj hdim w₀ e₀ e₁ he₀ he₁ hbdy hboundary e a b hab hsource hmeet hd hcover
    · exact exists_annulus_of_cylindrical_chain_of_spherical_cover hSch p hp hs hl
        ι hι hemb hinj hdim w₀ e₀ e₁ he₀ he₁ hbdy hboundary e a b hab hsource hmeet hd hcover
    · exact exists_annulus_of_cylindrical_chain_of_euclidean_open_cover hSch U p hp hs hl
        ι hι hemb hinj hdim w₀ e₀ e₁ he₀ he₁ hbdy hboundary e a b hab hsource hmeet hd hcover
  refine ⟨sphereAnnulusWithBoundaryMatching_of_product hann.some
    ι hι hemb hinj hdim e₀ e₁ he₀ he₁ hbdy, ?_⟩
  intro Ψ y hy
  obtain ⟨q, rfl⟩ := hy
  exact hcover (mem_range_self (Ψ q))

end Poincare.Geometry.Neck

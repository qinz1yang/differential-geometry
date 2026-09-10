import DifferentialGeometry.Topology.VanKampen.SphericalBoundaryChain
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Neck

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Topology

theorem simplyConnectedSpace_of_cylindrical_chain
    {E H W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PathConnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (ι : W → M) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3) (w₀ : W) [Finite (FundamentalGroup M (ι w₀))]
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
    SimplyConnectedSpace W := by
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hclosed : IsClosedEmbedding ι := hι.continuous.isClosedEmbedding hemb.injective
  have hregular := Boundary.closure_interior_range_of_fullRank_closedEmbedding ι hι hclosed hinj hdim'
  have hfront : frontier (range ι) = range e₀ ∪ range e₁ :=
    (Boundary.image_boundary_eq_frontier_of_fullRank_closedEmbedding ι hι hclosed hinj hdim').symm.trans hbdy
  have : PathConnectedSpace (range ι) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_range hι.continuous)
  have : SimplyConnectedSpace (range ι) :=
    VanKampen.simplyConnectedSpace_of_cylindrical_chain_of_two_spherical_boundaries hregular
      ⟨ι w₀, mem_range_self w₀⟩ e₀ e₁ he₀ he₁ hfront hboundary e a b hab hsource hmeet hd hcover
  exact hemb.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

end Poincare.Geometry.Neck

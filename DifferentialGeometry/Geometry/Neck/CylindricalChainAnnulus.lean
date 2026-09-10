import DifferentialGeometry.Geometry.Boundary.EuclideanCoverAnnulus
import DifferentialGeometry.Geometry.Neck.CylindricalChainSimpleConnected
import DifferentialGeometry.Geometry.Boundary.SphericalCoverAnnulus
import DifferentialGeometry.Geometry.Boundary.EuclideanOpenCoverAnnulus

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Neck

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Topology Poincare.Topology.SphereSeparation

theorem exists_annulus_of_cylindrical_chain_of_euclidean_cover
    {E H W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PathConnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    (hSch : smoothSchoenfliesThree)
    (p : EuclideanThree → M) (hp : IsCoveringMap p) (hponto : Function.Surjective p)
    (hps : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
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
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  have : SimplyConnectedSpace W := simplyConnectedSpace_of_cylindrical_chain
    ι hι hemb hinj hdim w₀ e₀ e₁ he₀ he₁ hbdy hboundary e a b hab hsource hmeet hd hcover
  exact Boundary.exists_diffeomorph_sphere_prod_interval_of_euclidean_cover hSch p hp hponto hps
    ι hι hemb hinj hdim e₀ e₁ he₀ he₁ hbdy hboundary

theorem exists_annulus_of_cylindrical_chain_of_spherical_cover
    {E H W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PathConnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    (hSch : smoothSchoenfliesThree)
    (p : SphereThree → M) (hp : IsCoveringMap p) (hponto : Function.Surjective p)
    (hps : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
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
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  have : SimplyConnectedSpace W := simplyConnectedSpace_of_cylindrical_chain
    ι hι hemb hinj hdim w₀ e₀ e₁ he₀ he₁ hbdy hboundary e a b hab hsource hmeet hd hcover
  exact Boundary.exists_diffeomorph_sphere_prod_interval_of_spherical_cover hSch p hp hponto hps
    ι hι hemb hinj hdim e₀ e₁ he₀ he₁ hbdy hboundary

theorem exists_annulus_of_cylindrical_chain_of_euclidean_open_cover
    {E H W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PathConnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    (hSch : smoothSchoenfliesThree)
    (U : TopologicalSpace.Opens EuclideanThree) (p : U → M) (hp : IsCoveringMap p) (hponto : Function.Surjective p)
    (hps : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
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
    Nonempty (Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞) := by
  have : SimplyConnectedSpace W := simplyConnectedSpace_of_cylindrical_chain
    ι hι hemb hinj hdim w₀ e₀ e₁ he₀ he₁ hbdy hboundary e a b hab hsource hmeet hd hcover
  exact Boundary.exists_diffeomorph_sphere_prod_interval_of_euclidean_open_cover hSch U p hp hponto hps
    ι hι hemb hinj hdim e₀ e₁ he₀ he₁ hbdy hboundary

end Poincare.Geometry.Neck

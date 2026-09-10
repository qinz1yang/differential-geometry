import DifferentialGeometry.Topology.VanKampen.CylindricalChainDomain
import DifferentialGeometry.Topology.VanKampen.SphereBoundaryInjection

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace Poincare.Topology.VanKampen

theorem simplyConnectedSpace_of_cylindrical_chain_of_two_spherical_boundaries
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {K : Set M} [PathConnectedSpace K] (hregular : closure (interior K) = K) (x₀ : K)
    [Finite (FundamentalGroup M x₀.val)]
    (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier K = range e₀ ∪ range e₁)
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
    (hcover : K ⊆ ⋃ i, e i '' ((univ : Set SphereTwo) ×ˢ Icc (a i) (b i))) :
    SimplyConnectedSpace K := by
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨c, hside⟩ := exists_outward_collar_of_two_spherical_boundaries
    hregular e₀ e₁ he₀ he₁ hfront hboundary
  apply simplyConnectedSpace_of_cylindrical_chain_of_boundary_collar
    (hregular ▸ isClosed_closure) x₀ c ?_ hside
    subsingleton_pathHomotopicQuotient_sum_sphereTwo e a b hab hsource hmeet hd hcover
  rw [hfront]
  rintro x (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact ⟨Sum.inl s, rfl⟩
  · exact ⟨Sum.inr s, rfl⟩

end Poincare.Topology.VanKampen

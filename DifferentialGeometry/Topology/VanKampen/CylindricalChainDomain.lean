import DifferentialGeometry.Topology.VanKampen.CylindricalChain
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection

noncomputable section

open Set

namespace DifferentialGeometry.Topology.VanKampen

theorem simplyConnectedSpace_of_cylindrical_chain_of_boundary_collar
    {S B M : Type*} [TopologicalSpace S] [CompactSpace S] [SimplyConnectedSpace S]
    [TopologicalSpace B] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    {K : Set M} [PathConnectedSpace K] (hK : IsClosed K) (x₀ : K)
    [Finite (FundamentalGroup M x₀.val)]
    {boundary : B → M} (c : ThreeManifold.TwoSidedCollar boundary)
    (hfront : frontier K ⊆ range boundary)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hB : ∀ x y : B, Subsingleton (Path.Homotopic.Quotient x y))
    {n : ℕ} (e : Fin (n + 1) → OpenPartialHomeomorph (S × ℝ) M)
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, (univ : Set S) ×ˢ Icc (a i) (b i) ⊆ (e i).source)
    (hmeet : ∀ i : Fin n,
      (e i.castSucc '' ((univ : Set S) ×ˢ Icc (a i.castSucc) (b i.castSucc)) ∩
        e i.succ '' ((univ : Set S) ×ˢ Icc (a i.succ) (b i.succ))).Nonempty)
    (hd : ∀ i j, i.val + 1 < j.val → Disjoint
      (e i '' ((univ : Set S) ×ˢ Icc (a i) (b i)))
      (e j '' ((univ : Set S) ×ˢ Icc (a j) (b j))))
    (hcover : K ⊆ ⋃ i, e i '' ((univ : Set S) ×ˢ Icc (a i) (b i))) :
    SimplyConnectedSpace K := by
  obtain ⟨U, _, hU, _, htf⟩ :=
    exists_open_torsionFree_neighborhood_of_cylindrical_chain e a b hab hsource hmeet hd
  let f : C(K, U) :=
    ⟨fun x ↦ ⟨x.val, hU (hcover x.property)⟩, continuous_subtype_val.subtype_mk _⟩
  let g := subsetToAmbient U
  let _ := htf (f x₀)
  let _ : Finite (FundamentalGroup M (g (f x₀))) :=
    inferInstanceAs (Finite (FundamentalGroup M x₀.val))
  have hinj := c.injective_fundamentalGroup_map_domain hK hfront hside hB x₀
  apply simplyConnectedSpace_of_injective_comp_through_torsion_free f g x₀
  intro p q hpq
  apply hinj
  change (Path.Homotopic.Quotient.map p f).map g =
    (Path.Homotopic.Quotient.map q f).map g at hpq
  rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp] at hpq
  exact hpq

end DifferentialGeometry.Topology.VanKampen

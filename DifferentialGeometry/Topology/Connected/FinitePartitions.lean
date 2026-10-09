import Mathlib.Topology.Connected.Clopen
open Set Function
set_option autoImplicit false

namespace DifferentialGeometry.Topology

variable {X ι κ : Type*} [TopologicalSpace X] [Finite ι] [Finite κ]

theorem connected_subset_finite_closed_partition {s : Set X} (hs : IsConnected s)
    (b : ι → Set X) (hb : ∀ i, IsClosed (b i)) (hdis : Pairwise (Disjoint on b))
    (hcover : s ⊆ ⋃ i, b i) : ∃ i, s ⊆ b i := by
  classical
  have : ConnectedSpace s := isConnected_iff_connectedSpace.mp hs
  let J := {i : ι // (s ∩ b i).Nonempty}
  let c : J → Set s := fun i => Subtype.val ⁻¹' b i.val
  have hc : ∀ i, (c i).Nonempty := by
    intro i
    obtain ⟨x, hx, hxi⟩ := i.property
    exact ⟨⟨x, hx⟩, hxi⟩
  have hd : Pairwise (Disjoint on c) := by
    intro i j hij
    exact (hdis (fun h => hij (Subtype.ext h))).preimage Subtype.val
  have hclosed : ∀ i, IsClosed (c i) := fun i => (hb i.val).preimage continuous_subtype_val
  have hu : ⋃ i, c i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover x.property)
    exact ⟨⟨i, x.val, x.property, hi⟩, hi⟩
  have : Subsingleton J := subsingleton_of_disjoint_isClosed_iUnion_eq_univ hc hd hclosed hu
  obtain ⟨x, hx⟩ := hs.nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  let i₀ : J := ⟨i, x, hx, hi⟩
  refine ⟨i, ?_⟩
  intro y hy
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hy)
  let j₀ : J := ⟨j, y, hy, hj⟩
  have heq : j = i := congrArg Subtype.val (Subsingleton.elim j₀ i₀)
  simpa [heq] using hj

theorem finite_connected_partitions_equiv (a : ι → Set X) (b : κ → Set X)
    (ha : ∀ i, IsConnected (a i)) (hb : ∀ j, IsConnected (b j))
    (hca : ∀ i, IsClosed (a i)) (hcb : ∀ j, IsClosed (b j))
    (hda : Pairwise (Disjoint on a)) (hdb : Pairwise (Disjoint on b))
    (hcover : ⋃ i, a i = ⋃ j, b j) : ∃ e : ι ≃ κ, ∀ i, a i = b (e i) := by
  classical
  have hab : ∀ i, ∃ j, a i ⊆ b j := by
    intro i
    apply connected_subset_finite_closed_partition (ha i) b hcb hdb
    rw [← hcover]
    exact subset_iUnion a i
  have hba : ∀ j, ∃ i, b j ⊆ a i := by
    intro j
    apply connected_subset_finite_closed_partition (hb j) a hca hda
    rw [hcover]
    exact subset_iUnion b j
  choose f hf using hab
  choose g hg using hba
  have hgf : ∀ i, g (f i) = i := by
    intro i
    by_contra h
    obtain ⟨x, hx⟩ := (ha i).nonempty
    exact (Set.disjoint_left.mp (hda h)) (hg (f i) (hf i hx)) hx
  have hfg : ∀ j, f (g j) = j := by
    intro j
    by_contra h
    obtain ⟨x, hx⟩ := (hb j).nonempty
    exact (Set.disjoint_left.mp (hdb h)) (hf (g j) (hg j hx)) hx
  refine ⟨⟨f, g, hgf, hfg⟩, ?_⟩
  intro i
  change a i = b (f i)
  exact subset_antisymm (hf i) (by simpa only [hgf i] using hg (f i))

end DifferentialGeometry.Topology

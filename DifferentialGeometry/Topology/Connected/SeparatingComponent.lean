import DifferentialGeometry.Topology.Connected.PhragmenBrouwer

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X] [LocallyConnectedSpace X]

theorem exists_separates_of_finite_iUnion
    (hpath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    {ι : Type*} [Finite ι] (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) {H K : Set X}
    (hH : IsConnected H) (hK : IsConnected K) (h : Separates (⋃ i, C i) H K) :
    ∃ i, Separates (C i) H K := by
  classical
  let _ := Fintype.ofFinite ι
  have aux (s : Finset ι) : Separates (⋃ i ∈ s, C i) H K →
      ∃ i ∈ s, Separates (C i) H K := by
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      obtain ⟨x, hx⟩ := hH.nonempty
      obtain ⟨y, hy⟩ := hK.nonempty
      have hs' : Separates ∅ H K := by simpa using hs
      exact False.elim (hs'.not_mem_connectedComponentIn hx hy (by
        simp [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]))
    | @insert i s hi ih =>
      intro hs
      rw [Finset.set_biUnion_insert] at hs
      have hsclosed : IsClosed (⋃ j ∈ s, C j) := isClosed_biUnion_finset fun j _ => hC j
      have hdis : Disjoint (C i) (⋃ j ∈ s, C j) := by
        apply disjoint_iUnion_right.mpr
        intro j
        apply disjoint_iUnion_right.mpr
        intro hj
        exact hd (fun heq => hi (heq ▸ hj))
      rcases separates_or_separates_of_union hpath (hC i) hsclosed hdis
        hH.isPreconnected hK.isPreconnected hs with hsep | hsep
      · exact ⟨i, Finset.mem_insert_self _ _, hsep⟩
      · obtain ⟨j, hj, hsep⟩ := ih hsep
        exact ⟨j, Finset.mem_insert_of_mem hj, hsep⟩
  obtain ⟨i, _, hi⟩ := aux Finset.univ (by simpa using h)
  exact ⟨i, hi⟩

theorem exists_separating_connectedComponentIn
    (hpath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    {C H K : Set X} [Finite (ConnectedComponents C)] (hC : IsClosed C)
    (hH : IsConnected H) (hK : IsConnected K) (h : Separates C H K) :
    ∃ x ∈ C, Separates (connectedComponentIn C x) H K := by
  classical
  let p : ConnectedComponents C → C := fun c => ConnectedComponents.surjective_coe c |>.choose
  have hp : ∀ c, ConnectedComponents.mk (p c) = c :=
    fun c => (ConnectedComponents.surjective_coe c).choose_spec
  let A : ConnectedComponents C → Set X := fun c => Subtype.val '' connectedComponent (p c)
  have hA : ∀ c, IsClosed (A c) := fun _ =>
    hC.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hd : Pairwise (fun c d => Disjoint (A c) (A d)) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have heq : w = z := Subtype.ext hzw
    subst w
    have hcomp := (connectedComponent_eq hz).trans (connectedComponent_eq hw).symm
    have hclass := ConnectedComponents.coe_eq_coe.mpr hcomp
    exact hcd ((hp c).symm.trans (hclass.trans (hp d)))
  have hcover : ⋃ c, A c = C := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨c, rfl⟩, z, _, rfl⟩
      exact z.property
    · intro x hx
      let z : C := ⟨x, hx⟩
      have hz : z ∈ connectedComponent (p (ConnectedComponents.mk z)) :=
        ConnectedComponents.coe_eq_coe'.mp (hp (ConnectedComponents.mk z)).symm
      exact mem_iUnion.mpr ⟨ConnectedComponents.mk z, z, hz, rfl⟩
  obtain ⟨c, hc⟩ := exists_separates_of_finite_iUnion hpath A hA hd hH hK (hcover.symm ▸ h)
  refine ⟨(p c).val, (p c).property, ?_⟩
  rwa [connectedComponentIn_eq_image (p c).property]

omit [LocallyConnectedSpace X] in
theorem exists_separating_component [LocallyPathConnectedSpace X]
    {C H K : Set X} [Finite (ConnectedComponents C)] (hC : IsClosed C)
    (hH : IsConnected H) (hK : IsConnected K) (h : Separates C H K) :
    ∃ x ∈ C, Separates (connectedComponentIn C x) H K :=
  exists_separating_connectedComponentIn (fun _ hU hc => hU.isConnected_iff_isPathConnected.mp hc)
    hC hH hK h

end DifferentialGeometry.Topology

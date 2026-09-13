import DifferentialGeometry.Topology.Attachment.BoundaryGluing
import DifferentialGeometry.Topology.Combinatorics.OrderedSpanningTree

noncomputable section

open Set Function Topology

namespace DifferentialGeometry.Topology

namespace BoundaryGluing

variable {X : Type*} {ι : Type*} [TopologicalSpace X] [Finite ι]

theorem rel_restrict_union_iff (G : BoundaryGluing X ι) (s t : Set ι) (x y : X) :
    (G.restrict (s ∪ t)).rel x y ↔ (G.restrict s).rel x y ∨ (G.restrict t).rel x y := by
  rw [rel_restrict_iff, rel_restrict_iff, rel_restrict_iff]
  constructor
  · rintro (h | ⟨i, hx, hy⟩)
    · exact Or.inl (Or.inl h)
    · rcases i.2 with hs | ht
      · exact Or.inl (Or.inr ⟨⟨i.1, hs⟩, hx, hy⟩)
      · exact Or.inr (Or.inr ⟨⟨i.1, ht⟩, hx, hy⟩)
  · rintro (h | h)
    · rcases h with h | ⟨i, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨i.1, Or.inl i.2⟩, hx, hy⟩
    · rcases h with h | ⟨i, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨i.1, Or.inr i.2⟩, hx, hy⟩

theorem setoid_restrict_mono (G : BoundaryGluing X ι) {s t : Set ι} (h : s ⊆ t) :
    (G.restrict s).setoid ≤ (G.restrict t).setoid := by
  intro x y hxy
  change (G.restrict s).rel x y at hxy
  change (G.restrict t).rel x y
  rw [rel_restrict_iff] at hxy
  rcases hxy with hxy | ⟨i, hx, hy⟩
  · exact Or.inl hxy
  · exact Or.inr ⟨⟨i.1, h i.2⟩, hx, hy⟩

theorem setoid_restrict_union (G : BoundaryGluing X ι) (s t : Set ι) :
    (G.restrict (s ∪ t)).setoid = (G.restrict s).setoid ⊔ (G.restrict t).setoid := by
  have hleft : (G.restrict s).setoid ≤ (G.restrict s).setoid ⊔ (G.restrict t).setoid :=
    le_sup_left
  have hright : (G.restrict t).setoid ≤ (G.restrict s).setoid ⊔ (G.restrict t).setoid :=
    le_sup_right
  apply le_antisymm
  · intro x y hxy
    change (G.restrict (s ∪ t)).rel x y at hxy
    rw [rel_restrict_iff] at hxy
    rcases hxy with hxy | ⟨i, hx, hy⟩
    · exact hleft (Or.inl hxy)
    · rcases i.2 with hs | ht
      · exact hleft (Or.inr ⟨⟨i.1, hs⟩, hx, hy⟩)
      · exact hright (Or.inr ⟨⟨i.1, ht⟩, hx, hy⟩)
  · exact sup_le (G.setoid_restrict_mono Set.subset_union_left)
      (G.setoid_restrict_mono Set.subset_union_right)

theorem rel_restrict_insert_iff (G : BoundaryGluing X ι) (s : Set ι) (i : ι) (x y : X) :
    (G.restrict (insert i s)).rel x y ↔ (G.restrict s).rel x y ∨ (G.restrict {i}).rel x y := by
  have h : insert i s = s ∪ ({i} : Set ι) := by
    rw [Set.insert_eq, Set.union_comm]
  rw [h, G.rel_restrict_union_iff]

theorem setoid_restrict_insert (G : BoundaryGluing X ι) (s : Set ι) (i : ι) :
    (G.restrict (insert i s)).setoid =
      (G.restrict s).setoid ⊔ (G.restrict ({i} : Set ι)).setoid := by
  have h : insert i s = s ∪ ({i} : Set ι) := by
    rw [Set.insert_eq, Set.union_comm]
  rw [h, G.setoid_restrict_union]

theorem setoid_restrict_finset (G : BoundaryGluing X ι) (s : Finset ι) :
    (G.restrict (s : Set ι)).setoid = s.sup (fun i => (G.restrict ({i} : Set ι)).setoid) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.coe_empty, Finset.sup_empty]
      exact G.setoid_restrict_empty
  | insert i s _ ih =>
      rw [Finset.coe_insert, Finset.sup_insert, G.setoid_restrict_insert, ih, sup_comm]

section

variable [DecidableEq ι]

theorem setoid_restrict_list (G : BoundaryGluing X ι) (L : List ι) :
    (G.restrict (L.toFinset : Set ι)).setoid =
      L.toFinset.sup (fun i => (G.restrict ({i} : Set ι)).setoid) :=
  G.setoid_restrict_finset L.toFinset

theorem setoid_restrict_append_singleton (G : BoundaryGluing X ι) (L : List ι) (i : ι) :
    (G.restrict ((L ++ [i]).toFinset : Set ι)).setoid =
      (G.restrict (L.toFinset : Set ι)).setoid ⊔ (G.restrict ({i} : Set ι)).setoid := by
  have hfin : (L ++ [i]).toFinset = insert i L.toFinset := by
    rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
    tauto
  rw [hfin, Finset.coe_insert, G.setoid_restrict_insert]

theorem setoid_restrict_take_succ (G : BoundaryGluing X ι) (L : List ι) (k : ℕ)
    (hk : k < L.length) :
    (G.restrict ((L.take (k + 1)).toFinset : Set ι)).setoid =
      (G.restrict ((L.take k).toFinset : Set ι)).setoid ⊔
        (G.restrict ({L[k]} : Set ι)).setoid := by
  rw [← List.take_concat_get' L k hk]
  exact G.setoid_restrict_append_singleton (L.take k) L[k]

theorem foldl_sup_eq_restrict_list (G : BoundaryGluing X ι) (s : Set ι) (L : List ι) :
    L.foldl (fun acc i => acc ⊔ (G.restrict ({i} : Set ι)).setoid)
        (G.restrict s).setoid =
      (G.restrict (s ∪ (L.toFinset : Set ι))).setoid := by
  induction L generalizing s with
  | nil =>
      rw [List.foldl_nil, List.toFinset_nil, Finset.coe_empty, Set.union_empty]
  | cons i L ih =>
      have hset : (s ∪ ({i} : Set ι)) ∪ (L.toFinset : Set ι) =
          s ∪ ((i :: L).toFinset : Set ι) := by
        rw [List.toFinset_cons, Finset.coe_insert]
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff]
        tauto
      rw [List.foldl_cons, ← G.setoid_restrict_union s ({i} : Set ι),
        ih (s ∪ ({i} : Set ι)), hset]

end

variable (G : BoundaryGluing X ι) (s : Set ι) (i : ι)

def stepSetoid : Setoid (Quotient (G.restrict s).setoid) :=
  Setoid.ker (Quot.mapRight (G.setoid_restrict_mono (Set.subset_insert i s)))

def stepMap : Quotient (G.restrict s).setoid → Quotient (G.restrict (insert i s)).setoid :=
  Quot.mapRight (G.setoid_restrict_mono (Set.subset_insert i s))

theorem stepMap_mk (x : X) :
    G.stepMap s i (Quotient.mk'' x) =
      (Quotient.mk'' x : Quotient (G.restrict (insert i s)).setoid) := rfl

theorem continuous_stepMap : Continuous (G.stepMap s i) :=
  continuous_quot_map (G.setoid_restrict_mono (Set.subset_insert i s)) continuous_id

theorem stepSetoid_iff (a b : Quotient (G.restrict s).setoid) :
    G.stepSetoid s i a b ↔ a = b ∨ ∃ x : X, x ∈ G.block i ∧
      Quotient.mk'' x = a ∧ Quotient.mk'' (G.flip i x) = b := by
  constructor
  · intro hab
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        have hxy : (G.restrict (insert i s)).rel x y := by
          have h : (Quotient.mk'' x : Quotient (G.restrict (insert i s)).setoid) =
              Quotient.mk'' y := hab
          have h' := Quotient.exact h
          change (G.restrict (insert i s)).rel x y at h'
          exact h'
        rcases (G.rel_restrict_insert_iff s i x y).mp hxy with hxy' | hxy'
        · exact Or.inl (Quotient.sound' hxy')
        · rcases hxy' with hxy' | ⟨j, hxj, hyj⟩
          · exact Or.inl (by rw [hxy'])
          · have hji : (j : ι) = i := Set.mem_singleton_iff.mp j.2
            have hflip : (G.restrict ({i} : Set ι)).flip j = G.flip i := by
              change G.flip (j : ι) = G.flip i
              rw [hji]
            refine Or.inr ⟨x, ?_, rfl, ?_⟩
            · rw [← hji]
              exact hxj
            · rw [hyj, hflip]
  · rintro (h | ⟨x, hx, rfl, hb⟩)
    · rw [h]
    · rw [← hb]
      have hrel : (G.restrict ({i} : Set ι)).rel x (G.flip i x) :=
        Or.inr ⟨⟨i, Set.mem_singleton i⟩, hx, rfl⟩
      exact Quotient.sound' ((G.rel_restrict_insert_iff s i x (G.flip i x)).mpr (Or.inr hrel))

def stepQuotientHomeomorph :
    Quotient (G.stepSetoid s i) ≃ₜ Quotient (G.restrict (insert i s)).setoid :=
  quotientQuotientHomeomorph (G.setoid_restrict_mono (Set.subset_insert i s))

theorem stepSetoid_iff_block (a b : Quotient (G.restrict s).setoid) :
    G.stepSetoid s i a b ↔
      Relation.Map (G.restrict ({i} : Set ι)).rel
        (Quotient.mk'' : X → Quotient (G.restrict s).setoid)
        (Quotient.mk'' : X → Quotient (G.restrict s).setoid) a b := by
  rw [G.stepSetoid_iff]
  constructor
  · rintro (rfl | ⟨x, hx, hxa, hxb⟩)
    · obtain ⟨x, hx⟩ := Quotient.exists_rep a
      subst hx
      exact ⟨x, x, Or.inl rfl, rfl, rfl⟩
    · exact ⟨x, G.flip i x, Or.inr ⟨⟨i, Set.mem_singleton i⟩, hx, rfl⟩, hxa, hxb⟩
  · rintro ⟨x, y, hxy, hx, hy⟩
    rcases hxy with hxy | ⟨j, hxj, hyj⟩
    · exact Or.inl (by rw [← hx, ← hy, hxy])
    · have hji : (j : ι) = i := Set.mem_singleton_iff.mp j.2
      have hflip : (G.restrict ({i} : Set ι)).flip j = G.flip i := by
        change G.flip (j : ι) = G.flip i
        rw [hji]
      refine Or.inr ⟨x, ?_, hx, ?_⟩
      · rw [← hji]
        exact hxj
      · rw [← hy, hyj, hflip]

def quotientHomeomorph_restrict_empty :
    Quotient (G.restrict (∅ : Set ι)).setoid ≃ₜ X :=
  (Homeomorph.Quotient.congrRight (fun x y => by
    rw [G.setoid_restrict_empty])).trans Homeomorph.quotientBot

end BoundaryGluing

namespace SimpleGraph

theorem exists_ordered_edgeList {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) :
    ∃ (L : List G.edgeSet) (W : List V) (root : V),
      W.Nodup ∧ L.length = W.length ∧ root ∉ W.toFinset ∧
      insert root W.toFinset = Finset.univ ∧
      (∀ (k : ℕ) (hk : k < W.length),
        ∃ y ∈ insert root (W.take k).toFinset,
          (L.map Subtype.val)[k]? = some (s(y, W.get ⟨k, hk⟩)) ∧ G.Adj y (W.get ⟨k, hk⟩)) ∧
      L.length + 1 = Fintype.card V := by
  classical
  let root : V := Classical.choice hG.nonempty
  obtain ⟨W, E, hWn, hElen, hroot, hcov, hstep⟩ :=
    SimpleGraph.exists_rooted_orderedSpanningTree G hG root
  have hsub : ∀ e ∈ E, e ∈ G.edgeSet := by
    intro e he
    obtain ⟨k, rfl⟩ := List.get_of_mem he
    have hk : (k : ℕ) < W.length := by rw [← hElen]; exact k.isLt
    obtain ⟨y, -, hget, hadj⟩ := hstep (k : ℕ) hk
    have hEq : E.get k = s(y, W.get ⟨(k : ℕ), hk⟩) := by
      obtain ⟨_, hget'⟩ := List.getElem?_eq_some_iff.mp hget
      simpa [List.get_eq_getElem] using hget'
    rw [hEq]
    rw [SimpleGraph.mem_edgeSet]
    exact hadj
  let L : List G.edgeSet := E.attach.map fun x => ⟨x.1, hsub x.1 x.2⟩
  have hLval : L.map Subtype.val = E := by
    simp only [L, List.map_map, Function.comp_def]
    exact List.attach_map_subtype_val E
  have hcardV : Fintype.card V = W.length + 1 := by
    rw [← Finset.card_univ, ← hcov, Finset.card_insert_of_notMem hroot,
      List.toFinset_card_of_nodup hWn]
  have hLlen : L.length = E.length := by
    rw [← List.length_map (f := Subtype.val), hLval]
  refine ⟨L, W, root, hWn, ?_, hroot, hcov, ?_, ?_⟩
  · rw [hLlen, hElen]
  · intro k hk
    obtain ⟨y, hy, hget, hadj⟩ := hstep k hk
    refine ⟨y, hy, ?_, hadj⟩
    rw [hLval]
    exact hget
  · rw [hLlen, hElen, hcardV]

end SimpleGraph

namespace BoundaryGluing

theorem exists_foldl_sup_eq_restrict_of_spanningTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected)
    {X : Type*} [TopologicalSpace X] (B : BoundaryGluing X G.edgeSet) :
    ∃ (L : List G.edgeSet) (W : List V) (root : V),
      W.Nodup ∧ L.length = W.length ∧ root ∉ W.toFinset ∧
      insert root W.toFinset = Finset.univ ∧
      (∀ (k : ℕ) (hk : k < W.length),
        ∃ y ∈ insert root (W.take k).toFinset,
          (L.map Subtype.val)[k]? = some (s(y, W.get ⟨k, hk⟩)) ∧ G.Adj y (W.get ⟨k, hk⟩)) ∧
      L.length + 1 = Fintype.card V ∧
      L.foldl (fun acc i => acc ⊔ (B.restrict ({i} : Set G.edgeSet)).setoid) ⊥ =
        (B.restrict (L.toFinset : Set G.edgeSet)).setoid := by
  obtain ⟨L, W, root, h1, h2, h3, h4, h5, h6⟩ := SimpleGraph.exists_ordered_edgeList G hG
  refine ⟨L, W, root, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [← B.setoid_restrict_empty]
  have h := B.foldl_sup_eq_restrict_list (∅ : Set G.edgeSet) L
  rw [Set.empty_union] at h
  exact h

end BoundaryGluing

end DifferentialGeometry.Topology

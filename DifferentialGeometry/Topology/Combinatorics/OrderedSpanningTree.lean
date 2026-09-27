import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

namespace DifferentialGeometry.Topology

namespace SimpleGraph

private lemma exists_lt_of_mem_take {V : Type*} {l : List V} {k : ℕ} {y : V}
    (hy : y ∈ l.take k) : ∃ j : Fin l.length, (j : ℕ) < k ∧ l.get j = y := by
  obtain ⟨j, hj, hjget⟩ := List.mem_take_iff_getElem.mp hy
  exact ⟨⟨j, lt_of_lt_of_le hj (Nat.min_le_right _ _)⟩,
    lt_of_lt_of_le hj (Nat.min_le_left _ _), by simpa [List.get_eq_getElem] using hjget⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem exists_expansion (G : SimpleGraph V) (hG : G.Connected) :
    ∀ N : ℕ, ∀ S : Finset V, (Finset.univ \ S).card ≤ N → S.Nonempty →
      ∃ (W : List V) (E : List (Sym2 V)),
        W.Nodup ∧ E.length = W.length ∧
          Disjoint W.toFinset S ∧ S ∪ W.toFinset = Finset.univ ∧
          ∀ (k : ℕ) (hk : k < W.length),
            ∃ y ∈ S ∪ (W.take k).toFinset,
              E[k]? = some (s(y, W.get ⟨k, hk⟩)) ∧ G.Adj y (W.get ⟨k, hk⟩) := by
  classical
  intro N
  induction N with
  | zero =>
      intro S hN hS
      have hSU : S = Finset.univ := by
        by_contra hne
        obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
          by_contra h
          exact hne (Finset.eq_univ_iff_forall.mpr fun x => by
            simpa using not_exists.mp h x)
        have hmem : x ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
        have hpos : 0 < (Finset.univ \ S).card := Finset.card_pos.mpr ⟨x, hmem⟩
        omega
      exact ⟨[], [], by simp, by simp, by simp [hSU], by simp [hSU], by simp⟩
  | succ N ih =>
      intro S hN hS
      by_cases hSU : S = Finset.univ
      · exact ⟨[], [], by simp, by simp, by simp [hSU], by simp [hSU], by simp⟩
      · obtain ⟨x, hxS⟩ : ∃ x, x ∉ S := by
          by_contra h
          exact hSU (Finset.eq_univ_iff_forall.mpr fun x => by
            simpa using not_exists.mp h x)
        obtain ⟨s, hsS⟩ := hS
        obtain ⟨p⟩ := hG s x
        have hex : ∃ i, i ≤ p.length ∧ p.getVert i ∉ S :=
          ⟨p.length, le_rfl, by rw [p.getVert_length]; exact hxS⟩
        let i := Nat.find hex
        have hi_le : i ≤ p.length := (Nat.find_spec hex).1
        have hi_not : p.getVert i ∉ S := (Nat.find_spec hex).2
        have hi_pos : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h | h
          · rw [h, p.getVert_zero] at hi_not
            exact absurd hsS hi_not
          · exact h
        have hprev : p.getVert (i - 1) ∈ S := by
          by_contra hc
          exact Nat.find_min hex (by omega) ⟨by omega, hc⟩
        have hadj : G.Adj (p.getVert (i - 1)) (p.getVert i) := by
          have h := p.adj_getVert_succ (i := i - 1) (by omega)
          have h' : i - 1 + 1 = i := by omega
          rwa [h'] at h
        have hcard : (Finset.univ \ insert (p.getVert i) S).card ≤ N := by
          rw [Finset.sdiff_insert, Finset.card_erase_of_mem]
          · omega
          · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi_not⟩
        obtain ⟨W', E', hWn', hlen', hdisj', hcov', hstep'⟩ :=
          ih (insert (p.getVert i) S) hcard ⟨p.getVert i, Finset.mem_insert_self _ _⟩
        have hx'W : p.getVert i ∉ W' := by
          intro hmem
          exact Finset.disjoint_left.mp hdisj' (List.mem_toFinset.mpr hmem)
            (Finset.mem_insert_self _ _)
        refine ⟨p.getVert i :: W', s(p.getVert (i - 1), p.getVert i) :: E',
          ?_, ?_, ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨hx'W, hWn'⟩
        · simp [hlen']
        · rw [List.toFinset_cons, Finset.disjoint_insert_left]
          exact ⟨hi_not, Finset.disjoint_left.mpr fun z hzW hzS =>
            Finset.disjoint_left.mp hdisj' hzW (Finset.mem_insert_of_mem hzS)⟩
        · have hcov'' : insert (p.getVert i) (S ∪ W'.toFinset) = Finset.univ := by
            rw [← Finset.insert_union]
            exact hcov'
          rw [List.toFinset_cons, Finset.union_insert]
          exact hcov''
        · intro k hk
          rcases k with _ | k
          · exact ⟨p.getVert (i - 1), Finset.mem_union_left _ hprev, by simp, hadj⟩
          · have hkW : k < W'.length := by
              simp only [List.length_cons] at hk
              omega
            obtain ⟨y, hy, hget, hadj'⟩ := hstep' k hkW
            refine ⟨y, ?_, ?_, ?_⟩
            · have hy' : y ∈ insert (p.getVert i) (S ∪ (W'.take k).toFinset) := by
                rw [← Finset.insert_union]
                exact hy
              rw [List.take_succ_cons, List.toFinset_cons, Finset.union_insert]
              exact hy'
            · simpa only [List.getElem?_cons_succ, List.get_cons_succ] using hget
            · simpa only [List.get_cons_succ] using hadj'

theorem exists_rooted_orderedSpanningTree (G : SimpleGraph V) (hG : G.Connected) (root : V) :
    ∃ (W : List V) (E : List (Sym2 V)),
      W.Nodup ∧ E.length = W.length ∧ root ∉ W.toFinset ∧
        insert root W.toFinset = Finset.univ ∧
        ∀ (k : ℕ) (hk : k < W.length),
          ∃ y ∈ insert root (W.take k).toFinset,
            E[k]? = some (s(y, W.get ⟨k, hk⟩)) ∧ G.Adj y (W.get ⟨k, hk⟩) := by
  obtain ⟨W, E, hW, hlen, hdisj, hcov, hstep⟩ :=
    exists_expansion G hG (Finset.univ \ {root}).card {root} le_rfl
      (Finset.singleton_nonempty root)
  refine ⟨W, E, hW, hlen, ?_, ?_, ?_⟩
  · intro hmem
    exact Finset.disjoint_left.mp hdisj hmem (Finset.mem_singleton_self root)
  · rw [← Finset.singleton_union]
    exact hcov
  · intro k hk
    obtain ⟨y, hy, hstepk⟩ := hstep k hk
    rw [Finset.singleton_union] at hy
    exact ⟨y, hy, hstepk⟩

theorem exists_spanningTree_edgeSet {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hG : G.Connected) :
    ∃ T : Set (Sym2 V), T ⊆ G.edgeSet ∧ T.Finite ∧ T.ncard + 1 = Fintype.card V ∧
      (Fintype.card G.edgeSet - T.ncard) + Fintype.card V = Fintype.card G.edgeSet + 1 ∧
      (SimpleGraph.fromEdgeSet T).IsTree := by
  classical
  let root := Classical.choice hG.nonempty
  obtain ⟨W, E, hW, hlen, hroot, hcov, hstep⟩ :=
    exists_rooted_orderedSpanningTree G hG root
  set T : Set (Sym2 V) := (E.toFinset : Set (Sym2 V)) with hT
  have hTcard : T.ncard = E.toFinset.card := by
    rw [hT]
    exact Set.ncard_coe_finset E.toFinset
  have hsub : ∀ e ∈ E.toFinset, e ∈ G.edgeSet := by
    intro e he
    obtain ⟨k, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp he)
    have hk : (k : ℕ) < W.length := by
      rw [← hlen]
      exact k.isLt
    obtain ⟨y, -, hget, hadj⟩ := hstep (k : ℕ) hk
    have hEq : E.get k = s(y, W.get ⟨(k : ℕ), hk⟩) := by
      obtain ⟨_, hget'⟩ := List.getElem?_eq_some_iff.mp hget
      simpa [List.get_eq_getElem] using hget'
    rw [hEq, SimpleGraph.mem_edgeSet]
    exact hadj
  have hcardV : Nat.card V = W.length + 1 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hcov,
      Finset.card_insert_of_notMem hroot, List.toFinset_card_of_nodup hW]
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet T
  have hAdjH : ∀ {a b : V}, s(a, b) ∈ E.toFinset → H.Adj a b := by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨hab, ((SimpleGraph.mem_edgeSet G).mp (hsub (s(a, b)) hab)).ne⟩
  have hreach : ∀ (k : ℕ) (hk : k < W.length), H.Reachable root (W.get ⟨k, hk⟩) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro hk
        obtain ⟨y, hy, hget, hadj⟩ := hstep k hk
        have hzy : s(y, W.get ⟨k, hk⟩) ∈ E.toFinset := by
          have hkE : k < E.length := by rw [hlen]; exact hk
          have hEq : E.get ⟨k, hkE⟩ = s(y, W.get ⟨k, hk⟩) := by
            obtain ⟨_, hget'⟩ := List.getElem?_eq_some_iff.mp hget
            simpa [List.get_eq_getElem] using hget'
          have hmem : E.get ⟨k, hkE⟩ ∈ E := by
            rw [List.get_eq_getElem]
            exact List.getElem_mem hkE
          rw [← hEq]
          exact List.mem_toFinset.mpr hmem
        have hAdjHy : H.Adj y (W.get ⟨k, hk⟩) := hAdjH hzy
        rcases Finset.mem_insert.mp hy with rfl | hyW
        · exact hAdjHy.reachable
        · obtain ⟨j, hjk, hjget⟩ := exists_lt_of_mem_take (List.mem_toFinset.mp hyW)
          have hrec : H.Reachable root (W.get j) := ih (j : ℕ) hjk j.isLt
          exact hrec.trans (by rw [hjget]; exact hAdjHy.reachable)
  have hreachAll : ∀ w : V, H.Reachable root w := by
    intro w
    rcases eq_or_ne w root with rfl | hwne
    · exact SimpleGraph.Reachable.rfl
    · have hw : w ∈ W.toFinset := by
        rcases Finset.mem_insert.mp (hcov ▸ Finset.mem_univ w) with h | h
        · exact absurd h hwne
        · exact h
      obtain ⟨k, hkget⟩ := List.get_of_mem (List.mem_toFinset.mp hw)
      rw [← hkget]
      exact hreach (k : ℕ) k.isLt
  have hconn : H.Connected := by
    exact (SimpleGraph.connected_iff_exists_forall_reachable H).mpr ⟨root, hreachAll⟩
  have hle1 : Nat.card V ≤ Nat.card (↥H.edgeSet) + 1 := hconn.card_vert_le_card_edgeSet_add_one
  have hcardEset : Nat.card (↥(E.toFinset : Set (Sym2 V))) = E.toFinset.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hle2 : Nat.card (↥H.edgeSet) ≤ E.toFinset.card := by
    have hset : H.edgeSet ⊆ (E.toFinset : Set (Sym2 V)) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact Set.sdiff_subset
    have h := Nat.card_le_card_of_injective (Set.inclusion hset) (Set.inclusion_injective hset)
    rwa [hcardEset] at h
  have hle3 : E.toFinset.card ≤ E.length := List.toFinset_card_le E
  have hcardE : E.toFinset.card = E.length := by
    have h1 : W.length + 1 ≤ E.toFinset.card + 1 := by
      calc W.length + 1 = Nat.card V := hcardV.symm
        _ ≤ Nat.card (↥H.edgeSet) + 1 := hle1
        _ ≤ E.toFinset.card + 1 := Nat.add_le_add_right hle2 1
    omega
  have hedge : Nat.card (↥H.edgeSet) = E.toFinset.card := by
    have hset : H.edgeSet = (E.toFinset : Set (Sym2 V)) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      exact ⟨fun he => (Set.mem_sdiff e).mp he |>.1,
        fun he => Set.mem_sdiff e |>.mpr ⟨he, fun hdiag =>
          SimpleGraph.not_isDiag_of_mem_edgeSet G (hsub e he) hdiag⟩⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hcardGE : E.toFinset.card ≤ Nat.card (↥G.edgeSet) := by
    have hset : (E.toFinset : Set (Sym2 V)) ⊆ G.edgeSet := fun e he => hsub e he
    have h := Nat.card_le_card_of_injective (Set.inclusion hset) (Set.inclusion_injective hset)
    rwa [hcardEset] at h
  have htree : H.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    exact ⟨hconn, by rw [hedge, hcardE, hlen, hcardV]⟩
  refine ⟨T, ?_, ?_, ?_, ?_, htree⟩
  · rw [hT]
    exact fun e he => hsub e he
  · rw [hT]
    exact E.toFinset.finite_toSet
  · rw [hTcard, hcardE, hlen, ← Nat.card_eq_fintype_card, hcardV]
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hTcard, hcardE, hlen, hcardV]
    omega

end SimpleGraph

end DifferentialGeometry.Topology

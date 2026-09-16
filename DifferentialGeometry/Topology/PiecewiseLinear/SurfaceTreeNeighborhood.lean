import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def embeddedVertexFace {K : Geometry.SimplicialComplex ℝ E}
    {V : Type*} (f : V → K.vertices) (v : V) : Finset E :=
  {(f v : E)}

open Classical in
noncomputable def embeddedEdgeFace {K : Geometry.SimplicialComplex ℝ E}
    {V : Type*} (f : V → K.vertices) (u v : V) : Finset E :=
  {(f u : E), (f v : E)}

open Classical in
noncomputable def embeddedGraphDerivedNeighborhood
    (K : Geometry.SimplicialComplex ℝ E) {V : Type*}
    (G : SimpleGraph V) (f : V → K.vertices) : Set E :=
  (⋃ v, (derivedNeighborhoodCell K (embeddedVertexFace f v)).space) ∪
    ⋃ p : {p : V × V // G.Adj p.1 p.2},
      (derivedNeighborhoodCell K (embeddedEdgeFace f p.1.1 p.1.2)).space

open Classical in
theorem mem_embeddedGraphDerivedNeighborhood_iff
    {K : Geometry.SimplicialComplex ℝ E} {V : Type*}
    {G : SimpleGraph V} {f : V → K.vertices} {x : E} :
    x ∈ embeddedGraphDerivedNeighborhood K G f ↔
      (∃ v, x ∈ (derivedNeighborhoodCell K (embeddedVertexFace f v)).space) ∨
      ∃ u v, G.Adj u v ∧
        x ∈ (derivedNeighborhoodCell K (embeddedEdgeFace f u v)).space := by
  constructor
  · rintro (hx | hx)
    · obtain ⟨v, hxv⟩ := mem_iUnion.mp hx
      exact Or.inl ⟨v, hxv⟩
    · obtain ⟨p, hxp⟩ := mem_iUnion.mp hx
      exact Or.inr ⟨p.1.1, p.1.2, p.2, hxp⟩
  · rintro (⟨v, hxv⟩ | ⟨u, v, huv, hx⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨v, hxv⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨(u, v), huv⟩, hx⟩)

open Classical in
theorem embeddedGraphDerivedNeighborhood_subset
    (K : Geometry.SimplicialComplex ℝ E) {V : Type*}
    (G : SimpleGraph V) (f : V → K.vertices) :
    embeddedGraphDerivedNeighborhood K G f ⊆ K.space := by
  intro x hx
  rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hx with ⟨v, hxv⟩ | ⟨u, v, -, huv⟩
  · exact derivedNeighborhoodCell_space_subset K (embeddedVertexFace f v) hxv
  · exact derivedNeighborhoodCell_space_subset K (embeddedEdgeFace f u v) huv

open Classical in
theorem embeddedVertexFace_mem
    {K : Geometry.SimplicialComplex ℝ E} {V : Type*}
    (f : V → K.vertices) (v : V) : embeddedVertexFace f v ∈ K.faces :=
  (f v).2

open Classical in
theorem embeddedEdgeFace_mem
    {K : Geometry.SimplicialComplex ℝ E} {V : Type*}
    {G : SimpleGraph V} {f : V → K.vertices}
    (hmap : ∀ ⦃u v⦄, G.Adj u v → (SimplicialComplex.edgeGraph K).Adj (f u) (f v))
    {u v : V} (huv : G.Adj u v) : embeddedEdgeFace f u v ∈ K.faces :=
  (hmap huv).2

open Classical in
theorem embeddedEdgeFace_card
    {K : Geometry.SimplicialComplex ℝ E} {V : Type*}
    {G : SimpleGraph V} {f : V → K.vertices}
    (hmap : ∀ ⦃u v⦄, G.Adj u v → (SimplicialComplex.edgeGraph K).Adj (f u) (f v))
    {u v : V} (huv : G.Adj u v) : (embeddedEdgeFace f u v).card = 2 :=
  Finset.card_pair (fun h => (hmap huv).1 (Subtype.ext h))

open Classical in
theorem isPLBall_embeddedGraphDerivedNeighborhood_of_isTree
    [FiniteDimensional ℝ E] {V : Type*} [Finite V]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (G : SimpleGraph V) (f : V → K.vertices)
    (hf : Function.Injective f)
    (hmap : ∀ ⦃u v⦄, G.Adj u v → (SimplicialComplex.edgeGraph K).Adj (f u) (f v))
    (hTree : G.IsTree) : IsPLBall 2 (embeddedGraphDerivedNeighborhood K G f) := by
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel _
  let _ : Nonempty V := hTree.connected.nonempty
  let hKB := hK.isCombinatorialManifoldWithBoundary
  by_cases hV : Nontrivial V
  · let _ : Nontrivial V := hV
    obtain ⟨v, hvdeg⟩ := hTree.exists_vert_degree_one_of_nontrivial
    have hvcard : (G.neighborSet v).ncard = 1 := by
      rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree]
      exact hvdeg
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hvcard
    have hvw : G.Adj v w := by
      apply (G.mem_neighborSet v w).mp
      rw [hw]
      exact Set.mem_singleton w
    have hwv : w ≠ v := hvw.symm.ne
    have hadj_eq {u : V} (hu : G.Adj v u) : u = w := by
      have hu' : u ∈ G.neighborSet v := (G.mem_neighborSet v u).mpr hu
      rw [hw] at hu'
      exact Set.mem_singleton_iff.mp hu'
    let W : Set V := {v}ᶜ
    let G' := G.induce W
    let f' : W → K.vertices := fun u => f u.1
    have hf' : Function.Injective f' := fun u z huz => Subtype.ext (hf huz)
    have hmap' : ∀ ⦃u z⦄, G'.Adj u z →
        (SimplicialComplex.edgeGraph K).Adj (f' u) (f' z) := by
      intro u z huz
      exact hmap ((SimpleGraph.induce_adj).mp huz)
    have hTree' : G'.IsTree := by
      exact ⟨hTree.connected.induce_compl_singleton_of_degree_eq_one hvdeg,
        hTree.isAcyclic.induce W⟩
    have hcardlt : Nat.card W < Nat.card V := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_compl_set]
      have htwo : 2 ≤ Fintype.card V := (Nat.succ_le_iff).mpr Fintype.one_lt_card
      have hone : Fintype.card ({v} : Set V) = 1 := Fintype.card_unique
      rw [hone]
      omega
    have hprev : IsPLBall 2 (embeddedGraphDerivedNeighborhood K G' f') :=
      isPLBall_embeddedGraphDerivedNeighborhood_of_isTree K hK G' f' hf' hmap' hTree'
    let q := embeddedEdgeFace f v w
    let cv := embeddedVertexFace f v
    let cw := embeddedVertexFace f w
    let A := (derivedNeighborhoodCell K q).space ∪
      (derivedNeighborhoodCell K cv).space
    have hqK : q ∈ K.faces := embeddedEdgeFace_mem hmap hvw
    have hqcard : q.card = 2 := embeddedEdgeFace_card hmap hvw
    have hcvK : cv ∈ K.faces := embeddedVertexFace_mem f v
    have hcwK : cw ∈ K.faces := embeddedVertexFace_mem f w
    have hqcv : q ≠ cv := by
      intro h
      have hc := congrArg Finset.card h
      rw [hqcard] at hc
      simp only [cv, embeddedVertexFace, Finset.card_singleton] at hc
      omega
    have hcvq : cv ⊆ q := by
      simp only [cv, q, embeddedVertexFace, embeddedEdgeFace, Finset.singleton_subset_iff,
        Finset.mem_insert, Finset.mem_singleton, true_or]
    have hqball : IsPLBall 2 (derivedNeighborhoodCell K q).space :=
      hKB.isPLBall_derivedNeighborhoodCell hqK
    have hcvball : IsPLBall 2 (derivedNeighborhoodCell K cv).space :=
      hKB.isPLBall_derivedNeighborhoodCell hcvK
    have hqcvball : IsPLBall 1 ((derivedNeighborhoodCell K q).space ∩
        (derivedNeighborhoodCell K cv).space) :=
      hKB.isPLBall_derivedNeighborhoodCell_inter hqK hcvK hqcv (Or.inr hcvq)
    have hA : IsPLBall 2 A :=
      hKB.isPLBall_union_of_inter_isPLBall_one hqball hcvball
        (derivedNeighborhoodCell_space_subset K q)
        (derivedNeighborhoodCell_space_subset K cv) hqcvball
    have hf_eq {a b : V} (hab : (f a : E) = (f b : E)) : a = b :=
      hf (Subtype.ext hab)
    have hinter : embeddedGraphDerivedNeighborhood K G' f' ∩ A =
        (derivedNeighborhoodCell K cw).space ∩ (derivedNeighborhoodCell K q).space := by
      apply Subset.antisymm
      · rintro x ⟨hxold, hxq | hxcv⟩
        · rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hxold with
            ⟨u, hxu⟩ | ⟨a, b, hab, hxab⟩
          · have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
              (embeddedVertexFace_mem f' u) hqK ⟨x, hxu, hxq⟩
            have hmem : (f' u : E) ∈ q := by
              rcases hcomp with h | h
              · exact Finset.singleton_subset_iff.mp h
              · have hc := Finset.card_le_card h
                rw [hqcard] at hc
                simp only [embeddedVertexFace, Finset.card_singleton] at hc
                omega
            have huvw : u.1 = v ∨ u.1 = w := by
              have h' : (f' u : E) = (f v : E) ∨ (f' u : E) = (f w : E) := by
                simpa only [q, embeddedEdgeFace, Finset.mem_insert, Finset.mem_singleton] using hmem
              exact h'.imp hf_eq hf_eq
            have huv : u.1 ≠ v := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using u.2
            have huw : u.1 = w := huvw.resolve_left huv
            exact ⟨by simpa only [cw, embeddedVertexFace, f', huw] using hxu, hxq⟩
          · have hrK : embeddedEdgeFace f' a b ∈ K.faces := embeddedEdgeFace_mem hmap' hab
            have hrcard : (embeddedEdgeFace f' a b).card = 2 := embeddedEdgeFace_card hmap' hab
            have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
              hrK hqK ⟨x, hxab, hxq⟩
            have heq : embeddedEdgeFace f' a b = q := by
              rcases hcomp with h | h
              · exact Finset.eq_of_subset_of_card_le h (by rw [hrcard, hqcard])
              · exact (Finset.eq_of_subset_of_card_le h (by rw [hqcard, hrcard])).symm
            have hvab : (f v : E) ∈ embeddedEdgeFace f' a b := by
              rw [heq]
              simp only [q, embeddedEdgeFace, Finset.mem_insert, Finset.mem_singleton, true_or]
            have hva : v = a.1 ∨ v = b.1 := by
              have h' : (f v : E) = (f' a : E) ∨ (f v : E) = (f' b : E) := by
                simpa only [embeddedEdgeFace, Finset.mem_insert, Finset.mem_singleton] using hvab
              exact h'.imp hf_eq hf_eq
            have hav : a.1 ≠ v := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using a.2
            have hbv : b.1 ≠ v := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using b.2
            exact (hva.elim (fun h => hav h.symm) (fun h => hbv h.symm)).elim
        · rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hxold with
            ⟨u, hxu⟩ | ⟨a, b, hab, hxab⟩
          · have huK := embeddedVertexFace_mem f' u
            have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
              huK hcvK ⟨x, hxu, hxcv⟩
            have heq : (f' u : E) = (f v : E) := by
              rcases hcomp with h | h
              · simpa only [cv, embeddedVertexFace, Finset.singleton_subset_iff,
                  Finset.mem_singleton] using h
              · symm
                simpa only [cv, embeddedVertexFace, Finset.singleton_subset_iff,
                  Finset.mem_singleton] using h
            have huv : u.1 = v := hf_eq heq
            have huv' : u.1 ≠ v := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using u.2
            exact (huv' huv).elim
          · have hrK : embeddedEdgeFace f' a b ∈ K.faces := embeddedEdgeFace_mem hmap' hab
            have hrcard : (embeddedEdgeFace f' a b).card = 2 := embeddedEdgeFace_card hmap' hab
            have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
              hrK hcvK ⟨x, hxab, hxcv⟩
            have hvab : (f v : E) ∈ embeddedEdgeFace f' a b := by
              rcases hcomp with h | h
              · have hc := Finset.card_le_card h
                simp only [cv, embeddedVertexFace, Finset.card_singleton] at hc
                rw [hrcard] at hc
                omega
              · exact Finset.singleton_subset_iff.mp h
            have hva : v = a.1 ∨ v = b.1 := by
              have h' : (f v : E) = (f' a : E) ∨ (f v : E) = (f' b : E) := by
                simpa only [embeddedEdgeFace, Finset.mem_insert, Finset.mem_singleton] using hvab
              exact h'.imp hf_eq hf_eq
            have hav : a.1 ≠ v := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using a.2
            have hbv : b.1 ≠ v := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using b.2
            exact (hva.elim (fun h => hav h.symm) (fun h => hbv h.symm)).elim
      · rintro x ⟨hxcw, hxq⟩
        have hwW : w ∈ W := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff] using hwv
        refine ⟨mem_embeddedGraphDerivedNeighborhood_iff.mpr (Or.inl ⟨⟨w, hwW⟩, ?_⟩), Or.inl hxq⟩
        simpa only [cw, embeddedVertexFace, f'] using hxcw
    have hcwq : cw ⊆ q := by
      simp only [cw, q, embeddedVertexFace, embeddedEdgeFace, Finset.singleton_subset_iff,
        Finset.mem_insert, Finset.mem_singleton, or_true]
    have hcwqne : cw ≠ q := by
      intro h
      have hc := congrArg Finset.card h
      simp only [cw, embeddedVertexFace, Finset.card_singleton] at hc
      rw [hqcard] at hc
      omega
    have hattach : IsPLBall 1 (embeddedGraphDerivedNeighborhood K G' f' ∩ A) := by
      rw [hinter]
      exact hKB.isPLBall_derivedNeighborhoodCell_inter hcwK hqK hcwqne (Or.inl hcwq)
    have hunion : embeddedGraphDerivedNeighborhood K G' f' ∪ A =
        embeddedGraphDerivedNeighborhood K G f := by
      ext x
      constructor
      · rintro (hxold | hxq | hxcv)
        · rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hxold with
            ⟨u, hxu⟩ | ⟨a, b, hab, hxab⟩
          · exact mem_embeddedGraphDerivedNeighborhood_iff.mpr
              (Or.inl ⟨u.1, by simpa only [f', embeddedVertexFace] using hxu⟩)
          · exact mem_embeddedGraphDerivedNeighborhood_iff.mpr
              (Or.inr ⟨a.1, b.1, (SimpleGraph.induce_adj).mp hab,
                by simpa only [f', embeddedEdgeFace] using hxab⟩)
        · exact mem_embeddedGraphDerivedNeighborhood_iff.mpr (Or.inr ⟨v, w, hvw, hxq⟩)
        · exact mem_embeddedGraphDerivedNeighborhood_iff.mpr (Or.inl ⟨v, hxcv⟩)
      · intro hx
        rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hx with
            ⟨u, hxu⟩ | ⟨a, b, hab, hxab⟩
        · by_cases huv : u = v
          · subst u
            exact Or.inr (Or.inr hxu)
          · have huW : u ∈ W := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff]
            exact Or.inl (mem_embeddedGraphDerivedNeighborhood_iff.mpr
              (Or.inl ⟨⟨u, huW⟩, by simpa only [f', embeddedVertexFace] using hxu⟩))
        · by_cases hav : a = v
          · subst a
            have hbw : b = w := hadj_eq hab
            subst b
            exact Or.inr (Or.inl hxab)
          · by_cases hbv : b = v
            · subst b
              have haw : a = w := hadj_eq hab.symm
              subst a
              have hxq' : x ∈ (derivedNeighborhoodCell K q).space := by
                simpa only [q, embeddedEdgeFace, Finset.pair_comm] using hxab
              exact Or.inr (Or.inl hxq')
            · have haW : a ∈ W := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff]
              have hbW : b ∈ W := by simpa only [W, Set.mem_compl_iff, Set.mem_singleton_iff]
              have hab' : G'.Adj ⟨a, haW⟩ ⟨b, hbW⟩ := (SimpleGraph.induce_adj).mpr hab
              exact Or.inl (mem_embeddedGraphDerivedNeighborhood_iff.mpr
                (Or.inr ⟨⟨a, haW⟩, ⟨b, hbW⟩, hab',
                  by simpa only [f', embeddedEdgeFace] using hxab⟩))
    have hU := hKB.isPLBall_union_of_inter_isPLBall_one hprev hA
      (embeddedGraphDerivedNeighborhood_subset K G' f')
      (union_subset (derivedNeighborhoodCell_space_subset K q)
        (derivedNeighborhoodCell_space_subset K cv)) hattach
    rwa [hunion] at hU
  · have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    let _ : Subsingleton V := hsub
    let v : V := Classical.choice (inferInstance : Nonempty V)
    have heq : embeddedGraphDerivedNeighborhood K G f =
        (derivedNeighborhoodCell K (embeddedVertexFace f v)).space := by
      ext x
      constructor
      · intro hx
        rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hx with
            ⟨u, hxu⟩ | ⟨u, w, huw, -⟩
        · simpa only [Subsingleton.elim u v] using hxu
        · have huv : u = v := Subsingleton.elim _ _
          have hwv' : w = v := Subsingleton.elim _ _
          have hvv : G.Adj v v := by simpa only [huv, hwv'] using huw
          exact (G.loopless.irrefl v hvv).elim
      · intro hx
        exact mem_embeddedGraphDerivedNeighborhood_iff.mpr (Or.inl ⟨v, hx⟩)
    rw [heq]
    exact hKB.isPLBall_derivedNeighborhoodCell (embeddedVertexFace_mem f v)
termination_by Nat.card V
decreasing_by exact hcardlt

end DifferentialGeometry.Topology.PiecewiseLinear

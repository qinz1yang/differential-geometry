import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhood_simplex_space_eq_of_card_le_three
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card ≤ 3) :
    (PiecewiseLinear.derivedNeighborhood K (simplexComplex s (K.indep hs))).space =
      ((derivedNeighborhoodCell K s).space ∪
        ⋃ e ∈ s.powersetCard 2, (derivedNeighborhoodCell K e).space) ∪
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space := by
  classical
  rw [← iUnion_derivedNeighborhoodCell_space K (simplexComplex s (K.indep hs)) (fun t ht => K.down_closed hs ht.2 ht.1)]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    by_cases hts : t = s
    · exact Or.inl (Or.inl (hts ▸ hxt))
    · have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht.2, hts⟩)
      have hpos := Finset.card_pos.mpr ht.1
      have hc : t.card = 1 ∨ t.card = 2 := by omega
      rcases hc with hc | hc
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
        exact Or.inr (mem_iUnion₂.mpr ⟨v, ht.2 (Finset.mem_singleton_self _), hxt⟩)
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨t, Finset.mem_powersetCard.mpr ⟨ht.2, hc⟩, hxt⟩))
  · rintro x ((hx | hx) | hx)
    · exact mem_iUnion₂.mpr ⟨s, ⟨K.nonempty_of_mem_faces hs, Finset.Subset.rfl⟩, hx⟩
    · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
      obtain ⟨hts, htcard⟩ := Finset.mem_powersetCard.mp ht
      exact mem_iUnion₂.mpr ⟨t, ⟨Finset.card_pos.mp (by omega), hts⟩, hxt⟩
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨{v}, ⟨Finset.singleton_nonempty v, Finset.singleton_subset_iff.mpr hv⟩, hxv⟩

noncomputable local instance : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _

open Classical in
private theorem isPLBall_triangle_cells
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {s : Finset (EuclideanSpace ℝ (Fin 3))} (hs : s ∈ (boundaryComplex 3 K).faces)
    (hcard : s.card = 3) :
    IsPLBall 3 (((derivedNeighborhoodCell K s).space ∪
      ⋃ e ∈ s.powersetCard 2, (derivedNeighborhoodCell K e).space) ∪
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space) := by
  classical
  let C := fun t : Finset (EuclideanSpace ℝ (Fin 3)) => (derivedNeighborhoodCell K t).space
  let edges := s.powersetCard 2
  let B := C s ∪ ⋃ e ∈ edges, C e
  have hsK := boundaryComplex_faces_subset 3 K hs
  have hedges (e : Finset (EuclideanSpace ℝ (Fin 3))) (he : e ∈ edges) :
      e ⊆ s ∧ e.card = 2 := Finset.mem_powersetCard.mp he
  have heK (e : Finset (EuclideanSpace ℝ (Fin 3))) (he : e ∈ edges) : e ∈ K.faces :=
    K.down_closed hsK (hedges e he).1 (Finset.card_pos.mp (by rw [(hedges e he).2]; decide))
  have hB : IsPLBall 3 B := hK.isPLBall_union_derivedNeighborhoodCells_of_card hsK edges
    (by decide : 0 < 2) (by omega) (fun e he => (hedges e he).1) (fun e he => (hedges e he).2)
  suffices h : ∀ a : Finset (EuclideanSpace ℝ (Fin 3)), a ⊆ s →
      IsPLBall 3 (B ∪ ⋃ v ∈ a, C {v}) from h s Finset.Subset.rfl
  intro a
  induction a using Finset.induction_on with
  | empty => intro _; simpa using hB
  | @insert v a hva ih =>
    intro has
    have hvs : v ∈ s := has (Finset.mem_insert_self _ _)
    have ha : a ⊆ s := (Finset.subset_insert _ _).trans has
    have hprev := ih ha
    have hvB : {v} ∈ (boundaryComplex 3 K).faces :=
      (boundaryComplex 3 K).down_closed hs (Finset.singleton_subset_iff.mpr hvs)
        (Finset.singleton_nonempty v)
    have hvK := boundaryComplex_faces_subset 3 K hvB
    have hvne : ({v} : Finset (EuclideanSpace ℝ (Fin 3))) ≠ s := by
      intro heq
      have hc := congrArg Finset.card heq
      simp only [Finset.card_singleton, hcard] at hc
      omega
    let arms := edges.filter (fun e => v ∈ e)
    have harme (e : Finset (EuclideanSpace ℝ (Fin 3))) (he : e ∈ arms) : e ∈ edges :=
      Finset.mem_of_mem_filter e he
    have harms (e : Finset (EuclideanSpace ℝ (Fin 3))) (he : e ∈ arms) :
        e ≠ {v} ∧ e ≠ s := by
      have hc := (hedges e (harme e he)).2
      constructor <;> intro heq <;> rw [heq] at hc
      · simp only [Finset.card_singleton] at hc
        omega
      · omega
    have hcomp (e : Finset (EuclideanSpace ℝ (Fin 3))) (he : e ∈ arms) :
        ({v} ⊆ e ∨ e ⊆ {v}) ∧ (s ⊆ e ∨ e ⊆ s) :=
      ⟨Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp he).2),
        Or.inr (hedges e (harme e he)).1⟩
    have hincomp (e : Finset (EuclideanSpace ℝ (Fin 3))) (he : e ∈ arms)
        (f : Finset (EuclideanSpace ℝ (Fin 3))) (hf : f ∈ arms) (hne : e ≠ f) :
        ¬e ⊆ f ∧ ¬f ⊆ e := by
      have hec := (hedges e (harme e he)).2
      have hfc := (hedges f (harme f hf)).2
      exact ⟨fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)),
        fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)).symm⟩
    have hattach : IsPLBall 2 (C {v} ∩ (C s ∪ ⋃ e ∈ arms, C e)) :=
      hK.isPLBall_derivedNeighborhoodCell_inter_union hvB hsK hvne
        (Or.inl (Finset.singleton_subset_iff.mpr hvs)) arms
        (fun e he => heK e (harme e he)) harms hcomp hincomp
    have hinter : (B ∪ ⋃ w ∈ a, C {w}) ∩ C {v} = C {v} ∩ (C s ∪ ⋃ e ∈ arms, C e) := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxv⟩
        · rcases hx with hxs | hxe
          · exact ⟨hxv, Or.inl hxs⟩
          · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxe
            have hve : v ∈ e := by
              rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hvK (heK e he)
                ⟨x, hxv, hxe⟩ with h | h
              · exact Finset.singleton_subset_iff.mp h
              · have hc := Finset.card_le_card h
                rw [(hedges e he).2, Finset.card_singleton] at hc
                omega
            exact ⟨hxv, Or.inr (mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, hxe⟩)⟩
        · obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
          have hwK : {w} ∈ K.faces := K.down_closed hsK
            (Finset.singleton_subset_iff.mpr (ha hw)) (Finset.singleton_nonempty w)
          have hwv : w ≠ v := ne_of_mem_of_not_mem hw hva
          have hdis := disjoint_derivedNeighborhoodCell_space K hwK hvK
            (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hwv)
            (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hwv.symm)
          exact (hdis.le_bot ⟨hxw, hxv⟩).elim
      · rintro x ⟨hxv, hxs | hxarms⟩
        · exact ⟨Or.inl (Or.inl hxs), hxv⟩
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxarms
          exact ⟨Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, harme e he, hxe⟩)), hxv⟩
    have hI : IsPLBall 2 ((B ∪ ⋃ w ∈ a, C {w}) ∩ C {v}) := hinter.symm ▸ hattach
    have hvball : IsPLBall 3 (C {v}) := hK.isPLBall_derivedNeighborhoodCell hvK
    have hleft := hvball.inter_subset_frontier_of_isPLBall hI (by decide : 2 < 3)
    have hright : (B ∪ ⋃ w ∈ a, C {w}) ∩ C {v} ⊆ frontier (C {v}) := by
      rw [inter_comm] at hI ⊢
      exact hprev.inter_subset_frontier_of_isPLBall hI (by decide : 2 < 3)
    have h := isPLBall_union_of_inter_isPLBall_two hprev hvball hI hleft hright
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_simplex
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {s : Finset (EuclideanSpace ℝ (Fin 3))} (hs : s ∈ (boundaryComplex 3 K).faces) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K
      (simplexComplex s (K.indep (boundaryComplex_faces_subset 3 K hs)))).space := by
  classical
  have hsK := boundaryComplex_faces_subset 3 K hs
  have hle : s.card ≤ 3 := ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.1
  have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hsK)
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hc | hc | hc
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    rw [← derivedNeighborhoodCell_singleton K hsK]
    exact hK.isPLBall_derivedNeighborhoodCell hsK
  · have hedge : (⋃ e ∈ s.powersetCard 2, (derivedNeighborhoodCell K e).space) =
        (derivedNeighborhoodCell K s).space := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        obtain ⟨hes, hec⟩ := Finset.mem_powersetCard.mp he
        exact Finset.eq_of_subset_of_card_le hes (by omega) ▸ hxe
      · intro x hx
        exact mem_iUnion₂.mpr ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, hc⟩, hx⟩
    have hvertex : (⋃ e ∈ s.powersetCard 1, (derivedNeighborhoodCell K e).space) =
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        obtain ⟨hes, hec⟩ := Finset.mem_powersetCard.mp he
        obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hec
        exact mem_iUnion₂.mpr ⟨v, Finset.singleton_subset_iff.mp hes, hxe⟩
      · intro x hx
        obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_powersetCard.mpr
          ⟨Finset.singleton_subset_iff.mpr hv, Finset.card_singleton v⟩, hxv⟩
    rw [derivedNeighborhood_simplex_space_eq_of_card_le_three K hsK hle, hedge, union_self,
      ← hvertex]
    exact hK.isPLBall_union_derivedNeighborhoodCells_of_card hsK (s.powersetCard 1)
      (by decide : 0 < 1) (by omega) (fun e he => (Finset.mem_powersetCard.mp he).1)
      (fun e he => (Finset.mem_powersetCard.mp he).2)
  · rw [derivedNeighborhood_simplex_space_eq_of_card_le_three K hsK hle]
    exact isPLBall_triangle_cells hK hs hc

end DifferentialGeometry.Topology.PiecewiseLinear

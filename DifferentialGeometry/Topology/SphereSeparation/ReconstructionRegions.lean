import DifferentialGeometry.Topology.SphereSeparation.BallSideRelations

namespace DifferentialGeometry.Topology.SphereSeparation.SphereSides

open Set

variable {X : Type*} [TopologicalSpace X] {S S₁ S₂ C : Set X}

theorem eq_compactSide_of_frontier_subset (d : SphereSides S)
    (hC : IsOpen C) (hne : C.Nonempty) (hc : IsCompact (closure C))
    (havoid : Disjoint C S) (hfront : frontier C ⊆ S) : C = d.compactSide := by
  have hside {T : Set X} (ht : IsPreconnected T) (hTS : T ⊆ Sᶜ)
      (hne : (T ∩ C).Nonempty) : T ⊆ C := by
    apply ht.subset_left_of_subset_union hC isClosed_closure.isOpen_compl
      (by exact disjoint_compl_right.mono_left subset_closure) _ hne
    intro x hx
    by_cases hxC : x ∈ C
    · exact Or.inl hxC
    · refine Or.inr (fun hxcl => hTS hx (hfront ?_))
      rw [hC.frontier_eq]
      exact ⟨hxcl, hxC⟩
  have hCE : Disjoint C d.endSide := by
    rw [disjoint_left]
    intro x hxC hxE
    have hEC := hside d.isConnected_endSide.isPreconnected d.endSide_subset_compl
      ⟨x, hxE, hxC⟩
    exact d.not_isCompact_closure_endSide
      (hc.of_isClosed_subset isClosed_closure (closure_mono hEC))
  have hCB : C ⊆ d.compactSide := by
    intro x hx
    have hxS : x ∈ Sᶜ := fun h => havoid.le_bot ⟨hx, h⟩
    rw [d.compl_eq_union] at hxS
    exact hxS.resolve_right (fun h => hCE.le_bot ⟨hx, h⟩)
  refine Subset.antisymm hCB (hside d.isConnected_compactSide.isPreconnected
    d.compactSide_subset_compl ?_)
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hCB hx, hx⟩

theorem compactSide_inter_eq_of_subset_of_boundary_inter_eq
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hsub : d₁.compactSide ⊆ d₂.compactSide) {U : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ S₁ ∩ U) (heq : S₁ ∩ U = S₂ ∩ U)
    (hconn : IsPreconnected (d₁.endSide ∩ U)) :
    d₁.compactSide ∩ U = d₂.compactSide ∩ U := by
  have havoid : d₁.endSide ∩ U ⊆ S₂ᶜ := by
    intro y hy hyS
    exact d₁.endSide_subset_compl hy.1 (heq.symm.subset ⟨hyS, hy.2⟩).1
  have hend : d₁.endSide ∩ U ⊆ d₂.endSide := by
    rcases d₂.subset_compactSide_or_subset_endSide hconn havoid with h | h
    · have hxcl : x ∈ closure d₂.endSide := d₂.closure_endSide ▸ Or.inr (heq.subset hx).1
      obtain ⟨y, hyU, hyE⟩ := mem_closure_iff.mp hxcl U hU hx.2
      have hyS : y ∉ S₁ := fun hy => d₂.endSide_subset_compl hyE (heq.subset ⟨hy, hyU⟩).1
      have hyB : y ∈ d₁.compactSide ∪ d₁.endSide := d₁.compl_eq_union ▸ hyS
      rcases hyB with hy | hy
      · exact False.elim (d₂.disjoint.le_bot ⟨hsub hy, hyE⟩)
      · exact False.elim (d₂.disjoint.le_bot ⟨h ⟨hy, hyU⟩, hyE⟩)
    · exact h
  apply Subset.antisymm (inter_subset_inter_left U hsub)
  intro y hy
  have hyS : y ∉ S₁ := fun hyS => d₂.compactSide_subset_compl hy.1
    (heq.subset ⟨hyS, hy.2⟩).1
  have hyB : y ∈ d₁.compactSide ∪ d₁.endSide := d₁.compl_eq_union ▸ hyS
  exact ⟨hyB.resolve_right (fun h => d₂.disjoint.le_bot ⟨hy.1, hend ⟨h, hy.2⟩⟩), hy.2⟩

theorem subset_union_closures_of_disjoint_of_boundary_inter_eq
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hd : Disjoint d₁.compactSide d₂.compactSide) {U : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ S₁ ∩ U) (heq : S₁ ∩ U = S₂ ∩ U)
    (hconn : IsPreconnected (d₁.endSide ∩ U)) :
    U ⊆ interior (closure d₁.compactSide ∪ closure d₂.compactSide) := by
  have havoid : d₁.endSide ∩ U ⊆ S₂ᶜ := by
    intro y hy hyS
    exact d₁.endSide_subset_compl hy.1 (heq.symm.subset ⟨hyS, hy.2⟩).1
  have hend : d₁.endSide ∩ U ⊆ d₂.compactSide := by
    rcases d₂.subset_compactSide_or_subset_endSide hconn havoid with h | h
    · exact h
    · have hxcl : x ∈ closure d₂.compactSide :=
        d₂.closure_compactSide ▸ Or.inr (heq.subset hx).1
      obtain ⟨y, hyU, hyB⟩ := mem_closure_iff.mp hxcl U hU hx.2
      have hyS : y ∉ S₁ := fun hy => d₂.compactSide_subset_compl hyB
        (heq.subset ⟨hy, hyU⟩).1
      have hyB₁ : y ∈ d₁.compactSide ∪ d₁.endSide := d₁.compl_eq_union ▸ hyS
      rcases hyB₁ with hy | hy
      · exact False.elim (hd.le_bot ⟨hy, hyB⟩)
      · exact False.elim (d₂.disjoint.le_bot ⟨hyB, h ⟨hy, hyU⟩⟩)
  apply interior_maximal _ hU
  intro y hy
  by_cases hyS : y ∈ S₁
  · exact Or.inl (d₁.closure_compactSide ▸ Or.inr hyS)
  · have hyB : y ∈ d₁.compactSide ∪ d₁.endSide := d₁.compl_eq_union ▸ hyS
    rcases hyB with hyB | hyE
    · exact Or.inl (subset_closure hyB)
    · exact Or.inr (subset_closure (hend ⟨hyE, hy⟩))

private theorem interior_union_closure_disjoint_sdiff
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hd : Disjoint d₁.compactSide d₂.compactSide) :
    Disjoint (interior (closure d₁.compactSide ∪ closure d₂.compactSide)) (S₁ \ S₂) := by
  rw [disjoint_left]
  intro x hx hxS
  have hxcl₁ : x ∈ closure d₁.compactSide := d₁.closure_compactSide ▸ Or.inr hxS.1
  have hxcl₂ : x ∉ closure d₂.compactSide := by
    rw [d₂.closure_compactSide]
    rintro (hy | hy)
    · exact (hd.closure_left d₂.isOpen_compactSide).le_bot ⟨hxcl₁, hy⟩
    · exact hxS.2 hy
  have hxi : x ∈ interior ((closure d₂.compactSide)ᶜ) := by
    rw [isClosed_closure.isOpen_compl.interior_eq]
    exact hxcl₂
  have hx₁ := interior_union_inter_interior_compl_right_subset ⟨hx, hxi⟩
  rw [d₁.interior_closure_compactSide] at hx₁
  exact d₁.compactSide_subset_compl hx₁ hxS.1

theorem disjoint_reconstruction_regions
    (d : SphereSides S) (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hd : Disjoint d₁.compactSide d₂.compactSide)
    (hS : S = closure ((S₁ \ S₂) ∪ (S₂ \ S₁)))
    (hpatch : (S₁ ∪ S₂) \ S ⊆ interior (closure d₁.compactSide ∪ closure d₂.compactSide)) :
    closure d.compactSide = closure d₁.compactSide ∪ closure d₂.compactSide ∧
      closure d₁.compactSide ∩ closure d₂.compactSide = S₁ ∩ S₂ := by
  let K := closure d₁.compactSide ∪ closure d₂.compactSide
  have hK : IsClosed K := isClosed_closure.union isClosed_closure
  have h₁ : d₁.compactSide ⊆ interior K := by
    rw [← d₁.interior_closure_compactSide]
    exact interior_mono subset_union_left
  have h₂ : d₂.compactSide ⊆ interior K := by
    rw [← d₂.interior_closure_compactSide]
    exact interior_mono subset_union_right
  have hreg : closure (interior K) = K :=
    Subset.antisymm hK.closure_interior_subset
      (union_subset (closure_mono h₁) (closure_mono h₂))
  have hne : (interior K).Nonempty := d₁.compactSide_nonempty.mono h₁
  have hcompact : IsCompact (closure (interior K)) := by
    rw [hreg]
    exact d₁.isCompact_closure_compactSide.union d₂.isCompact_closure_compactSide
  have havoid : Disjoint (interior K) S := by
    rw [hS]
    apply Disjoint.closure_right _ isOpen_interior
    apply disjoint_union_right.mpr
    refine ⟨interior_union_closure_disjoint_sdiff d₁ d₂ hd, ?_⟩
    simpa only [union_comm] using interior_union_closure_disjoint_sdiff d₂ d₁ hd.symm
  have hfront : frontier (interior K) ⊆ S := by
    intro x hx
    have hxK : x ∈ frontier K := frontier_interior_subset hx
    have hxS : x ∈ S₁ ∪ S₂ := by
      rcases frontier_union_subset (closure d₁.compactSide) (closure d₂.compactSide) hxK
        with hx | hx
      · exact Or.inl (d₁.frontier_compactSide ▸ frontier_closure_subset hx.1)
      · exact Or.inr (d₂.frontier_compactSide ▸ frontier_closure_subset hx.2)
    by_contra hxnot
    have hxi := hpatch ⟨hxS, hxnot⟩
    rw [isOpen_interior.frontier_eq] at hx
    exact hx.2 hxi
  have heq := d.eq_compactSide_of_frontier_subset isOpen_interior hne hcompact havoid hfront
  exact ⟨by rw [← heq, hreg], d₁.closure_compactSide_inter_eq_of_disjoint d₂ hd⟩

theorem nested_reconstruction_regions
    (d : SphereSides S) (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hproper : d₁.compactSide ⊂ d₂.compactSide) (hS : S ⊆ S₁ ∪ S₂)
    (hpatch : ∀ x ∈ (S₁ ∪ S₂) \ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      d₁.compactSide ∩ U = d₂.compactSide ∩ U) :
    d.compactSide = d₂.compactSide \ closure d₁.compactSide ∧
      closure d₂.compactSide = closure d.compactSide ∪ closure d₁.compactSide ∧
      closure d.compactSide ∩ closure d₁.compactSide = S ∩ S₁ := by
  let R := d₂.compactSide ∩ d₁.endSide
  have hReq : R = d₂.compactSide \ closure d₁.compactSide := by
    rw [d₁.closure_compactSide_eq_compl, sdiff_compl]
  have hopen : IsOpen R := d₂.isOpen_compactSide.inter d₁.isOpen_endSide
  have hne : R.Nonempty := by
    by_contra hn
    have hcl : d₂.compactSide ⊆ closure d₁.compactSide := by
      intro x hx
      rw [d₁.closure_compactSide_eq_compl]
      exact fun hy => hn ⟨x, hx, hy⟩
    have hsub : d₂.compactSide ⊆ d₁.compactSide := by
      simpa only [d₂.isOpen_compactSide.interior_eq, d₁.interior_closure_compactSide]
        using interior_mono hcl
    exact hproper.not_ge hsub
  have hcompact : IsCompact (closure R) :=
    d₂.isCompact_closure_compactSide.of_isClosed_subset isClosed_closure
      (closure_mono inter_subset_left)
  have havoid : Disjoint R S := by
    rw [disjoint_left]
    intro x hx hxS
    rcases hS hxS with hx₁ | hx₂
    · exact d₁.endSide_subset_compl hx.2 hx₁
    · exact d₂.compactSide_subset_compl hx.1 hx₂
  have hfront : frontier R ⊆ S := by
    intro x hx
    have hxS : x ∈ S₁ ∪ S₂ := by
      rcases frontier_inter_subset d₂.compactSide d₁.endSide hx with hx | hx
      · exact Or.inr (d₂.frontier_compactSide ▸ hx.1)
      · exact Or.inl (d₁.frontier_endSide ▸ hx.2)
    by_contra hxnot
    obtain ⟨U, hU, hxU, heq⟩ := hpatch x ⟨hxS, hxnot⟩
    obtain ⟨y, hyU, hyR⟩ := mem_closure_iff.mp (frontier_subset_closure hx) U hU hxU
    have hy₁ : y ∈ d₁.compactSide := (heq.symm.subset ⟨hyR.1, hyU⟩).1
    exact d₁.disjoint.le_bot ⟨hy₁, hyR.2⟩
  have heq : R = d.compactSide :=
    d.eq_compactSide_of_frontier_subset hopen hne hcompact havoid hfront
  refine ⟨heq.symm.trans hReq, ?_, ?_⟩
  · apply Subset.antisymm
    · apply closure_minimal _ (isClosed_closure.union isClosed_closure)
      intro x hx
      by_cases hx₁ : x ∈ closure d₁.compactSide
      · exact Or.inr hx₁
      · apply Or.inl
        apply subset_closure
        rw [← heq, hReq]
        exact ⟨hx, hx₁⟩
    · apply union_subset
      · exact closure_mono (heq ▸ inter_subset_left)
      · exact closure_mono hproper.subset
  · apply d.closure_compactSide_inter_eq_of_disjoint d₁
    rw [← heq, disjoint_left]
    intro x hx hy
    exact d₁.disjoint.le_bot ⟨hy, hx.2⟩

end DifferentialGeometry.Topology.SphereSeparation.SphereSides

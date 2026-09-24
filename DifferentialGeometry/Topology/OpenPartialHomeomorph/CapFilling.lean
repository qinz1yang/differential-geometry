import DifferentialGeometry.Topology.OpenPartialHomeomorph.GraphOrientation

open Set

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [PreconnectedSpace X] [TopologicalSpace Y]

theorem fill_of_shared_cylinder_boundary_of_disjoint_interiors
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : ∀ q : X, (q, 0) ∈ T.source) {W B R : Set Y}
    (hW : closure (interior W) = W) (hB : closure (interior B) = B)
    (houtside : Disjoint (interior W) (interior B)) (hR : IsClosed R)
    (hfrontW : frontier W = range (fun q : X => T (q, 0)) ∪ R)
    (hfrontB : frontier B = range (fun q : X => T (q, 0)))
    (hdis : Disjoint (range (fun q : X => T (q, 0))) R) :
    B ∩ W = range (fun q : X => T (q, 0)) ∧
      closure (interior (W ∪ B)) = W ∪ B ∧
      frontier (W ∪ B) = R ∧
      range (fun q : X => T (q, 0)) ⊆ interior (W ∪ B) := by
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hBclosed : IsClosed B := hB ▸ isClosed_closure
  have hWB : W ⊆ (interior B)ᶜ := by
    rw [← hW]
    exact (houtside.closure_left isOpen_interior).subset_compl_right
  have hSW : range (fun q : X => T (q, 0)) ⊆ W :=
    fun x hx => hWclosed.frontier_subset (hfrontW.symm ▸ Or.inl hx)
  have hSB : range (fun q : X => T (q, 0)) ⊆ B :=
    fun x hx => hBclosed.frontier_subset (hfrontB.symm ▸ hx)
  have hinter : B ∩ W = range (fun q : X => T (q, 0)) := by
    apply subset_antisymm
    · intro x hx
      exact hfrontB ▸ (show x ∈ frontier B from ⟨subset_closure hx.1, hWB hx.2⟩)
    · exact fun x hx => ⟨hSB hx, hSW hx⟩
  have hRavoid : Disjoint R B := by
    rw [disjoint_left]
    intro x hxR hxB
    have hxW : x ∈ W := hWclosed.frontier_subset (hfrontW.symm ▸ Or.inr hxR)
    exact disjoint_left.mp hdis (hinter ▸ ⟨hxB, hxW⟩) hxR
  obtain ⟨rW, hrW, horW⟩ := exists_cylinder_orientation_of_frontier_eq_union T
    hsource hW hR hfrontW hdis
  obtain ⟨rB, hrB, horB⟩ := exists_cylinder_orientation_of_frontier_eq_union T
    hsource hB isClosed_empty (by simpa using hfrontB) (disjoint_empty _)
  let r := min rW rB
  have hr : 0 < r := lt_min hrW hrB
  have hhalves : ∀ q : X, ∀ t ∈ Ioo (0 : ℝ) r,
      T (q, t) ∈ W ∪ B ∧ T (q, -t) ∈ W ∪ B := by
    intro q t ht
    have htW : t ∈ Ioo (0 : ℝ) rW := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have htB : t ∈ Ioo (0 : ℝ) rB := ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
    rcases horW with hWpos | hWneg <;> rcases horB with hBpos | hBneg
    · exact (hWB (interior_subset (hWpos q t htW).2) (hBpos q t htB).2).elim
    · exact ⟨Or.inr (interior_subset (hBneg q t htB).2),
        Or.inl (interior_subset (hWpos q t htW).2)⟩
    · exact ⟨Or.inl (interior_subset (hWneg q t htW).2),
        Or.inr (interior_subset (hBpos q t htB).2)⟩
    · exact (hWB (interior_subset (hWneg q t htW).2) (hBneg q t htB).2).elim
  have hfill : range (fun q : X => T (q, 0)) ⊆ interior (W ∪ B) := by
    rintro x ⟨q, rfl⟩
    have hVopen : IsOpen (T.source ∩ (univ ×ˢ Ioo (-r) r)) :=
      T.open_source.inter (isOpen_univ.prod isOpen_Ioo)
    have hOopen : IsOpen (T '' (T.source ∩ (univ ×ˢ Ioo (-r) r))) :=
      T.isOpen_image_of_subset_source hVopen inter_subset_left
    apply mem_interior.mpr
    refine ⟨T '' (T.source ∩ (univ ×ˢ Ioo (-r) r)), ?_, hOopen, ?_⟩
    · rintro y ⟨⟨z, t⟩, ht, rfl⟩
      rcases lt_trichotomy t 0 with hn | he | hp
      · have hs : -t ∈ Ioo (0 : ℝ) r := ⟨neg_pos.mpr hn, by linarith [ht.2.2.1]⟩
        simpa only [neg_neg] using (hhalves z (-t) hs).2
      · subst t
        exact Or.inl (hSW (mem_range_self z))
      · exact (hhalves z t ⟨hp, ht.2.2.2⟩).1
    · exact ⟨(q, 0), ⟨hsource q, mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩
  have hreg : closure (interior (W ∪ B)) = W ∪ B := by
    apply subset_antisymm (closure_minimal interior_subset (hWclosed.union hBclosed))
    rintro x (hx | hx)
    · exact closure_mono (interior_mono subset_union_left) (hW.symm ▸ hx)
    · exact closure_mono (interior_mono subset_union_right) (hB.symm ▸ hx)
  have hfront : frontier (W ∪ B) = R := by
    apply subset_antisymm
    · intro x hx
      rcases frontier_union_subset W B hx with h | h
      · rw [hfrontW] at h
        exact h.1.resolve_left (fun hs => hx.2 (hfill hs))
      · exact (hx.2 (hfill (hfrontB ▸ h.2))).elim
    · intro x hxR
      have hxW : x ∈ frontier W := hfrontW.symm ▸ Or.inr hxR
      have hxB : x ∉ B := fun hxB => disjoint_left.mp hRavoid hxR hxB
      refine ⟨closure_mono subset_union_left hxW.1, ?_⟩
      intro hxint
      apply hxW.2
      apply mem_interior.mpr
      refine ⟨interior (W ∪ B) ∩ Bᶜ, ?_, isOpen_interior.inter hBclosed.isOpen_compl,
        hxint, hxB⟩
      intro y hy
      exact (interior_subset hy.1).resolve_right hy.2
  exact ⟨hinter, hreg, hfront, hfill⟩

theorem subset_or_fill_of_shared_cylinder_boundary
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : ∀ q : X, (q, 0) ∈ T.source) {W B R : Set Y}
    (hW : closure (interior W) = W) (hB : closure (interior B) = B)
    (hconn : IsPreconnected (interior W)) (hR : IsClosed R)
    (hfrontW : frontier W = range (fun q : X => T (q, 0)) ∪ R)
    (hfrontB : frontier B = range (fun q : X => T (q, 0)))
    (hdis : Disjoint (range (fun q : X => T (q, 0))) R) :
    W ⊆ B ∨
      B ∩ W = range (fun q : X => T (q, 0)) ∧
      closure (interior (W ∪ B)) = W ∪ B ∧
      frontier (W ∪ B) = R ∧
      range (fun q : X => T (q, 0)) ⊆ interior (W ∪ B) := by
  have hBclosed : IsClosed B := hB ▸ isClosed_closure
  have havoid : interior W ⊆ (frontier B)ᶜ := by
    intro x hx hb
    have hf : x ∈ frontier W := hfrontW.symm ▸ Or.inl (hfrontB ▸ hb)
    exact hf.2 hx
  have hsplit : (frontier B)ᶜ = interior B ∪ Bᶜ := by
    rw [compl_frontier_eq_union_interior, hBclosed.isOpen_compl.interior_eq]
  rcases hconn.subset_or_subset isOpen_interior hBclosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (havoid.trans hsplit.subset) with hin | hout
  · exact Or.inl (hW ▸ hB ▸ closure_mono hin)
  have hWB : W ⊆ (interior B)ᶜ := by
    rw [← hW]
    simpa only [closure_compl] using closure_mono hout
  exact Or.inr (fill_of_shared_cylinder_boundary_of_disjoint_interiors T hsource hW hB
    (disjoint_left.mpr (fun x hxW hxB => hWB (interior_subset hxW) hxB))
    hR hfrontW hfrontB hdis)

omit [CompactSpace X] [PreconnectedSpace X] in
private theorem disjoint_closure_sdiff_of_cylinder_subset
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : ∀ q : X, (q, 0) ∈ T.source) {W B : Set Y} {r : ℝ}
    (hr : 0 < r)
    (hsub : ∀ q : X, ∀ t ∈ Ioo (-r) r, T (q, t) ∈ W → T (q, t) ∈ B) :
    Disjoint (range (fun q : X => T (q, 0))) (closure (W \ B)) := by
  rw [disjoint_left]
  rintro x ⟨q, rfl⟩ hx
  let O := T '' (T.source ∩ (univ ×ˢ Ioo (-r) r))
  have hopen : IsOpen O := T.isOpen_image_of_subset_source
    (T.open_source.inter (isOpen_univ.prod isOpen_Ioo)) inter_subset_left
  have hmem : T (q, 0) ∈ O :=
    ⟨(q, 0), ⟨hsource q, mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩
  obtain ⟨y, hyO, hyW, hyB⟩ := mem_closure_iff.mp hx O hopen hmem
  obtain ⟨⟨z, t⟩, ht, rfl⟩ := hyO
  exact hyB (hsub z t ht.2.2 hyW)

theorem fill_of_shared_cylinder_boundary_of_exterior_accumulation
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : ∀ q : X, (q, 0) ∈ T.source) {W B R : Set Y}
    (hW : closure (interior W) = W) (hB : closure (interior B) = B)
    (hR : IsClosed R)
    (hfrontW : frontier W = range (fun q : X => T (q, 0)) ∪ R)
    (hfrontB : frontier B = range (fun q : X => T (q, 0)))
    (hdis : Disjoint (range (fun q : X => T (q, 0))) R)
    (htouch : (range (fun q : X => T (q, 0)) ∩ closure (W \ B)).Nonempty) :
    closure (interior (W ∪ B)) = W ∪ B ∧
      frontier (W ∪ B) = R \ B ∧
      range (fun q : X => T (q, 0)) ⊆ interior (W ∪ B) := by
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hBclosed : IsClosed B := hB ▸ isClosed_closure
  have hSW : range (fun q : X => T (q, 0)) ⊆ W :=
    fun x hx => hWclosed.frontier_subset (hfrontW.symm ▸ Or.inl hx)
  have hSB : range (fun q : X => T (q, 0)) ⊆ B :=
    fun x hx => hBclosed.frontier_subset (hfrontB.symm ▸ hx)
  obtain ⟨rW, hrW, horW⟩ := exists_cylinder_orientation_of_frontier_eq_union T
    hsource hW hR hfrontW hdis
  obtain ⟨rB, hrB, horB⟩ := exists_cylinder_orientation_of_frontier_eq_union T
    hsource hB isClosed_empty (by simpa using hfrontB) (disjoint_empty _)
  let r := min rW rB
  have hr : 0 < r := lt_min hrW hrB
  have hsame
      (hlocal : ∀ q : X, ∀ t ∈ Ioo (-r) r, T (q, t) ∈ W → T (q, t) ∈ B) : False := by
    obtain ⟨x, hxS, hxC⟩ := htouch
    exact disjoint_left.mp
      (disjoint_closure_sdiff_of_cylinder_subset T hsource hr hlocal) hxS hxC
  have hhalves : ∀ q : X, ∀ t ∈ Ioo (0 : ℝ) r,
      T (q, t) ∈ W ∪ B ∧ T (q, -t) ∈ W ∪ B := by
    rcases horW with hWpos | hWneg <;> rcases horB with hBpos | hBneg
    · exfalso
      apply hsame
      intro q t ht htW
      rcases lt_trichotomy t 0 with hn | he | hp
      · have htB : -t ∈ Ioo (0 : ℝ) rB := ⟨neg_pos.mpr hn, by
          have := min_le_right rW rB; dsimp [r] at ht; linarith [ht.1]⟩
        simpa only [neg_neg] using interior_subset (hBpos q (-t) htB).2
      · subst t; exact hSB (mem_range_self q)
      · exact ((hWpos q t ⟨hp, ht.2.trans_le (min_le_left _ _)⟩).1 htW).elim
    · intro q t ht
      exact ⟨Or.inr (interior_subset (hBneg q t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩).2),
        Or.inl (interior_subset (hWpos q t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩).2)⟩
    · intro q t ht
      exact ⟨Or.inl (interior_subset (hWneg q t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩).2),
        Or.inr (interior_subset (hBpos q t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩).2)⟩
    · exfalso
      apply hsame
      intro q t ht htW
      rcases lt_trichotomy t 0 with hn | he | hp
      · have htW' : -t ∈ Ioo (0 : ℝ) rW := ⟨neg_pos.mpr hn, by
          have := min_le_left rW rB; dsimp [r] at ht; linarith [ht.1]⟩
        exact ((hWneg q (-t) htW').1 (by simpa only [neg_neg] using htW)).elim
      · subst t; exact hSB (mem_range_self q)
      · exact interior_subset (hBneg q t ⟨hp, ht.2.trans_le (min_le_right _ _)⟩).2
  have hfill : range (fun q : X => T (q, 0)) ⊆ interior (W ∪ B) := by
    rintro x ⟨q, rfl⟩
    have hVopen : IsOpen (T.source ∩ (univ ×ˢ Ioo (-r) r)) :=
      T.open_source.inter (isOpen_univ.prod isOpen_Ioo)
    have hOopen : IsOpen (T '' (T.source ∩ (univ ×ˢ Ioo (-r) r))) :=
      T.isOpen_image_of_subset_source hVopen inter_subset_left
    apply mem_interior.mpr
    refine ⟨T '' (T.source ∩ (univ ×ˢ Ioo (-r) r)), ?_, hOopen, ?_⟩
    · rintro y ⟨⟨z, t⟩, ht, rfl⟩
      rcases lt_trichotomy t 0 with hn | he | hp
      · have hs : -t ∈ Ioo (0 : ℝ) r := ⟨neg_pos.mpr hn, by linarith [ht.2.2.1]⟩
        simpa only [neg_neg] using (hhalves z (-t) hs).2
      · subst t
        exact Or.inl (hSW (mem_range_self z))
      · exact (hhalves z t ⟨hp, ht.2.2.2⟩).1
    · exact ⟨(q, 0), ⟨hsource q, mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩
  have hreg : closure (interior (W ∪ B)) = W ∪ B := by
    apply subset_antisymm (closure_minimal interior_subset (hWclosed.union hBclosed))
    rintro x (hx | hx)
    · exact closure_mono (interior_mono subset_union_left) (hW.symm ▸ hx)
    · exact closure_mono (interior_mono subset_union_right) (hB.symm ▸ hx)
  have hfront : frontier (W ∪ B) = R \ B := by
    apply subset_antisymm
    · intro x hx
      have hxR : x ∈ R := by
        rcases frontier_union_subset W B hx with h | h
        · rw [hfrontW] at h
          exact h.1.resolve_left (fun hs => hx.2 (hfill hs))
        · exact (hx.2 (hfill (hfrontB ▸ h.2))).elim
      refine ⟨hxR, ?_⟩
      intro hxB
      have hxBi : x ∈ interior B := by
        by_contra hn
        exact disjoint_left.mp hdis (hfrontB ▸ ⟨subset_closure hxB, hn⟩) hxR
      exact hx.2 (interior_mono subset_union_right hxBi)
    · rintro x ⟨hxR, hxB⟩
      have hxW : x ∈ frontier W := hfrontW.symm ▸ Or.inr hxR
      refine ⟨closure_mono subset_union_left hxW.1, ?_⟩
      intro hxint
      apply hxW.2
      apply mem_interior.mpr
      refine ⟨interior (W ∪ B) ∩ Bᶜ, ?_, isOpen_interior.inter hBclosed.isOpen_compl,
        hxint, hxB⟩
      intro y hy
      exact (interior_subset hy.1).resolve_right hy.2
  exact ⟨hreg, hfront, hfill⟩

theorem frontier_union_of_shared_cylinder_boundary
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : ∀ q : X, (q, 0) ∈ T.source) {W B R : Set Y}
    (hW : closure (interior W) = W) (hB : closure (interior B) = B)
    (hR : IsClosed R)
    (hfrontW : frontier W = range (fun q : X => T (q, 0)) ∪ R)
    (hfrontB : frontier B = range (fun q : X => T (q, 0)))
    (hdis : Disjoint (range (fun q : X => T (q, 0))) R) :
    closure (interior (W ∪ B)) = W ∪ B ∧
      ((frontier (W ∪ B) = R \ B ∧
        range (fun q : X => T (q, 0)) ⊆ interior (W ∪ B)) ∨
      (frontier (W ∪ B) = (R \ B) ∪ range (fun q : X => T (q, 0)) ∧
        range (fun q : X => T (q, 0)) ⊆ frontier (W ∪ B))) := by
  classical
  by_cases ht : (range (fun q : X => T (q, 0)) ∩ closure (W \ B)).Nonempty
  · obtain ⟨hreg, hfront, hfill⟩ :=
      fill_of_shared_cylinder_boundary_of_exterior_accumulation
        T hsource hW hB hR hfrontW hfrontB hdis ht
    exact ⟨hreg, Or.inl ⟨hfront, hfill⟩⟩
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hBclosed : IsClosed B := hB ▸ isClosed_closure
  have hreg : closure (interior (W ∪ B)) = W ∪ B := by
    apply subset_antisymm (closure_minimal interior_subset (hWclosed.union hBclosed))
    rintro x (hx | hx)
    · exact closure_mono (interior_mono subset_union_left) (hW.symm ▸ hx)
    · exact closure_mono (interior_mono subset_union_right) (hB.symm ▸ hx)
  have hkeep : range (fun q : X => T (q, 0)) ⊆ frontier (W ∪ B) := by
    intro x hx
    have hxB : x ∈ frontier B := hfrontB.symm ▸ hx
    refine ⟨closure_mono subset_union_right hxB.1, ?_⟩
    intro hxint
    apply ht
    refine ⟨x, hx, mem_closure_iff.mpr ?_⟩
    intro O hO hxO
    have hxBc : x ∈ closure Bᶜ := by
      rw [closure_compl]
      exact hxB.2
    obtain ⟨y, hyO, hyBc⟩ := mem_closure_iff.mp hxBc
      (O ∩ interior (W ∪ B)) (hO.inter isOpen_interior) ⟨hxO, hxint⟩
    exact ⟨y, hyO.1, (interior_subset hyO.2).resolve_right hyBc, hyBc⟩
  refine ⟨hreg, Or.inr ⟨?_, hkeep⟩⟩
  apply subset_antisymm
  · intro x hx
    rcases frontier_union_subset W B hx with h | h
    · rw [hfrontW] at h
      rcases h.1 with hxS | hxR
      · exact Or.inr hxS
      · left
        refine ⟨hxR, ?_⟩
        intro hxB
        have hxBi : x ∈ interior B := by
          by_contra hn
          exact disjoint_left.mp hdis (hfrontB ▸ ⟨subset_closure hxB, hn⟩) hxR
        exact hx.2 (interior_mono subset_union_right hxBi)
    · exact Or.inr (hfrontB ▸ h.2)
  · rintro x (⟨hxR, hxB⟩ | hxS)
    · have hxW : x ∈ frontier W := hfrontW.symm ▸ Or.inr hxR
      refine ⟨closure_mono subset_union_left hxW.1, ?_⟩
      intro hxint
      apply hxW.2
      apply mem_interior.mpr
      refine ⟨interior (W ∪ B) ∩ Bᶜ, ?_, isOpen_interior.inter hBclosed.isOpen_compl,
        hxint, hxB⟩
      intro y hy
      exact (interior_subset hy.1).resolve_right hy.2
    · exact hkeep hxS

end DifferentialGeometry.Topology

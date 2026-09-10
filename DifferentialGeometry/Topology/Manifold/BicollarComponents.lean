import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

set_option autoImplicit false
open Set
open scoped Topology

namespace Poincare.Topology.ThreeManifold.TwoSidedCollar

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (h : TwoSidedCollar e)


theorem negative_component_ne_positive_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    ConnectedComponents.mk h.negativePoint ≠ ConnectedComponents.mk h.positivePoint := by
  intro hnp
  apply hsep
  rw [isConnected_iff_connectedSpace]
  let _ : Nonempty h.complement := ⟨h.negativePoint⟩
  let _ : PreconnectedSpace h.complement := preconnectedSpace_iff_connectedComponent.mpr (by
    intro y
    apply Set.eq_univ_of_forall
    intro z
    have hy := h.component_eq_negative_or_positive y
    have hz := h.component_eq_negative_or_positive z
    have hzy : ConnectedComponents.mk z = ConnectedComponents.mk y := by
      rcases hz with hz | hz <;> rcases hy with hy | hy
      · exact hz.trans hy.symm
      · exact hz.trans (hnp.trans hy.symm)
      · exact hz.trans (hnp.symm.trans hy.symm)
      · exact hz.trans hy.symm
    rw [← ConnectedComponents.coe_eq_coe.mp hzy]
    exact mem_connectedComponent)
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }


theorem disjoint_negativeSide_positiveSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    Disjoint h.negativeSide h.positiveSide := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hab' : a = b := Subtype.ext hab.symm
  subst b
  have hccne : connectedComponent h.negativePoint ≠ connectedComponent h.positivePoint :=
    ConnectedComponents.coe_ne_coe.mp (h.negative_component_ne_positive_of_disconnected hsep)
  exact Set.disjoint_left.mp (connectedComponent_disjoint hccne) ha hb


theorem compl_negativeSide_union_zeroSlice_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    (h.negativeSide ∪ Set.range e)ᶜ = h.positiveSide := by
  ext x
  constructor
  · intro hx
    have hxZ : x ∉ Set.range e := fun hxe => hx (Or.inr hxe)
    have hxU : x ∈ h.complement := hxZ
    rw [h.complement_eq_negativeSide_union_positiveSide] at hxU
    exact hxU.resolve_left (fun hxn => hx (Or.inl hxn))
  · intro hxp hx
    rcases hx with hxn | hxz
    · exact Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep) hxn hxp
    · exact Set.disjoint_left.mp h.zeroSlice_disjoint_positiveSide hxz hxp


theorem compl_positiveSide_union_zeroSlice_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    (h.positiveSide ∪ Set.range e)ᶜ = h.negativeSide := by
  ext x
  constructor
  · intro hx
    have hxZ : x ∉ Set.range e := fun hxe => hx (Or.inr hxe)
    have hxU : x ∈ h.complement := hxZ
    rw [h.complement_eq_negativeSide_union_positiveSide] at hxU
    exact hxU.resolve_right (fun hxp => hx (Or.inl hxp))
  · intro hxn hx
    rcases hx with hxp | hxz
    · exact Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep) hxn hxp
    · exact Set.disjoint_left.mp h.zeroSlice_disjoint_negativeSide hxz hxn


theorem closure_negativeSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    closure h.negativeSide = h.negativeSide ∪ Set.range e := by
  apply Set.Subset.antisymm
  · apply closure_minimal Set.subset_union_left
    rw [← isOpen_compl_iff, (h.compl_negativeSide_union_zeroSlice_of_disconnected hsep)]
    exact h.isOpen_positiveSide
  · exact Set.union_subset subset_closure h.range_e_subset_closure_negativeSide


theorem closure_positiveSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    closure h.positiveSide = h.positiveSide ∪ Set.range e := by
  apply Set.Subset.antisymm
  · apply closure_minimal Set.subset_union_left
    rw [← isOpen_compl_iff, (h.compl_positiveSide_union_zeroSlice_of_disconnected hsep)]
    exact h.isOpen_negativeSide
  · exact Set.union_subset subset_closure h.range_e_subset_closure_positiveSide


theorem frontier_negativeSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    frontier h.negativeSide = Set.range e := by
  rw [h.isOpen_negativeSide.frontier_eq, (h.closure_negativeSide_of_disconnected hsep)]
  ext x
  constructor
  · rintro ⟨hxn | hxz, hnotn⟩
    · exact (hnotn hxn).elim
    · exact hxz
  · intro hxz
    exact ⟨Or.inr hxz, fun hxn =>
      Set.disjoint_left.mp h.zeroSlice_disjoint_negativeSide hxz hxn⟩


theorem frontier_positiveSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    frontier h.positiveSide = Set.range e := by
  rw [h.isOpen_positiveSide.frontier_eq, (h.closure_positiveSide_of_disconnected hsep)]
  ext x
  constructor
  · rintro ⟨hxp | hxz, hnotp⟩
    · exact (hnotp hxp).elim
    · exact hxz
  · intro hxz
    exact ⟨Or.inr hxz, fun hxp =>
      Set.disjoint_left.mp h.zeroSlice_disjoint_positiveSide hxz hxp⟩


theorem isConnected_negativeSide [Nonempty S] : IsConnected h.negativeSide :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn


theorem isConnected_positiveSide [Nonempty S] : IsConnected h.positiveSide :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

section Separated
variable [CompactSpace S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
  [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement)

include hsep


theorem toFun_mem_negativeSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ h.negativeSide ↔ t < 0 := by
  constructor
  · intro hx
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact ht
    · exact (h.negativeSide_subset_complement hx ⟨s, (h.zero_eq s).symm⟩).elim
    · exact (Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep)
        hx (h.toFun_mem_positiveSide_of_pos s ht)).elim
  · exact h.toFun_mem_negativeSide_of_neg s


theorem toFun_mem_positiveSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ h.positiveSide ↔ 0 < t := by
  constructor
  · intro hx
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact (Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep)
        (h.toFun_mem_negativeSide_of_neg s ht) hx).elim
    · exact (h.positiveSide_subset_complement hx ⟨s, (h.zero_eq s).symm⟩).elim
    · exact ht
  · exact h.toFun_mem_positiveSide_of_pos s


theorem toFun_mem_closure_negativeSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ closure h.negativeSide ↔ t ≤ 0 := by
  rw [h.closure_negativeSide_of_disconnected hsep]
  constructor
  · rintro (hn | hz)
    · exact (h.toFun_mem_negativeSide_iff hsep s t).mp hn |>.le
    · by_contra ht
      exact h.toFun_mem_complement_of_ne_zero s (ne_of_gt (lt_of_not_ge ht)) hz
  · intro ht
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact Or.inl (h.toFun_mem_negativeSide_of_neg s ht)
    · exact Or.inr ⟨s, (h.zero_eq s).symm⟩


theorem toFun_mem_closure_positiveSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ closure h.positiveSide ↔ 0 ≤ t := by
  rw [h.closure_positiveSide_of_disconnected hsep]
  constructor
  · rintro (hp | hz)
    · exact (h.toFun_mem_positiveSide_iff hsep s t).mp hp |>.le
    · by_contra ht
      exact h.toFun_mem_complement_of_ne_zero s (ne_of_lt (lt_of_not_ge ht)) hz
  · intro ht
    rcases lt_or_eq_of_le ht with ht | ht
    · exact Or.inl (h.toFun_mem_positiveSide_of_pos s ht)
    · subst t
      exact Or.inr ⟨s, (h.zero_eq s).symm⟩


theorem closure_negativeSide_inter_closure_positiveSide :
    closure h.negativeSide ∩ closure h.positiveSide = Set.range e := by
  rw [h.closure_negativeSide_of_disconnected hsep,
    h.closure_positiveSide_of_disconnected hsep]
  ext x
  constructor
  · rintro ⟨hn | hz, hp | hz'⟩
    · exact (Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep)
        hn hp).elim
    · exact hz'
    · exact hz
    · exact hz
  · intro hz
    exact ⟨Or.inr hz, Or.inr hz⟩


theorem closure_negativeSide_union_closure_positiveSide :
    closure h.negativeSide ∪ closure h.positiveSide = Set.univ := by
  rw [h.closure_negativeSide_of_disconnected hsep,
    h.closure_positiveSide_of_disconnected hsep]
  have := h.complement_union_zeroSlice
  rw [h.complement_eq_negativeSide_union_positiveSide] at this
  convert this using 1
  ext x
  simp only [mem_union]
  tauto

def negativeHalfCollar (q : S × Set.Iic (0 : ℝ)) : closure h.negativeSide :=
  ⟨h.toFun (q.1, q.2), (h.toFun_mem_closure_negativeSide_iff hsep q.1 q.2).mpr q.2.2⟩


@[simp]
theorem negativeHalfCollar_coe (q : S × Set.Iic (0 : ℝ)) :
    (h.negativeHalfCollar hsep q : X) = h.toFun (q.1, q.2) := rfl

theorem range_negativeHalfCollar :
    Set.range (h.negativeHalfCollar hsep) =
      Subtype.val ⁻¹' h.range := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q.1, q.2), rfl⟩
  · rintro ⟨p, hp⟩
    have ht : p.2 ≤ 0 := (h.toFun_mem_closure_negativeSide_iff hsep p.1 p.2).mp
      (hp.symm ▸ x.2)
    exact ⟨(p.1, ⟨p.2, ht⟩), Subtype.ext hp⟩


theorem isOpenEmbedding_negativeHalfCollar :
    Topology.IsOpenEmbedding (h.negativeHalfCollar hsep) := by
  have hi : Topology.IsEmbedding (fun q : S × Set.Iic (0 : ℝ) ↦
      h.toFun (q.1, q.2)) :=
    h.isOpenEmbedding_toFun.isEmbedding.comp
      (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
  refine ⟨hi.codRestrict _ _, ?_⟩
  rw [h.range_negativeHalfCollar hsep]
  exact h.isOpen_range.preimage continuous_subtype_val

noncomputable def negativeHalfCollarHomeomorph :
    S × Set.Iic (0 : ℝ) ≃ₜ Set.range (h.negativeHalfCollar hsep) :=
  (h.isOpenEmbedding_negativeHalfCollar hsep).isEmbedding.toHomeomorph


theorem negativeHalfCollar_zero (s : S) :
    (h.negativeHalfCollar hsep (s, ⟨0, by simp⟩) : X) = e s := h.zero_eq s

def positiveHalfCollar (q : S × Set.Ici (0 : ℝ)) : closure h.positiveSide :=
  ⟨h.toFun (q.1, q.2), (h.toFun_mem_closure_positiveSide_iff hsep q.1 q.2).mpr q.2.2⟩


@[simp]
theorem positiveHalfCollar_coe (q : S × Set.Ici (0 : ℝ)) :
    (h.positiveHalfCollar hsep q : X) = h.toFun (q.1, q.2) := rfl

theorem range_positiveHalfCollar :
    Set.range (h.positiveHalfCollar hsep) =
      Subtype.val ⁻¹' h.range := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q.1, q.2), rfl⟩
  · rintro ⟨p, hp⟩
    have ht : 0 ≤ p.2 := (h.toFun_mem_closure_positiveSide_iff hsep p.1 p.2).mp
      (hp.symm ▸ x.2)
    exact ⟨(p.1, ⟨p.2, ht⟩), Subtype.ext hp⟩


theorem isOpenEmbedding_positiveHalfCollar :
    Topology.IsOpenEmbedding (h.positiveHalfCollar hsep) := by
  have hi : Topology.IsEmbedding (fun q : S × Set.Ici (0 : ℝ) ↦
      h.toFun (q.1, q.2)) :=
    h.isOpenEmbedding_toFun.isEmbedding.comp
      (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
  refine ⟨hi.codRestrict _ _, ?_⟩
  rw [h.range_positiveHalfCollar hsep]
  exact h.isOpen_range.preimage continuous_subtype_val

noncomputable def positiveHalfCollarHomeomorph :
    S × Set.Ici (0 : ℝ) ≃ₜ Set.range (h.positiveHalfCollar hsep) :=
  (h.isOpenEmbedding_positiveHalfCollar hsep).isEmbedding.toHomeomorph


theorem positiveHalfCollar_zero (s : S) :
    (h.positiveHalfCollar hsep (s, ⟨0, by simp⟩) : X) = e s := h.zero_eq s


theorem interior_closure_negativeSide :
    interior (closure h.negativeSide) = h.negativeSide := by
  rw [interior_eq_compl_closure_compl, h.closure_negativeSide_of_disconnected hsep,
    h.compl_negativeSide_union_zeroSlice_of_disconnected hsep,
    h.closure_positiveSide_of_disconnected hsep,
    h.compl_positiveSide_union_zeroSlice_of_disconnected hsep]


theorem interior_closure_positiveSide :
    interior (closure h.positiveSide) = h.positiveSide := by
  rw [interior_eq_compl_closure_compl, h.closure_positiveSide_of_disconnected hsep,
    h.compl_positiveSide_union_zeroSlice_of_disconnected hsep,
    h.closure_negativeSide_of_disconnected hsep,
    h.compl_negativeSide_union_zeroSlice_of_disconnected hsep]


theorem frontier_closure_negativeSide :
    frontier (closure h.negativeSide) = Set.range e := by
  rw [frontier, closure_closure, h.interior_closure_negativeSide hsep]
  rw [← h.isOpen_negativeSide.frontier_eq]
  exact h.frontier_negativeSide_of_disconnected hsep


theorem frontier_closure_positiveSide :
    frontier (closure h.positiveSide) = Set.range e := by
  rw [frontier, closure_closure, h.interior_closure_positiveSide hsep]
  rw [← h.isOpen_positiveSide.frontier_eq]
  exact h.frontier_positiveSide_of_disconnected hsep

noncomputable def negativeFrontierHomeomorph :
    S ≃ₜ frontier (closure h.negativeSide) :=
  (h.continuous_e.isClosedEmbedding h.injective_e).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (h.frontier_closure_negativeSide hsep).symm)


@[simp]
theorem negativeFrontierHomeomorph_coe (s : S) :
    (h.negativeFrontierHomeomorph hsep s : X) = e s := rfl

noncomputable def positiveFrontierHomeomorph :
    S ≃ₜ frontier (closure h.positiveSide) :=
  (h.continuous_e.isClosedEmbedding h.injective_e).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (h.frontier_closure_positiveSide hsep).symm)


@[simp]
theorem positiveFrontierHomeomorph_coe (s : S) :
    (h.positiveFrontierHomeomorph hsep s : X) = e s := rfl

end Separated


theorem isCompact_closure_negativeSide [Nonempty S] [CompactSpace X] :
    IsCompact (closure h.negativeSide) := isClosed_closure.isCompact


theorem isCompact_closure_positiveSide [Nonempty S] [CompactSpace X] :
    IsCompact (closure h.positiveSide) := isClosed_closure.isCompact

end Poincare.Topology.ThreeManifold.TwoSidedCollar

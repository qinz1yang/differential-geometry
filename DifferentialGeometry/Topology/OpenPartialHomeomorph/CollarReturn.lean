import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarAdvance
import DifferentialGeometry.Topology.Connected.InteriorUnion

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [PreconnectedSpace X] [TopologicalSpace Y] [T2Space Y]

theorem frontier_union_closed_cylinder_of_inter_eq_boundary
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W S : Set Y}
    (hW : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W =
      (A '' (univ ×ˢ ({a} : Set ℝ))) ∪ (A '' (univ ×ˢ ({b} : Set ℝ))) ∪ S)
    (havoid : Disjoint S (A '' (univ ×ˢ Icc a b)))
    (hinter : (A '' (univ ×ˢ Icc a b)) ∩ W =
      (A '' (univ ×ˢ ({a} : Set ℝ))) ∪ (A '' (univ ×ˢ ({b} : Set ℝ)))) :
    closure (interior (W ∪ A '' (univ ×ˢ Icc a b))) = W ∪ A '' (univ ×ˢ Icc a b) ∧
      frontier (W ∪ A '' (univ ×ˢ Icc a b)) = S := by
  let B := A '' (univ ×ˢ Icc a b)
  let L := A '' (univ ×ˢ ({a} : Set ℝ))
  let U := A '' (univ ×ˢ ({b} : Set ℝ))
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hBclosed : IsClosed B :=
    ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (A.continuousOn.mono hsource)).isClosed
  have hLsrc : univ ×ˢ ({a} : Set ℝ) ⊆ A.source :=
    (prod_mono Subset.rfl (by
      intro t ht
      have he : t = a := ht
      subst t
      exact ⟨le_rfl, hab.le⟩)).trans hsource
  have hUsrc : univ ×ˢ ({b} : Set ℝ) ⊆ A.source :=
    (prod_mono Subset.rfl (by
      intro t ht
      have he : t = b := ht
      subst t
      exact ⟨hab.le, le_rfl⟩)).trans hsource
  have hLclosed : IsClosed L :=
    ((isCompact_univ.prod (isCompact_singleton : IsCompact ({a} : Set ℝ))).image_of_continuousOn
      (A.continuousOn.mono hLsrc)).isClosed
  have hUclosed : IsClosed U :=
    ((isCompact_univ.prod (isCompact_singleton : IsCompact ({b} : Set ℝ))).image_of_continuousOn
      (A.continuousOn.mono hUsrc)).isClosed
  have hBL : L ⊆ B := image_mono (prod_mono Subset.rfl (by
    intro t ht; have he : t = a := ht; subst t; exact ⟨le_rfl, hab.le⟩))
  have hBU : U ⊆ B := image_mono (prod_mono Subset.rfl (by
    intro t ht; have he : t = b := ht; subst t; exact ⟨hab.le, le_rfl⟩))
  have hLUdisj : Disjoint L U := by
    apply disjoint_left.mpr
    rintro y ⟨⟨q, t⟩, ht, heq⟩ ⟨⟨q', t'⟩, ht', heq'⟩
    have he := congrArg Prod.snd (A.injOn (hLsrc ht) (hUsrc ht') (heq.trans heq'.symm))
    have hta : t = a := ht.2
    have htb : t' = b := ht'.2
    exact hab.ne (hta.symm.trans (he.trans htb))
  have hLW : L ⊆ W := fun y hy => hWclosed.frontier_subset (hfront.symm ▸ Or.inl (Or.inl hy))
  have hUW : U ⊆ W := fun y hy => hWclosed.frontier_subset (hfront.symm ▸ Or.inl (Or.inr hy))
  have hBfront : frontier B = L ∪ U := by
    change frontier (A '' (univ ×ˢ Icc a b)) = _
    rw [← A.image_frontier_of_subset_source hsource
      (isClosed_univ.prod isClosed_Icc) hBclosed, frontier_univ_prod_eq,
      frontier_Icc hab.le]
    rw [show ({a, b} : Set ℝ) = {a} ∪ {b} by ext; simp [or_comm]]
    rw [prod_union, image_union]
  have hdisj : Disjoint (interior B) (interior W) := by
    apply disjoint_left.mpr
    intro y hyB hyW
    have hy : y ∈ B ∩ W := ⟨interior_subset hyB, interior_subset hyW⟩
    have hyF : y ∈ frontier B := hBfront.symm ▸ (hinter ▸ hy)
    exact hyF.2 hyB
  have hBreg : closure (interior B) = B := by
    apply A.closure_interior_image_of_subset_source hsource _ hBclosed
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
      closure_univ, closure_Ioo hab.ne]
  have hreg : closure (interior (W ∪ B)) = W ∪ B := by
    apply subset_antisymm (closure_minimal interior_subset (hWclosed.union hBclosed))
    rintro y (hy | hy)
    · exact closure_mono (interior_mono subset_union_left) (hW.symm ▸ hy)
    · exact closure_mono (interior_mono subset_union_right) (hBreg.symm ▸ hy)
  have hLfill : L ⊆ interior (B ∪ W) := by
    apply A.image_lower_boundary_subset_interior_union hab hsource hW (hUclosed.union hS)
      hdisj hLW
    · intro y hy
      rcases hfront ▸ hy with (hyL | hyU) | hyS
      · exact Or.inl hyL
      · exact Or.inr (Or.inl hyU)
      · exact Or.inr (Or.inr hyS)
    · exact hLUdisj.union_right ((havoid.mono_right hBL).symm)
  have hUfill : U ⊆ interior (B ∪ W) := by
    apply A.image_upper_boundary_subset_interior_union hab hsource hW (hLclosed.union hS)
      hdisj hUW
    · intro y hy
      rcases hfront ▸ hy with (hyL | hyU) | hyS
      · exact Or.inr (Or.inl hyL)
      · exact Or.inl hyU
      · exact Or.inr (Or.inr hyS)
    · exact hLUdisj.symm.union_right ((havoid.mono_right hBU).symm)
  have hnewfront : frontier (W ∪ B) = S := by
    apply subset_antisymm
    · intro y hy
      have hy' : y ∈ frontier (B ∪ W) := by simpa only [union_comm] using hy
      rcases frontier_union_subset B W hy' with hleft | hright
      · rw [hBfront] at hleft
        exact (hy'.2 (hleft.1.elim (fun h => hLfill h) (fun h => hUfill h))).elim
      · rw [hfront] at hright
        rcases hright.2 with (hyL | hyU) | hyS
        · exact (hy'.2 (hLfill hyL)).elim
        · exact (hy'.2 (hUfill hyU)).elim
        · exact hyS
    · intro y hyS
      have hyW : y ∈ frontier W := hfront.symm ▸ Or.inr hyS
      have hyB : y ∉ B := fun hyB => disjoint_left.mp havoid hyS hyB
      refine ⟨closure_mono subset_union_left hyW.1, ?_⟩
      intro hyint
      apply hyW.2
      apply mem_interior.mpr
      refine ⟨interior (W ∪ B) ∩ Bᶜ, ?_, isOpen_interior.inter hBclosed.isOpen_compl, hyint, hyB⟩
      intro z hz
      exact (interior_subset hz.1).resolve_right hz.2
  exact ⟨hreg, hnewfront⟩

private theorem cylinder_interior_properties
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) :
    closure (interior (A '' (univ ×ˢ Icc a b))) = A '' (univ ×ˢ Icc a b) ∧
      IsPreconnected (interior (A '' (univ ×ˢ Icc a b))) := by
  have hBclosed : IsClosed (A '' (univ ×ˢ Icc a b)) :=
    ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (A.continuousOn.mono hsource)).isClosed
  have hreg : closure (interior (A '' (univ ×ˢ Icc a b))) =
      A '' (univ ×ˢ Icc a b) := by
    apply A.closure_interior_image_of_subset_source hsource _ hBclosed
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
      closure_univ, closure_Ioo hab.ne]
  refine ⟨hreg, ?_⟩
  rw [← A.image_interior_of_subset_source hsource, interior_prod_eq,
    interior_univ, interior_Icc]
  exact (isPreconnected_univ.prod isPreconnected_Ioo).image A
    (A.continuousOn.mono ((prod_mono Subset.rfl Ioo_subset_Icc_self).trans hsource))

theorem closed_cylinder_advance_subset_closure_component
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W S : Set Y}
    (hW : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = A '' (univ ×ˢ ({a} : Set ℝ)) ∪ S)
    (havoid : Disjoint S (A '' (univ ×ˢ Icc a b)))
    (hseed : (A '' (univ ×ˢ Ioo a b) ∩ Wᶜ).Nonempty)
    (x : Y) (hincident : (A '' (univ ×ˢ ({a} : Set ℝ)) ∩
      closure (connectedComponentIn (interior W) x)).Nonempty) :
    A '' (univ ×ˢ Icc a b) ⊆
      closure (connectedComponentIn (interior (W ∪ A '' (univ ×ˢ Icc a b))) x) := by
  obtain ⟨hinter, _, _⟩ := A.closed_cylinder_advance hab hsource hW hS hfront havoid hseed
  have hBfront : frontier (A '' (univ ×ˢ Icc a b)) =
      A '' (univ ×ˢ ({a} : Set ℝ)) ∪ A '' (univ ×ˢ ({b} : Set ℝ)) := by
    have hBclosed : IsClosed (A '' (univ ×ˢ Icc a b)) :=
      ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
        (A.continuousOn.mono hsource)).isClosed
    rw [← A.image_frontier_of_subset_source hsource
      (isClosed_univ.prod isClosed_Icc) hBclosed, frontier_univ_prod_eq, frontier_Icc hab.le]
    rw [show ({a, b} : Set ℝ) = {a} ∪ {b} by ext; simp [or_comm], prod_union, image_union]
  have hdisj : Disjoint (interior (A '' (univ ×ˢ Icc a b))) (interior W) := by
    rw [disjoint_left]
    intro z hzB hzW
    have hzF : z ∈ frontier (A '' (univ ×ˢ Icc a b)) :=
      hBfront.symm ▸ Or.inl (hinter ▸ ⟨interior_subset hzB, interior_subset hzW⟩)
    exact hzF.2 hzB
  have hlow : A '' (univ ×ˢ ({a} : Set ℝ)) ⊆ A '' (univ ×ˢ Icc a b) :=
    image_mono (prod_mono Subset.rfl (by
      intro t ht; have ht' : t = a := ht; subst t; exact ⟨le_rfl, hab.le⟩))
  have hfill : A '' (univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (W ∪ A '' (univ ×ˢ Icc a b)) := by
    rw [union_comm]
    exact A.image_lower_boundary_subset_interior_union hab hsource hW hS hdisj
      (fun z hz => (hW ▸ isClosed_closure).frontier_subset (hfront.symm ▸ Or.inl hz))
      hfront.le (havoid.mono_right hlow).symm
  obtain ⟨hBreg, hBconn⟩ := cylinder_interior_properties A hab hsource
  apply DifferentialGeometry.Topology.subset_closure_connectedComponentIn_interior_union_of_incident_component
    hBreg.symm.subset hBconn
  obtain ⟨p, hpL, hpC⟩ := hincident
  exact ⟨p, ⟨hpC, hBreg.symm ▸ hlow hpL⟩, hfill hpL⟩

theorem connectedComponentIn_interior_union_closed_cylinder_eq
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W S : Set Y}
    (hW : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W =
      (A '' (univ ×ˢ ({a} : Set ℝ))) ∪ (A '' (univ ×ˢ ({b} : Set ℝ))) ∪ S)
    (havoid : Disjoint S (A '' (univ ×ˢ Icc a b)))
    (hinter : (A '' (univ ×ˢ Icc a b)) ∩ W =
      (A '' (univ ×ˢ ({a} : Set ℝ))) ∪ (A '' (univ ×ˢ ({b} : Set ℝ))))
    (x y : Y)
    (hx : (A '' (univ ×ˢ ({a} : Set ℝ)) ∩
      closure (connectedComponentIn (interior W) x)).Nonempty)
    (hy : (A '' (univ ×ˢ ({b} : Set ℝ)) ∩
      closure (connectedComponentIn (interior W) y)).Nonempty) :
    connectedComponentIn (interior (W ∪ A '' (univ ×ˢ Icc a b))) x =
      connectedComponentIn (interior (W ∪ A '' (univ ×ˢ Icc a b))) y := by
  obtain ⟨_, hfrontV⟩ := A.frontier_union_closed_cylinder_of_inter_eq_boundary
    hab hsource hW hS hfront havoid hinter
  obtain ⟨hBreg, hBconn⟩ := cylinder_interior_properties A hab hsource
  have hfill : A '' (univ ×ˢ Icc a b) ⊆ interior (W ∪ A '' (univ ×ˢ Icc a b)) := by
    intro z hz
    by_contra hn
    have hzF : z ∈ frontier (W ∪ A '' (univ ×ˢ Icc a b)) :=
      ⟨subset_closure (Or.inr hz), hn⟩
    exact disjoint_left.mp havoid (hfrontV ▸ hzF) hz
  apply DifferentialGeometry.Topology.connectedComponentIn_interior_union_eq_of_incident_components hBconn
  · obtain ⟨p, hpL, hpC⟩ := hx
    have hpB : p ∈ A '' (univ ×ˢ Icc a b) := by
      apply image_mono (prod_mono Subset.rfl ?_) hpL
      intro t ht; have ht' : t = a := ht; subst t; exact ⟨le_rfl, hab.le⟩
    exact ⟨p, ⟨hpC, hBreg.symm ▸ hpB⟩, hfill hpB⟩
  · obtain ⟨p, hpU, hpC⟩ := hy
    have hpB : p ∈ A '' (univ ×ˢ Icc a b) := by
      apply image_mono (prod_mono Subset.rfl ?_) hpU
      intro t ht; have ht' : t = b := ht; subst t; exact ⟨hab.le, le_rfl⟩
    exact ⟨p, ⟨hpC, hBreg.symm ▸ hpB⟩, hfill hpB⟩

end OpenPartialHomeomorph

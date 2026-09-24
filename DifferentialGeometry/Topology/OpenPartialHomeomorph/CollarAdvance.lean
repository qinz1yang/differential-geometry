import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarUnion
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

noncomputable section

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [PreconnectedSpace X] [TopologicalSpace Y] [T2Space Y]

theorem image_lower_boundary_subset_interior_union
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W S : Set Y}
    (hW : closure (interior W) = W) (hS : IsClosed S)
    (hdisj : Disjoint (interior (A '' (univ ×ˢ Icc a b))) (interior W))
    (hWlower : A '' (univ ×ˢ ({a} : Set ℝ)) ⊆ W)
    (hfront : frontier W ⊆ A '' (univ ×ˢ ({a} : Set ℝ)) ∪ S)
    (hSdisj : Disjoint (A '' (univ ×ˢ ({a} : Set ℝ))) S) :
    A '' (univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (A '' (univ ×ˢ Icc a b) ∪ W) := by
  let R : X × ℝ ≃ₜ X × ℝ := (Homeomorph.refl X).prodCongr (Homeomorph.neg ℝ)
  let A' : OpenPartialHomeomorph (X × ℝ) Y := R.transOpenPartialHomeomorph A
  have happ (x : X) (t : ℝ) : A' (x, t) = A (x, -t) := by rfl
  have hsource' : univ ×ˢ Icc (-b) (-a) ⊆ A'.source := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change (x, -t) ∈ A.source
    exact hsource ⟨hx, by change a ≤ -t ∧ -t ≤ b; constructor <;> linarith [ht.1, ht.2]⟩
  have hband : A' '' (univ ×ˢ Icc (-b) (-a)) = A '' (univ ×ˢ Icc a b) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨(x, -t), ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩, (happ x t).symm⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨(x, -t), ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
      rw [happ, neg_neg]
  have hface : A' '' (univ ×ˢ ({-a} : Set ℝ)) = A '' (univ ×ˢ ({a} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = -a := ht
      subst t
      refine ⟨(x, a), ⟨hx, rfl⟩, ?_⟩
      rw [happ, neg_neg]
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = a := ht
      subst t
      refine ⟨(x, -a), ⟨hx, rfl⟩, ?_⟩
      rw [happ, neg_neg]
  have h := A'.image_upper_boundary_subset_interior_union (neg_lt_neg hab)
    hsource' hW hS (by rwa [hband]) (by rwa [hface]) (by rwa [hface]) (by rwa [hface])
  rwa [hface, hband] at h

omit [T2Space Y] in
private theorem frontier_union_of_mem_frontier_of_not_mem
    {A B : Set Y} (hB : IsClosed B) {x : Y} (hx : x ∈ frontier A) (hxB : x ∉ B) :
    x ∈ frontier (A ∪ B) := by
  refine ⟨closure_mono subset_union_left hx.1, ?_⟩
  intro hint
  apply hx.2
  apply mem_interior.mpr
  refine ⟨interior (A ∪ B) ∩ Bᶜ, ?_, isOpen_interior.inter hB.isOpen_compl, hint, hxB⟩
  intro y hy
  exact (interior_subset hy.1).resolve_right hy.2

theorem closed_cylinder_advance
    (A : OpenPartialHomeomorph (X × ℝ) Y) {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ A.source) {W S : Set Y}
    (hW : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = A '' (univ ×ˢ ({a} : Set ℝ)) ∪ S)
    (havoid : Disjoint S (A '' (univ ×ˢ Icc a b)))
    (hseed : (A '' (univ ×ˢ Ioo a b) ∩ Wᶜ).Nonempty) :
    (A '' (univ ×ˢ Icc a b)) ∩ W = A '' (univ ×ˢ ({a} : Set ℝ)) ∧
      closure (interior ((A '' (univ ×ˢ Icc a b)) ∪ W)) =
        (A '' (univ ×ˢ Icc a b)) ∪ W ∧
      frontier ((A '' (univ ×ˢ Icc a b)) ∪ W) =
        S ∪ A '' (univ ×ˢ ({b} : Set ℝ)) := by
  let B := A '' (univ ×ˢ Icc a b)
  let L := A '' (univ ×ˢ ({a} : Set ℝ))
  let U := A '' (univ ×ˢ ({b} : Set ℝ))
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hBclosed : IsClosed B :=
    ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (A.continuousOn.mono hsource)).isClosed
  have hBL : L ⊆ B := image_mono (prod_mono Subset.rfl (by
    intro t ht
    have ht' : t = a := ht
    subst t
    exact ⟨le_rfl, hab.le⟩))
  have hBU : U ⊆ B := image_mono (prod_mono Subset.rfl (by
    intro t ht
    have ht' : t = b := ht
    subst t
    exact ⟨hab.le, le_rfl⟩))
  have hLW : L ⊆ W := fun x hx => hWclosed.frontier_subset (hfront.symm ▸ Or.inl hx)
  have hbandSource : univ ×ˢ Ioc a b ⊆ A.source :=
    (prod_mono Subset.rfl Ioc_subset_Icc_self).trans hsource
  have hconn : IsPreconnected (A '' (univ ×ˢ Ioc a b)) :=
    (isPreconnected_univ.prod isPreconnected_Ioc).image _ (A.continuousOn.mono hbandSource)
  have hbandDisj : Disjoint (A '' (univ ×ˢ Ioc a b)) (frontier W) := by
    apply disjoint_left.mpr
    rintro y ⟨⟨x, t⟩, ht, rfl⟩ hy
    rw [hfront] at hy
    rcases hy with ⟨⟨z, r⟩, hr, heq⟩ | hyS
    · have heq' := A.injOn (hsource ⟨hr.1, by
        have hr' : r = a := hr.2
        rw [hr']; exact ⟨le_rfl, hab.le⟩⟩) (hbandSource ht) heq
      have hrt := congrArg Prod.snd heq'
      have hr' : r = a := hr.2
      linarith [ht.2.1]
    · exact disjoint_left.mp havoid hyS ⟨(x, t), ⟨ht.1, ht.2.1.le, ht.2.2⟩, rfl⟩
  have hseed' : ((A '' (univ ×ˢ Ioc a b)) ∩ interior Wᶜ).Nonempty := by
    obtain ⟨x, hx, hxW⟩ := hseed
    exact ⟨x, image_mono (prod_mono Subset.rfl Ioo_subset_Ioc_self) hx,
      hWclosed.isOpen_compl.interior_eq.symm ▸ hxW⟩
  have hbandOut : A '' (univ ×ˢ Ioc a b) ⊆ Wᶜ := by
    have hdisj : Disjoint (A '' (univ ×ˢ Ioc a b)) (frontier Wᶜ) := by
      rwa [frontier_compl]
    exact (DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hconn hdisj hseed').trans interior_subset
  have hinter : B ∩ W = L := by
    apply subset_antisymm
    · rintro y ⟨⟨⟨x, t⟩, ht, rfl⟩, hyW⟩
      have hta : t = a := by
        by_contra hne
        exact hbandOut ⟨(x, t), ⟨ht.1, lt_of_le_of_ne ht.2.1 (Ne.symm hne), ht.2.2⟩,
          rfl⟩ hyW
      exact ⟨(x, t), ⟨ht.1, hta⟩, rfl⟩
    · exact fun y hy => ⟨hBL hy, hLW hy⟩
  have hBint : interior B = A '' (univ ×ˢ Ioo a b) := by
    change interior (A '' (univ ×ˢ Icc a b)) = _
    rw [← A.image_interior_of_subset_source hsource, interior_prod_eq,
      interior_univ, interior_Icc]
  have hBreg : closure (interior B) = B := by
    apply A.closure_interior_image_of_subset_source hsource _ hBclosed
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
      closure_univ, closure_Ioo hab.ne]
  have hreg : closure (interior (B ∪ W)) = B ∪ W := by
    apply subset_antisymm (closure_minimal interior_subset (hBclosed.union hWclosed))
    rintro y (hy | hy)
    · exact closure_mono (interior_mono subset_union_left) (hBreg.symm ▸ hy)
    · exact closure_mono (interior_mono subset_union_right) (hW.symm ▸ hy)
  have hfill : L ⊆ interior (B ∪ W) := by
    apply A.image_lower_boundary_subset_interior_union hab hsource hW hS
    · rw [hBint]
      exact disjoint_left.mpr fun y hy hyW =>
        hbandOut (image_mono (prod_mono Subset.rfl Ioo_subset_Ioc_self) hy)
          (interior_subset hyW)
    · exact hLW
    · exact hfront.le
    · exact (havoid.mono_right hBL).symm
  have hBfront : frontier B = L ∪ U := by
    change frontier (A '' (univ ×ˢ Icc a b)) = _
    rw [← A.image_frontier_of_subset_source hsource
      (isClosed_univ.prod isClosed_Icc) hBclosed, frontier_univ_prod_eq,
      frontier_Icc hab.le]
    rw [show ({a, b} : Set ℝ) = {a} ∪ {b} by ext; simp [or_comm]]
    rw [prod_union, image_union]
  have hUout : U ⊆ Wᶜ := by
    apply Subset.trans _ hbandOut
    apply image_mono
    exact prod_mono Subset.rfl (by intro t ht; have ht' : t = b := ht; subst t; exact ⟨hab, le_rfl⟩)
  have hnewfront : frontier (B ∪ W) = S ∪ U := by
    apply subset_antisymm
    · intro y hy
      rcases frontier_union_subset B W hy with hleft | hright
      · rw [hBfront] at hleft
        rcases hleft.1 with hyL | hyU
        · exact (hy.2 (hfill hyL)).elim
        · exact Or.inr hyU
      · rw [hfront] at hright
        rcases hright.2 with hyL | hyS
        · exact (hy.2 (hfill hyL)).elim
        · exact Or.inl hyS
    · rintro y (hyS | hyU)
      · have hyW : y ∈ frontier W := hfront.symm ▸ Or.inr hyS
        have hyB : y ∉ B := fun hyB => disjoint_left.mp havoid hyS hyB
        simpa only [union_comm W B] using
          frontier_union_of_mem_frontier_of_not_mem hBclosed hyW hyB
      · exact frontier_union_of_mem_frontier_of_not_mem hWclosed
          (hBfront.symm ▸ Or.inr hyU) (hUout hyU)
  exact ⟨hinter, hreg, hnewfront⟩

end OpenPartialHomeomorph

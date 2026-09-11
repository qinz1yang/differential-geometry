import Mathlib.Topology.Connected.Clopen
import DifferentialGeometry.Topology.SphereSeparation.Bicollar

set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation


def sliceDomain {a : ℝ} (c : AxialInterval a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ {c}


def sliceImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) : Set N :=
  Φ '' sliceDomain c


def lowerHalfDomain {a : ℝ} (c : AxialInterval a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ Iio c


def lowerHalfImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) : Set N :=
  Φ '' lowerHalfDomain c


def upperHalfDomain {a : ℝ} (c : AxialInterval a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ Ioi c


def upperHalfImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) : Set N :=
  Φ '' upperHalfDomain c


def axialReflection (a : ℝ) : AxialInterval a ≃ₜ AxialInterval a where
  toEquiv :=
    { toFun := fun r => ⟨-r.1, by
        constructor
        · simpa using neg_lt_neg r.2.2
        · simpa using neg_lt_neg r.2.1⟩
      invFun := fun r => ⟨-r.1, by
        constructor
        · simpa using neg_lt_neg r.2.2
        · simpa using neg_lt_neg r.2.1⟩
      left_inv := by intro r; exact Subtype.ext (neg_neg r.1)
      right_inv := by intro r; exact Subtype.ext (neg_neg r.1) }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


def reverseAxialSource (a : ℝ) :
    SphereTwo × AxialInterval a ≃ₜ SphereTwo × AxialInterval a :=
  Homeomorph.prodCongr (Homeomorph.refl SphereTwo) (axialReflection a)

theorem reverseAxialSource_image_lowerHalfDomain {a : ℝ}
    (c : AxialInterval a) :
    reverseAxialSource a '' lowerHalfDomain c =
      upperHalfDomain (axialReflection a c) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Set.mem_univ _, by
      change -(c : ℝ) < -(q.2 : ℝ)
      exact neg_lt_neg hq.2⟩
  · intro hp
    refine ⟨reverseAxialSource a p, ?_, ?_⟩
    · exact ⟨Set.mem_univ _, by
        have hp' : -(c : ℝ) < (p.2 : ℝ) := hp.2
        change -(p.2 : ℝ) < (c : ℝ)
        linarith⟩
    · apply Prod.ext
      · rfl
      · exact Subtype.ext (neg_neg p.2.1)


theorem reverseAxialSource_image_upperHalfDomain {a : ℝ}
    (c : AxialInterval a) :
    reverseAxialSource a '' upperHalfDomain c =
      lowerHalfDomain (axialReflection a c) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Set.mem_univ _, by
      change -(q.2 : ℝ) < -(c : ℝ)
      exact neg_lt_neg hq.2⟩
  · intro hp
    refine ⟨reverseAxialSource a p, ?_, ?_⟩
    · exact ⟨Set.mem_univ _, by
        have hp' : (p.2 : ℝ) < -(c : ℝ) := hp.2
        change (c : ℝ) < -(p.2 : ℝ)
        linarith⟩
    · apply Prod.ext
      · rfl
      · exact Subtype.ext (neg_neg p.2.1)


def halfOpenSlabDomain {a : ℝ} (s t : AxialInterval a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ Ico s t


def halfOpenSlabImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (s t : AxialInterval a) : Set N :=
  Φ '' halfOpenSlabDomain s t


def closedSlabDomain {a : ℝ} (s t : AxialInterval a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ Icc s t


def closedSlabImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (s t : AxialInterval a) : Set N :=
  Φ '' closedSlabDomain s t

theorem closedSlabImage_eq_halfOpen_union_slice
    {N : Type*} {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    {s t : AxialInterval a} (hst : s < t) :
    closedSlabImage Φ s t = halfOpenSlabImage Φ s t ∪ sliceImage Φ t := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases lt_or_eq_of_le hp.2.2 with hpt | hpt
    · exact Or.inl ⟨p, ⟨hp.1, hp.2.1, hpt⟩, rfl⟩
    · exact Or.inr ⟨p, ⟨hp.1, hpt⟩, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, ⟨hp.1, hp.2.1, hp.2.2.le⟩, rfl⟩
    · exact ⟨p, ⟨hp.1, hp.2 ▸ hst.le, hp.2 ▸ le_rfl⟩, rfl⟩

structure IsAxiallyOriented {N : Type*} [TopologicalSpace N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N)
    (d : ∀ c, SphereSides (sliceImage Φ c)) : Prop where
  lower_subset_compact : ∀ c, lowerHalfImage Φ c ⊆ (d c).compactSide
  upper_subset_end : ∀ c, upperHalfImage Φ c ⊆ (d c).endSide

namespace IsAxiallyOriented

variable {N : Type*} [TopologicalSpace N] {a : ℝ}
  {Φ : SphereTwo × AxialInterval a → N}
  {d : ∀ c, SphereSides (sliceImage Φ c)}

theorem at_zero (o : IsAxiallyOriented Φ d) (ha : 0 < a) :
    negativeHalfImage Φ ha ⊆ (d (axialZero ha)).compactSide ∧
      positiveHalfImage Φ ha ⊆ (d (axialZero ha)).endSide := by
  exact ⟨o.lower_subset_compact (axialZero ha),
    o.upper_subset_end (axialZero ha)⟩

omit [TopologicalSpace N] in
private theorem sliceImage_nonempty (c : AxialInterval a) :
    (sliceImage Φ c).Nonempty := by
  obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
  exact ⟨Φ (p, c), ⟨(p, c), ⟨hp, rfl⟩, rfl⟩⟩

omit [TopologicalSpace N] in
private theorem slice_subset_lower {s t : AxialInterval a} (h : s < t) :
    sliceImage Φ s ⊆ lowerHalfImage Φ t := by
  rintro y ⟨p, hp, rfl⟩
  exact ⟨p, ⟨hp.1, hp.2 ▸ h⟩, rfl⟩

omit [TopologicalSpace N] in
private theorem slice_subset_upper {s t : AxialInterval a} (h : s < t) :
    sliceImage Φ t ⊆ upperHalfImage Φ s := by
  rintro y ⟨p, hp, rfl⟩
  exact ⟨p, ⟨hp.1, hp.2 ▸ h⟩, rfl⟩


theorem slice_subset_later_compact (o : IsAxiallyOriented Φ d)
    {s t : AxialInterval a} (hst : s < t) :
    sliceImage Φ s ⊆ (d t).compactSide :=
  (slice_subset_lower hst).trans (o.lower_subset_compact t)


theorem slice_subset_earlier_end (o : IsAxiallyOriented Φ d)
    {s t : AxialInterval a} (hst : s < t) :
    sliceImage Φ t ⊆ (d s).endSide :=
  (slice_subset_upper hst).trans (o.upper_subset_end s)


theorem compactSide_mono (o : IsAxiallyOriented Φ d)
    {s t : AxialInterval a} (hst : s < t) :
    (d s).compactSide ⊆ (d t).compactSide := by
  have hBsCompl : (d s).compactSide ⊆ (sliceImage Φ t)ᶜ := by
    intro x hxBs hxSt
    exact Set.disjoint_left.1 (d s).disjoint hxBs
      (o.slice_subset_earlier_end hst hxSt)
  apply (d t).subset_compactSide_of_isPreconnected_of_inter_nonempty
    (d s).isConnected_compactSide.isPreconnected hBsCompl
  obtain ⟨q, hqSs⟩ := sliceImage_nonempty (Φ := Φ) s
  have hqBt : q ∈ (d t).compactSide := o.slice_subset_later_compact hst hqSs
  have hqClosure : q ∈ closure (d s).compactSide := by
    apply frontier_subset_closure
    simpa only [(d s).frontier_compactSide] using hqSs
  obtain ⟨x, hxBt, hxBs⟩ := mem_closure_iff.1 hqClosure
    (d t).compactSide (d t).isOpen_compactSide hqBt
  exact ⟨x, hxBs, hxBt⟩


theorem endSide_antitone (o : IsAxiallyOriented Φ d)
    {s t : AxialInterval a} (hst : s < t) :
    (d t).endSide ⊆ (d s).endSide := by
  have hEtCompl : (d t).endSide ⊆ (sliceImage Φ s)ᶜ := by
    intro x hxEt hxSs
    exact Set.disjoint_left.1 (d t).disjoint
      (o.slice_subset_later_compact hst hxSs) hxEt
  exact (d s).subset_endSide_of_not_isCompact_closure
    (d t).isConnected_endSide.isPreconnected hEtCompl
    (d t).not_isCompact_closure_endSide

theorem compactClosure_subset_later_compact_and_interior
    (o : IsAxiallyOriented Φ d) {s t : AxialInterval a} (hst : s < t) :
    closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide) := by
  constructor
  · rw [(d s).closure_compactSide]
    exact union_subset (o.compactSide_mono hst)
      (o.slice_subset_later_compact hst)
  · exact (d t).interior_closure_compactSide.symm


theorem compactClosure_ssubset (o : IsAxiallyOriented Φ d)
    {s t : AxialInterval a} (hst : s < t) :
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  have hKst : closure (d s).compactSide ⊆ (d t).compactSide :=
    (o.compactClosure_subset_later_compact_and_interior hst).1
  apply Set.ssubset_iff_exists.2
  refine ⟨hKst.trans subset_closure, ?_⟩
  obtain ⟨q, hqSt⟩ := sliceImage_nonempty (Φ := Φ) t
  refine ⟨q, ?_, ?_⟩
  · rw [(d t).closure_compactSide]
    exact Or.inr hqSt
  · intro hqKs
    exact (d t).compactSide_disjoint_sphere.le_bot
      ⟨hKst hqKs, hqSt⟩

theorem compactClosure_ssubset_later_compact
    (o : IsAxiallyOriented Φ d) {s t : AxialInterval a} (hst : s < t) :
    closure (d s).compactSide ⊂ (d t).compactSide := by
  have hsubset : closure (d s).compactSide ⊆ (d t).compactSide :=
    (o.compactClosure_subset_later_compact_and_interior hst).1
  have hstReal : (s : ℝ) < (t : ℝ) := hst
  apply Set.ssubset_iff_exists.2
  refine ⟨hsubset, ?_⟩
  let r : AxialInterval a :=
    ⟨((s : ℝ) + (t : ℝ)) / 2,
      lt_trans s.2.1 (by change (s : ℝ) < ((s : ℝ) + (t : ℝ)) / 2; linarith),
      lt_trans (by change ((s : ℝ) + (t : ℝ)) / 2 < (t : ℝ); linarith) t.2.2⟩
  have hsr : s < r := by
    change (s : ℝ) < ((s : ℝ) + (t : ℝ)) / 2
    linarith
  have hrt : r < t := by
    change ((s : ℝ) + (t : ℝ)) / 2 < (t : ℝ)
    linarith
  obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
  let x := Φ (p, r)
  have hxBt : x ∈ (d t).compactSide :=
    o.lower_subset_compact t ⟨(p, r), ⟨hp, hrt⟩, rfl⟩
  have hxEs : x ∈ (d s).endSide :=
    o.upper_subset_end s ⟨(p, r), ⟨hp, hsr⟩, rfl⟩
  refine ⟨x, hxBt, ?_⟩
  rw [(d s).closure_compactSide]
  rintro (hxBs | hxSs)
  · exact (d s).disjoint.le_bot ⟨hxBs, hxEs⟩
  · exact (d s).endSide_disjoint_sphere.le_bot ⟨hxEs, hxSs⟩

private theorem compact_union_lower_eq_halfOpen
    (o : IsAxiallyOriented Φ d) (s t : AxialInterval a) :
    (d s).compactSide ∪ lowerHalfImage Φ t =
      (d s).compactSide ∪ halfOpenSlabImage Φ s t := by
  ext x
  constructor
  · rintro (hxBs | ⟨p, hp, rfl⟩)
    · exact Or.inl hxBs
    · rcases lt_trichotomy p.2 s with hps | hps | hsp
      · exact Or.inl (o.lower_subset_compact s ⟨p, ⟨hp.1, hps⟩, rfl⟩)
      · exact Or.inr ⟨p, ⟨hp.1, hps.ge, hp.2⟩, rfl⟩
      · exact Or.inr ⟨p, ⟨hp.1, hsp.le, hp.2⟩, rfl⟩
  · rintro (hxBs | ⟨p, hp, rfl⟩)
    · exact Or.inl hxBs
    · exact Or.inr ⟨p, ⟨hp.1, hp.2.2⟩, rfl⟩

omit [TopologicalSpace N] in
private theorem axialIcc_isCompact (s t : AxialInterval a) :
    IsCompact (Icc s t : Set (AxialInterval a)) := by
  let f : Icc (s : ℝ) (t : ℝ) → AxialInterval a := fun r =>
    ⟨r.1, lt_of_lt_of_le s.2.1 r.2.1, lt_of_le_of_lt r.2.2 t.2.2⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = Icc s t := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2
    · intro hr
      refine ⟨⟨r.1, hr⟩, ?_⟩
      exact Subtype.ext rfl
  rw [← hrange]
  exact isCompact_range hf

private theorem isClosed_closedSlabImage [T2Space N]
    (hΦ : IsOpenEmbedding Φ) (s t : AxialInterval a) :
    IsClosed (closedSlabImage Φ s t) := by
  have hdomain : IsCompact (closedSlabDomain s t) :=
    isCompact_univ.prod (axialIcc_isCompact s t)
  exact (hdomain.image hΦ.continuous).isClosed

private theorem closure_compact_union_lower_subset
    [T2Space N] (o : IsAxiallyOriented Φ d) (hΦ : IsOpenEmbedding Φ)
    (s t : AxialInterval a) :
    closure ((d s).compactSide ∪ lowerHalfImage Φ t) ⊆
      closure (d s).compactSide ∪ closedSlabImage Φ s t := by
  rw [compact_union_lower_eq_halfOpen o s t]
  apply closure_minimal
  · rintro x (hxBs | ⟨p, hp, rfl⟩)
    · exact Or.inl (subset_closure hxBs)
    · exact Or.inr ⟨p, ⟨hp.1, hp.2.1, hp.2.2.le⟩, rfl⟩
  · exact isClosed_closure.union (isClosed_closedSlabImage hΦ s t)

private theorem closure_compact_union_lower_subset_self_union_slice
    [T2Space N] (o : IsAxiallyOriented Φ d) (hΦ : IsOpenEmbedding Φ)
    {s t : AxialInterval a} (hst : s < t) :
    closure ((d s).compactSide ∪ lowerHalfImage Φ t) ⊆
      ((d s).compactSide ∪ lowerHalfImage Φ t) ∪ sliceImage Φ t := by
  intro x hx
  rcases closure_compact_union_lower_subset o hΦ s t hx with hxKs | hxSlab
  · rw [(d s).closure_compactSide] at hxKs
    rcases hxKs with hxBs | hxSs
    · exact Or.inl (Or.inl hxBs)
    · exact Or.inl (Or.inr (slice_subset_lower hst hxSs))
  · rcases hxSlab with ⟨p, hp, rfl⟩
    rcases lt_or_eq_of_le hp.2.2 with hpt | hpt
    · exact Or.inl (Or.inr ⟨p, ⟨hp.1, hpt⟩, rfl⟩)
    · exact Or.inr ⟨p, ⟨hp.1, hpt⟩, rfl⟩

theorem compactSide_eq_union_halfOpenSlab [T2Space N]
    (o : IsAxiallyOriented Φ d) (hΦ : IsOpenEmbedding Φ)
    {s t : AxialInterval a} (hst : s < t) :
    (d t).compactSide =
      (d s).compactSide ∪ halfOpenSlabImage Φ s t := by
  have hcandidateOpen :
      IsOpen ((d s).compactSide ∪ lowerHalfImage Φ t) := by
    apply (d s).isOpen_compactSide.union
    exact hΦ.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
  have hcandidateSubset :
      (d s).compactSide ∪ lowerHalfImage Φ t ⊆ (d t).compactSide :=
    union_subset (o.compactSide_mono hst) (o.lower_subset_compact t)
  have hcover : (d t).compactSide ⊆
      ((d s).compactSide ∪ lowerHalfImage Φ t) ∪
        (closure ((d s).compactSide ∪ lowerHalfImage Φ t))ᶜ := by
    intro x hxBt
    by_cases hx : x ∈ (d s).compactSide ∪ lowerHalfImage Φ t
    · exact Or.inl hx
    · refine Or.inr ?_
      intro hxClosure
      rcases closure_compact_union_lower_subset_self_union_slice o hΦ hst hxClosure with
        hx' | hxSt
      · exact hx hx'
      · exact (d t).compactSide_disjoint_sphere.le_bot ⟨hxBt, hxSt⟩
  have hinter : ((d t).compactSide ∩
      ((d s).compactSide ∪ lowerHalfImage Φ t)).Nonempty := by
    obtain ⟨x, hxBs⟩ := (d s).compactSide_nonempty
    exact ⟨x, o.compactSide_mono hst hxBs, Or.inl hxBs⟩
  have hdisjoint : Disjoint
      ((d s).compactSide ∪ lowerHalfImage Φ t)
      (closure ((d s).compactSide ∪ lowerHalfImage Φ t))ᶜ := by
    rw [Set.disjoint_left]
    intro x hx hxClosure
    exact hxClosure (subset_closure hx)
  have hBtSubset : (d t).compactSide ⊆
      (d s).compactSide ∪ lowerHalfImage Φ t :=
    (d t).isConnected_compactSide.isPreconnected.subset_left_of_subset_union
      hcandidateOpen isClosed_closure.isOpen_compl hdisjoint hcover hinter
  rw [← compact_union_lower_eq_halfOpen o s t]
  exact Set.Subset.antisymm hBtSubset hcandidateSubset

theorem compactClosure_eq_union_closedSlab [T2Space N]
    (o : IsAxiallyOriented Φ d) (hΦ : IsOpenEmbedding Φ)
    {s t : AxialInterval a} (hst : s < t) :
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t := by
  have hBt : (d t).compactSide =
      (d s).compactSide ∪ lowerHalfImage Φ t :=
    (o.compactSide_eq_union_halfOpenSlab hΦ hst).trans
      (compact_union_lower_eq_halfOpen o s t).symm
  apply Set.Subset.antisymm
  · rw [hBt]
    exact closure_compact_union_lower_subset o hΦ s t
  · rintro x (hxKs | ⟨p, hp, rfl⟩)
    · exact subset_closure
        ((o.compactClosure_subset_later_compact_and_interior hst).1 hxKs)
    · rcases lt_or_eq_of_le hp.2.2 with hpt | hpt
      · exact subset_closure
          (o.lower_subset_compact t ⟨p, ⟨hp.1, hpt⟩, rfl⟩)
      · rw [(d t).closure_compactSide]
        exact Or.inr ⟨p, ⟨hp.1, hpt⟩, rfl⟩

private theorem closedSlab_subset_slice_union_end
    (o : IsAxiallyOriented Φ d) {s t : AxialInterval a} :
    closedSlabImage Φ s t ⊆ sliceImage Φ s ∪ (d s).endSide := by
  rintro x ⟨p, hp, rfl⟩
  rcases eq_or_lt_of_le hp.2.1 with hps | hsp
  · exact Or.inl ⟨p, ⟨hp.1, hps.symm⟩, rfl⟩
  · exact Or.inr (o.upper_subset_end s ⟨p, ⟨hp.1, hsp⟩, rfl⟩)

private theorem closedSlab_subset_compact_union_slice
    (o : IsAxiallyOriented Φ d) {s t : AxialInterval a} :
    closedSlabImage Φ s t ⊆ (d t).compactSide ∪ sliceImage Φ t := by
  rintro x ⟨p, hp, rfl⟩
  rcases lt_or_eq_of_le hp.2.2 with hpt | hpt
  · exact Or.inl (o.lower_subset_compact t ⟨p, ⟨hp.1, hpt⟩, rfl⟩)
  · exact Or.inr ⟨p, ⟨hp.1, hpt⟩, rfl⟩

theorem compl_closedSlab_eq_union_and_disjoint [T2Space N]
    (o : IsAxiallyOriented Φ d) (hΦ : IsOpenEmbedding Φ)
    {s t : AxialInterval a} (hst : s < t) :
    (closedSlabImage Φ s t)ᶜ = (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide := by
  have hSsSlab : sliceImage Φ s ⊆ closedSlabImage Φ s t := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hp.1, hp.2 ▸ le_rfl, hp.2 ▸ hst.le⟩, rfl⟩
  have hStSlab : sliceImage Φ t ⊆ closedSlabImage Φ s t := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hp.1, hp.2 ▸ hst.le, hp.2 ▸ le_rfl⟩, rfl⟩
  have hBt : (d t).compactSide =
      (d s).compactSide ∪ halfOpenSlabImage Φ s t :=
    o.compactSide_eq_union_halfOpenSlab hΦ hst
  have hBsDisjointSlab : Disjoint (d s).compactSide (closedSlabImage Φ s t) := by
    rw [Set.disjoint_left]
    intro x hxBs hxSlab
    rcases closedSlab_subset_slice_union_end o hxSlab with hxSs | hxEs
    · exact (d s).compactSide_disjoint_sphere.le_bot ⟨hxBs, hxSs⟩
    · exact (d s).disjoint.le_bot ⟨hxBs, hxEs⟩
  have hEtDisjointSlab : Disjoint (d t).endSide (closedSlabImage Φ s t) := by
    rw [Set.disjoint_left]
    intro x hxEt hxSlab
    rcases closedSlab_subset_compact_union_slice o hxSlab with hxBt | hxSt
    · exact (d t).disjoint.le_bot ⟨hxBt, hxEt⟩
    · exact (d t).endSide_disjoint_sphere.le_bot ⟨hxEt, hxSt⟩
  constructor
  · apply Set.Subset.antisymm
    · intro x hxOutside
      have hxSs : x ∈ (sliceImage Φ s)ᶜ := fun hx => hxOutside (hSsSlab hx)
      have hxSt : x ∈ (sliceImage Φ t)ᶜ := fun hx => hxOutside (hStSlab hx)
      have hxsides : x ∈ (d s).compactSide ∪ (d s).endSide := by
        rw [(d s).union_eq_compl]
        exact hxSs
      rcases hxsides with hxBs | hxEs
      · exact Or.inl hxBs
      · have hxtsides : x ∈ (d t).compactSide ∪ (d t).endSide := by
          rw [(d t).union_eq_compl]
          exact hxSt
        rcases hxtsides with hxBt | hxEt
        · rw [hBt] at hxBt
          rcases hxBt with hxBs | hxBand
          · exact False.elim ((d s).disjoint.le_bot ⟨hxBs, hxEs⟩)
          · exact False.elim (hxOutside (by
              rcases hxBand with ⟨p, hp, rfl⟩
              exact ⟨p, ⟨hp.1, hp.2.1, hp.2.2.le⟩, rfl⟩))
        · exact Or.inr hxEt
    · rintro x (hxBs | hxEt) hxSlab
      · exact hBsDisjointSlab.le_bot ⟨hxBs, hxSlab⟩
      · exact hEtDisjointSlab.le_bot ⟨hxEt, hxSlab⟩
  · rw [Set.disjoint_left]
    intro x hxBs hxEt
    exact (d t).disjoint.le_bot ⟨o.compactSide_mono hst hxBs, hxEt⟩

theorem orderedSlices_core [T2Space N]
    (o : IsAxiallyOriented Φ d) (hΦ : IsOpenEmbedding Φ)
    {s t : AxialInterval a} (hst : s < t) :
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ = (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide := by
  exact ⟨o.compactClosure_subset_later_compact_and_interior hst,
    o.compactClosure_eq_union_closedSlab hΦ hst,
    o.compl_closedSlab_eq_union_and_disjoint hΦ hst,
    o.compactClosure_ssubset_later_compact hst⟩

theorem orderedSlices_core_of_isSmoothEmbedding
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : ∀ c, SphereSides (sliceImage Φ c))
    (o : IsAxiallyOriented Φ d) {s t : AxialInterval a} (hst : s < t) :
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ = (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide := by
  have hrank :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
        Module.finrank ℝ EuclideanThree := by
    norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
  have hopen : IsOpen (Set.range Φ) :=
    Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  exact o.orderedSlices_core ⟨hΦ.isEmbedding, hopen⟩ hst

end IsAxiallyOriented

end DifferentialGeometry.Topology.SphereSeparation

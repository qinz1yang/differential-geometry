import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {N T M : Type*} [TopologicalSpace N] [TopologicalSpace T] [PartialOrder T]
  [OrderTopology T] [TopologicalSpace M]

theorem image_Icc_subset_interior_union_upper_boundary
    (e : OpenPartialHomeomorph (N × T) M) {a b : T} {W : Set M}
    (hsource : univ ×ˢ Icc a b ⊆ e.source)
    (hcontained : e '' (univ ×ˢ Icc a b) ⊆ W)
    (hlower : e '' (univ ×ˢ ({a} : Set T)) ⊆ interior W) :
    e '' (univ ×ˢ Icc a b) ⊆ interior W ∪ e '' (univ ×ˢ ({b} : Set T)) := by
  have hsub : (univ : Set N) ×ˢ Ioo a b ⊆ univ ×ˢ Icc a b :=
    prod_mono_right Ioo_subset_Icc_self
  have hopen : IsOpen (e '' (univ ×ˢ Ioo a b)) :=
    e.isOpen_image_of_subset_source (isOpen_univ.prod (isOpen_Ioo' a b)) (hsub.trans hsource)
  have hint : e '' (univ ×ˢ Ioo a b) ⊆ interior W :=
    interior_maximal ((image_mono hsub).trans hcontained) hopen
  rintro y ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
  rcases ht.1.eq_or_lt with h | h
  · exact Or.inl (hlower ⟨(z, t), ⟨mem_univ _, h.symm⟩, rfl⟩)
  · rcases ht.2.eq_or_lt with h' | h'
    · exact Or.inr ⟨(z, t), ⟨mem_univ _, h'⟩, rfl⟩
    · exact Or.inl (hint ⟨(z, t), ⟨mem_univ _, h, h'⟩, rfl⟩)

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology

private theorem disjoint_of_frontier_faces_at_max
    {M ι : Type*} [TopologicalSpace M]
    (label : ℕ → ι) (face : ℕ → ι → Set M) (band W : ℕ → Set M)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hW : Monotone W)
    (hcontained : ∀ n, band n ⊆ W (n + 1))
    (hinter : ∀ n, band n ∩ W n = face n (label n))
    (hfrontier : ∀ n, face n (label n) ⊆ frontier (W n))
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (hexposed : ∀ n, band n ⊆ interior (W (n + 1)) ∪ face (n + 1) (label n))
    (a b : ℕ) (hne : label a ≠ label b)
    (hdisjoint : Disjoint (face (max a b) (label a)) (face (max a b) (label b))) :
    Disjoint (band a) (band b) := by
  have hprop (a b : ℕ) (hab : a + 1 ≤ b) :
      band a ⊆ interior (W b) ∪ face b (label a) := by
    induction b, hab using Nat.le_induction with
    | base => exact hexposed a
    | succ b hab ih =>
      intro x hx
      rcases ih hx with hx | hx
      · exact Or.inl (interior_mono (hW (Nat.le_succ b)) hx)
      · by_cases hba : label b = label a
        · exact Or.inl (hfilled b (by simpa only [hba] using hx))
        · exact Or.inr ((hunchanged b (label a) hba).symm ▸ hx)
  have hlt (a b : ℕ) (hab : a < b)
      (hd : Disjoint (face b (label a)) (face b (label b))) :
      Disjoint (band a) (band b) := by
    apply disjoint_left.mpr
    intro x hxa hxb
    have hxW : x ∈ W b := hW (Nat.succ_le_of_lt hab) (hcontained a hxa)
    have hxbface : x ∈ face b (label b) := hinter b ▸ ⟨hxb, hxW⟩
    rcases hprop a b (Nat.succ_le_of_lt hab) hxa with hxint | hxface
    · exact (hfrontier b hxbface).2 hxint
    · exact disjoint_left.mp hd hxface hxbface
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hlt a b hab (by simpa only [max_eq_right hab.le] using hdisjoint)
  · exact (hne (congrArg label hab)).elim
  · exact (hlt b a hab (by simpa only [max_eq_left hab.le] using hdisjoint.symm)).symm

end DifferentialGeometry.Topology

namespace OpenPartialHomeomorph

open DifferentialGeometry.Topology

theorem disjoint_cylinder_images_of_disjoint_frontier_faces
    {N T M ι : Type*} [TopologicalSpace N] [TopologicalSpace T]
    [PartialOrder T] [OrderTopology T] [TopologicalSpace M] {c d : T}
    (label : ℕ → ι) (face : ℕ → ι → Set M)
    (P : ℕ → OpenPartialHomeomorph (N × T) M)
    (hsource : ∀ n, univ ×ˢ Icc c d ⊆ (P n).source)
    (hlower : ∀ n, P n '' (univ ×ˢ ({c} : Set T)) ⊆ face n (label n))
    (hupper : ∀ n, P n '' (univ ×ˢ ({d} : Set T)) ⊆ face (n + 1) (label n))
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (univ ×ˢ Icc c d) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (univ ×ˢ Icc c d) ∩ W n = face n (label n))
    (hfrontier : ∀ n, face n (label n) ⊆ frontier (W n))
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (a b : ℕ) (hne : label a ≠ label b)
    (hdisjoint : Disjoint (face (max a b) (label a)) (face (max a b) (label b))) :
    Disjoint (P a '' (univ ×ˢ Icc c d)) (P b '' (univ ×ˢ Icc c d)) := by
  apply disjoint_of_frontier_faces_at_max label face
    (fun n => P n '' (univ ×ˢ Icc c d)) W hunchanged hW hcontained
    hinter hfrontier hfilled _ a b hne hdisjoint
  intro n
  exact ((P n).image_Icc_subset_interior_union_upper_boundary (hsource n)
    (hcontained n) ((hlower n).trans (hfilled n))).trans (union_subset_union_right _ (hupper n))

theorem disjoint_cylinder_images_of_distinct_labels
    {N T M ι : Type*} [TopologicalSpace N] [TopologicalSpace T]
    [PartialOrder T] [OrderTopology T] [TopologicalSpace M] {c d : T}
    (label : ℕ → ι) (face : ℕ → ι → Set M)
    (P : ℕ → OpenPartialHomeomorph (N × T) M)
    (hsource : ∀ n, univ ×ˢ Icc c d ⊆ (P n).source)
    (hlower : ∀ n, P n '' (univ ×ˢ ({c} : Set T)) ⊆ face n (label n))
    (hupper : ∀ n, P n '' (univ ×ˢ ({d} : Set T)) ⊆ face (n + 1) (label n))
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (univ ×ˢ Icc c d) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (univ ×ˢ Icc c d) ∩ W n = face n (label n))
    (hfrontier : ∀ n, face n (label n) ⊆ frontier (W n))
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (hdisjoint : ∀ n, (range label).Pairwise (fun i j => Disjoint (face n i) (face n j)))
    (a b : ℕ) (hne : label a ≠ label b) :
    Disjoint (P a '' (univ ×ˢ Icc c d)) (P b '' (univ ×ˢ Icc c d)) := by
  apply disjoint_cylinder_images_of_disjoint_frontier_faces label face P hsource hlower hupper
    hunchanged W hW hcontained hinter hfrontier hfilled a b hne
  exact hdisjoint (max a b) (mem_range_self a) (mem_range_self b) hne

end OpenPartialHomeomorph

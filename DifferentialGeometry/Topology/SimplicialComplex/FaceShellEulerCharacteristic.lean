import DifferentialGeometry.Topology.SimplicialComplex.FaceShell
import DifferentialGeometry.Topology.SimplicialComplex.EulerCharacteristic
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
noncomputable section
open Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι)
  (s : Finset ι) (hs : s ∈ K)

include hs in
private theorem augmented_shell_membership (t : Finset ι) :
    (t = ∅ ∨ t ∈ faceShell K s) ↔
      t ∩ s ⊂ s ∧ (t \ s = ∅ ∨ t \ s ∈ link K s) := by
  have hsne := (K.isRelLowerSet_faces hs).1
  constructor
  · intro ht
    rcases ht with rfl | ht
    · simp only [empty_inter, empty_sdiff, true_or, and_true]
      exact Finset.empty_ssubset.mpr hsne
    · refine ⟨lt_iff_le_not_ge.mpr ⟨Finset.inter_subset_right, ?_⟩, ?_⟩
      · exact fun h ↦ ht.2.2 (h.trans Finset.inter_subset_left)
      · by_cases he : t \ s = ∅
        · exact Or.inl he
        · refine Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr he,
            disjoint_sdiff_self_right, ?_⟩
          simpa only [Finset.union_sdiff_self_eq_union, Finset.union_comm] using ht.2.1
  · rintro ⟨hproper, hlink⟩
    by_cases ht : t = ∅
    · exact Or.inl ht
    · have hcoface : t ∪ s ∈ K := by
        rcases hlink with hb | hb
        · have hts : t ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp hb
          simpa only [Finset.union_eq_right.mpr hts] using hs
        · simpa only [Finset.union_sdiff_self_eq_union, Finset.union_comm] using hb.2.2
      refine Or.inr ⟨(K.isRelLowerSet_faces hcoface).2 Finset.subset_union_left
        (Finset.nonempty_iff_ne_empty.mpr ht), hcoface, ?_⟩
      intro hst
      exact (lt_iff_le_not_ge.mp hproper).2 (Finset.subset_inter hst (Finset.Subset.refl _))

private theorem augmented_link_disjoint {t : Finset ι} (ht : t = ∅ ∨ t ∈ link K s) :
    Disjoint s t := by
  rcases ht with rfl | ht
  · exact Finset.disjoint_empty_right _
  · exact ht.2.1

private theorem shell_components_union {a b : Finset ι} (ha : a ⊂ s)
    (hb : b = ∅ ∨ b ∈ link K s) :
    (a ∪ b) ∩ s = a ∧ (a ∪ b) \ s = b := by
  have hd := augmented_link_disjoint K s hb
  constructor
  · ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hps⟩
      · exact hp
      · exact (Finset.disjoint_left.mp hd hps hp).elim
    · intro hp
      exact ⟨Or.inl hp, ha.le hp⟩
  · rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr ha.le,
      Finset.empty_union, Finset.sdiff_eq_self_iff_disjoint.mpr hd.symm]

def augmentedFaceShellEquiv :
    {t : Finset ι // t = ∅ ∨ t ∈ faceShell K s} ≃
      {a : Finset ι // a ⊂ s} × {b : Finset ι // b = ∅ ∨ b ∈ link K s} where
  toFun t :=
    (⟨t.val ∩ s, ((augmented_shell_membership K s hs t.val).mp t.prop).1⟩,
      ⟨t.val \ s, ((augmented_shell_membership K s hs t.val).mp t.prop).2⟩)
  invFun z := ⟨z.1.val ∪ z.2.val, (augmented_shell_membership K s hs _).mpr
    (by rw [(shell_components_union K s z.1.prop z.2.prop).1,
      (shell_components_union K s z.1.prop z.2.prop).2]; exact ⟨z.1.prop, z.2.prop⟩)⟩
  left_inv t := Subtype.ext (by
    change t.val ∩ s ∪ t.val \ s = t.val
    rw [Finset.union_comm, Finset.sdiff_union_inter])
  right_inv z := Prod.ext (Subtype.ext (shell_components_union K s z.1.prop z.2.prop).1)
    (Subtype.ext (shell_components_union K s z.1.prop z.2.prop).2)


@[simp]
theorem augmentedFaceShellEquiv_fst_val
    (t : {t : Finset ι // t = ∅ ∨ t ∈ faceShell K s}) :
    (augmentedFaceShellEquiv K s hs t).1.val = t.val ∩ s := rfl


@[simp]
theorem augmentedFaceShellEquiv_snd_val
    (t : {t : Finset ι // t = ∅ ∨ t ∈ faceShell K s}) :
    (augmentedFaceShellEquiv K s hs t).2.val = t.val \ s := rfl


@[simp]
theorem augmentedFaceShellEquiv_symm_val
    (z : {a : Finset ι // a ⊂ s} × {b : Finset ι // b = ∅ ∨ b ∈ link K s}) :
    ((augmentedFaceShellEquiv K s hs).symm z).val = z.1.val ∪ z.2.val := rfl


theorem augmentedFaceShellEquiv_card
    (t : {t : Finset ι // t = ∅ ∨ t ∈ faceShell K s}) :
    t.val.card = (augmentedFaceShellEquiv K s hs t).1.val.card +
      (augmentedFaceShellEquiv K s hs t).2.val.card := by
  change t.val.card = (t.val ∩ s).card + (t.val \ s).card
  simpa only [Finset.inter_comm] using (Finset.card_inter_add_card_sdiff t.val s).symm

private theorem sum_augmented_faces (L : PreAbstractSimplicialComplex ι) [Finite L.faces] :
    (∑ t ∈ insert ∅ (Set.toFinite L.faces).toFinset, (-1 : ℤ) ^ t.card) =
      1 - faceEulerChar L := by
  have hnot : ∅ ∉ (Set.toFinite L.faces).toFinset := by
    intro h
    exact (L.isRelLowerSet_faces ((Set.toFinite L.faces).mem_toFinset.mp h)).1.ne_empty rfl
  rw [Finset.sum_insert hnot, Finset.card_empty, pow_zero, faceEulerChar,
    Finset.sum_neg_distrib, sub_neg_eq_add]

include hs in
private theorem shell_sum_product [Finite K.faces] :
    (∑ t ∈ insert ∅ (Set.toFinite (faceShell K s).faces).toFinset, (-1 : ℤ) ^ t.card) =
      (∑ a ∈ s.powerset.erase s, (-1 : ℤ) ^ a.card) *
        ∑ b ∈ insert ∅ (Set.toFinite (link K s).faces).toFinset, (-1 : ℤ) ^ b.card := by
  let T := insert ∅ (Set.toFinite (faceShell K s).faces).toFinset
  let A := s.powerset.erase s
  let B := insert ∅ (Set.toFinite (link K s).faces).toFinset
  have hT (t : Finset ι) : t ∈ T ↔ t = ∅ ∨ t ∈ faceShell K s := by
    simp only [T, Finset.mem_insert, Set.Finite.mem_toFinset]
    rfl
  have hA (a : Finset ι) : a ∈ A ↔ a ⊂ s := by
    simp only [A, Finset.mem_erase, Finset.mem_powerset, Finset.ssubset_iff_subset_ne, and_comm]
  have hB (b : Finset ι) : b ∈ B ↔ b = ∅ ∨ b ∈ link K s := by
    simp only [B, Finset.mem_insert, Set.Finite.mem_toFinset]
    rfl
  let e := augmentedFaceShellEquiv K s hs
  change (∑ t ∈ T, (-1 : ℤ) ^ t.card) =
    (∑ a ∈ A, (-1 : ℤ) ^ a.card) * ∑ b ∈ B, (-1 : ℤ) ^ b.card
  calc
    _ = ∑ z ∈ A ×ˢ B, (-1 : ℤ) ^ z.1.card * (-1 : ℤ) ^ z.2.card := by
      apply Finset.sum_bij
        (fun t ht ↦ ((e ⟨t, (hT t).mp ht⟩).1.val, (e ⟨t, (hT t).mp ht⟩).2.val))
      · intro t ht
        exact Finset.mem_product.mpr
          ⟨(hA _).mpr (e ⟨t, (hT t).mp ht⟩).1.prop,
            (hB _).mpr (e ⟨t, (hT t).mp ht⟩).2.prop⟩
      · intro t ht u hu he
        have he' : e ⟨t, (hT t).mp ht⟩ = e ⟨u, (hT u).mp hu⟩ :=
          Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
        exact congrArg Subtype.val (e.injective he')
      · intro z hz
        let zz : {a : Finset ι // a ⊂ s} × {b : Finset ι // b = ∅ ∨ b ∈ link K s} :=
          (⟨z.1, (hA _).mp (Finset.mem_product.mp hz).1⟩,
            ⟨z.2, (hB _).mp (Finset.mem_product.mp hz).2⟩)
        refine ⟨(e.symm zz).val, (hT _).mpr (e.symm zz).prop, ?_⟩
        exact congrArg (fun w ↦ (w.1.val, w.2.val)) (e.apply_symm_apply zz)
      · intro t ht
        rw [augmentedFaceShellEquiv_card K s hs ⟨t, (hT t).mp ht⟩, pow_add]
    _ = _ := by
      rw [Finset.sum_product]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

include hs in
theorem faceEulerChar_faceShell [Finite K.faces] :
    faceEulerChar (faceShell K s) =
      1 + (-1 : ℤ) ^ s.card * (1 - faceEulerChar (link K s)) := by
  have hsum := Finset.sum_erase_add (s := s.powerset)
    (f := fun a : Finset ι ↦ (-1 : ℤ) ^ a.card)
    (Finset.mem_powerset.mpr (Finset.Subset.refl s))
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty (K.isRelLowerSet_faces hs).1] at hsum
  have hprod := shell_sum_product K s hs
  rw [sum_augmented_faces, sum_augmented_faces] at hprod
  have hA : (∑ a ∈ s.powerset.erase s, (-1 : ℤ) ^ a.card) = -(-1 : ℤ) ^ s.card := by
    linarith
  rw [hA] at hprod
  linarith

include hs in
theorem one_sub_faceEulerChar_faceShell [Finite K.faces] :
    1 - faceEulerChar (faceShell K s) =
      (-1 : ℤ) ^ (s.card - 1) * (1 - faceEulerChar (link K s)) := by
  have hc : s.card - 1 + 1 = s.card := Nat.sub_add_cancel
    (Finset.card_pos.mpr (K.isRelLowerSet_faces hs).1)
  have hp : (-1 : ℤ) ^ s.card = -(-1 : ℤ) ^ (s.card - 1) := by
    conv_lhs => rw [← hc, pow_succ]
    ring
  rw [faceEulerChar_faceShell K s hs, hp]
  ring

end DifferentialGeometry.Topology.SimplicialComplex

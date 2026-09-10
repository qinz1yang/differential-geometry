import DifferentialGeometry.Topology.SimplicialComplex.EulerCharacteristic
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
noncomputable section
open Finset

namespace Poincare.Topology.SimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]

theorem one_sub_faceEulerChar_link_eq_sum_cofaces (s : Finset ι) (hs : s ∈ K) :
    1 - faceEulerChar (link K s) =
      ∑ t ∈ (Set.toFinite K.faces).toFinset.filter (s ⊆ ·), (-1 : ℤ) ^ (t.card - s.card) := by
  let B := insert ∅ (Set.toFinite (link K s).faces).toFinset
  let T := (Set.toFinite K.faces).toFinset.filter (s ⊆ ·)
  have hB (b : Finset ι) : b ∈ B ↔ b = ∅ ∨ b ∈ link K s := by
    simp only [B, Finset.mem_insert, Set.Finite.mem_toFinset]
    rfl
  have hT (t : Finset ι) : t ∈ T ↔ t ∈ K ∧ s ⊆ t := by
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset]
    rfl
  have hbdata (b : Finset ι) (hb : b ∈ B) : Disjoint s b ∧ s ∪ b ∈ K := by
    rcases (hB b).mp hb with rfl | hb
    · exact ⟨Finset.disjoint_empty_right _, by simpa only [Finset.union_empty] using hs⟩
    · exact hb.2
  have hnot : ∅ ∉ (Set.toFinite (link K s).faces).toFinset := by
    intro h
    exact ((Set.toFinite (link K s).faces).mem_toFinset.mp h).1.ne_empty rfl
  have hsum : (∑ b ∈ B, (-1 : ℤ) ^ b.card) = 1 - faceEulerChar (link K s) := by
    rw [show B = insert ∅ (Set.toFinite (link K s).faces).toFinset from rfl,
      Finset.sum_insert hnot, Finset.card_empty, pow_zero, faceEulerChar,
      Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [← hsum]
  apply Finset.sum_bij (fun b _ ↦ s ∪ b)
  · intro b hb
    exact (hT _).mpr ⟨(hbdata b hb).2, Finset.subset_union_left⟩
  · intro b hb c hc he
    have hh := congrArg (· \ s) he
    simpa only [Finset.union_sdiff_cancel_left (hbdata b hb).1,
      Finset.union_sdiff_cancel_left (hbdata c hc).1] using hh
  · intro t ht
    have ht' := (hT t).mp ht
    refine ⟨t \ s, (hB _).mpr ?_, Finset.union_sdiff_of_subset ht'.2⟩
    by_cases hb : t \ s = ∅
    · exact Or.inl hb
    · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr hb, disjoint_sdiff_self_right,
        (Finset.union_sdiff_of_subset ht'.2).symm ▸ ht'.1⟩
  · intro b hb
    rw [Finset.card_union_of_disjoint (hbdata b hb).1, Nat.add_sub_cancel_left]

private theorem neg_one_pow_sub (m n : ℕ) (hn : n ≤ m) :
    (-1 : ℤ) ^ (m - n) = (-1 : ℤ) ^ m * (-1 : ℤ) ^ n := by
  have hsq : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = (-1 : ℤ) ^ (m - n) * ((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) := by rw [hsq, mul_one]
    _ = ((-1 : ℤ) ^ (m - n) * (-1 : ℤ) ^ n) * (-1 : ℤ) ^ n := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hn]

private theorem nonempty_subface_sum (t : Finset ι) (ht : t ∈ K) :
    (∑ s ∈ (Set.toFinite K.faces).toFinset.filter (· ⊆ t),
      (-1 : ℤ) ^ (t.card - s.card)) = -(-1 : ℤ) ^ t.card := by
  have hfaces : (Set.toFinite K.faces).toFinset.filter (· ⊆ t) = t.powerset.erase ∅ := by
    ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_erase, Finset.mem_powerset]
    constructor
    · rintro ⟨hs, hst⟩
      exact ⟨(K.isRelLowerSet_faces hs).1.ne_empty, hst⟩
    · rintro ⟨hs, hst⟩
      exact ⟨(K.isRelLowerSet_faces ht).2 hst (Finset.nonempty_iff_ne_empty.mpr hs), hst⟩
  rw [hfaces]
  have hsum := Finset.sum_erase_add (s := t.powerset)
    (f := fun s : Finset ι ↦ (-1 : ℤ) ^ s.card)
    (Finset.mem_powerset.mpr (Finset.empty_subset t))
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty (K.isRelLowerSet_faces ht).1,
    Finset.card_empty, pow_zero] at hsum
  calc
    _ = ∑ s ∈ t.powerset.erase ∅, (-1 : ℤ) ^ t.card * (-1 : ℤ) ^ s.card := by
      apply Finset.sum_congr rfl
      intro s hs
      exact neg_one_pow_sub _ _ (Finset.card_le_card
        (Finset.mem_powerset.mp (Finset.mem_erase.mp hs).2))
    _ = (-1 : ℤ) ^ t.card * ∑ s ∈ t.powerset.erase ∅, (-1 : ℤ) ^ s.card :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [show (∑ s ∈ t.powerset.erase ∅, (-1 : ℤ) ^ s.card) = -1 by linarith]; ring

theorem sum_one_sub_faceEulerChar_link :
    (∑ s ∈ (Set.toFinite K.faces).toFinset, (1 - faceEulerChar (link K s))) = faceEulerChar K := by
  calc
    _ = ∑ s ∈ (Set.toFinite K.faces).toFinset,
        ∑ t ∈ (Set.toFinite K.faces).toFinset.filter (s ⊆ ·),
          (-1 : ℤ) ^ (t.card - s.card) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact one_sub_faceEulerChar_link_eq_sum_cofaces K s
        ((Set.toFinite K.faces).mem_toFinset.mp hs)
    _ = ∑ t ∈ (Set.toFinite K.faces).toFinset,
        ∑ s ∈ (Set.toFinite K.faces).toFinset.filter (· ⊆ t),
          (-1 : ℤ) ^ (t.card - s.card) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ t ∈ (Set.toFinite K.faces).toFinset, -(-1 : ℤ) ^ t.card := by
      apply Finset.sum_congr rfl
      intro t ht
      exact nonempty_subface_sum K t ((Set.toFinite K.faces).mem_toFinset.mp ht)
    _ = faceEulerChar K := rfl

end Poincare.Topology.SimplicialComplex

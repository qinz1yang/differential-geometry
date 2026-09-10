import DifferentialGeometry.Topology.SimplicialComplex.Incidence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset

namespace Poincare.Topology.SimplicialComplex

noncomputable section

variable {ι : Type*} (K : PreAbstractSimplicialComplex ι) [Finite K.faces]


def faceEulerChar : ℤ := ∑ s ∈ (Set.toFinite K.faces).toFinset, -(-1 : ℤ) ^ s.card


theorem faceEulerChar_eq_sum (d : ℕ) (hd : ∀ s ∈ K, s.card ≤ d) :
    faceEulerChar K = ∑ n ∈ range (d + 1), -(-1 : ℤ) ^ n * (facesOfCard K n).card := by
  classical
  have hmap : ∀ s ∈ (Set.toFinite K.faces).toFinset, s.card ∈ range (d + 1) := by
    intro s hs
    exact mem_range.mpr (Nat.lt_succ_of_le (hd s ((Set.toFinite K.faces).mem_toFinset.mp hs)))
  unfold faceEulerChar
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro n hn
  change (∑ s ∈ facesOfCard K n, -(-1 : ℤ) ^ s.card) = _
  calc
    _ = ∑ _s ∈ facesOfCard K n, -(-1 : ℤ) ^ n := by
      apply sum_congr rfl
      intro s hs
      rw [((mem_facesOfCard K).mp hs).2]
    _ = _ := by simp [mul_comm]


theorem faceEulerChar_eq_of_card_le_four (hd : ∀ s ∈ K, s.card ≤ 4) :
    faceEulerChar K = (facesOfCard K 1).card - (facesOfCard K 2).card +
      (facesOfCard K 3).card - (facesOfCard K 4).card := by
  rw [faceEulerChar_eq_sum K 4 hd]
  simp [sum_range_succ]
  ring


theorem faceEulerChar_eq_of_card_le_three (hd : ∀ s ∈ K, s.card ≤ 3) :
    faceEulerChar K = (facesOfCard K 1).card - (facesOfCard K 2).card +
      (facesOfCard K 3).card := by
  rw [faceEulerChar_eq_sum K 3 hd]
  simp [sum_range_succ]
  ring


theorem faceEulerChar_eq_of_card_le_two (hd : ∀ s ∈ K, s.card ≤ 2) :
    faceEulerChar K = (facesOfCard K 1).card - (facesOfCard K 2).card := by
  rw [faceEulerChar_eq_sum K 2 hd]
  simp [sum_range_succ, sub_eq_add_neg, add_comm]


@[simp]
theorem faceEulerChar_bot : faceEulerChar (⊥ : PreAbstractSimplicialComplex ι) = 0 := by
  have h : (Set.toFinite (⊥ : PreAbstractSimplicialComplex ι).faces).toFinset = ∅ := by
    ext s
    simp only [Set.Finite.mem_toFinset, notMem_empty, iff_false]
    exact id
  simp [faceEulerChar, h]


theorem faceEulerChar_sup_add_faceEulerChar_inf
    (L : PreAbstractSimplicialComplex ι) [Finite L.faces] :
    faceEulerChar (K ⊔ L) + faceEulerChar (K ⊓ L) =
      faceEulerChar K + faceEulerChar L := by
  classical
  have hsup : (Set.toFinite (K ⊔ L).faces).toFinset =
      (Set.toFinite K.faces).toFinset ∪ (Set.toFinite L.faces).toFinset := by
    ext s
    simp only [Set.Finite.mem_toFinset, mem_union]
    rfl
  have hinf : (Set.toFinite (K ⊓ L).faces).toFinset =
      (Set.toFinite K.faces).toFinset ∩ (Set.toFinite L.faces).toFinset := by
    ext s
    simp only [Set.Finite.mem_toFinset, mem_inter]
    rfl
  simp only [faceEulerChar, hsup, hinf]
  exact sum_union_inter


theorem faceEulerChar_map_of_injective {κ : Type*} [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) :
    faceEulerChar (K.map f) = faceEulerChar K := by
  classical
  have hmap : (Set.toFinite (K.map f).faces).toFinset =
      (Set.toFinite K.faces).toFinset.image (fun s => s.image f) := by
    ext s
    simp only [Set.Finite.mem_toFinset, mem_image]
    rfl
  rw [faceEulerChar, hmap, sum_image]
  · apply sum_congr rfl
    intro s hs
    rw [card_image_of_injective _ hf]
  · exact (image_injective hf).injOn

end

end Poincare.Topology.SimplicialComplex

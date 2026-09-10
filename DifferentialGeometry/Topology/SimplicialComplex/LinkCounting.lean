import DifferentialGeometry.Topology.SimplicialComplex.EulerCharacteristic
import Mathlib.Tactic.NormNum

open Finset

namespace Poincare.Topology.SimplicialComplex

noncomputable section

variable {ι : Type*} [DecidableEq ι]
  (K : PreAbstractSimplicialComplex ι)


theorem card_add_card_le_of_mem_link {d : ℕ} (hd : ∀ u ∈ K, u.card ≤ d)
    {s t : Finset ι} (ht : t ∈ link K s) : s.card + t.card ≤ d := by
  rw [← card_union_of_disjoint ht.2.1]
  exact hd _ ht.2.2

variable [Finite K.faces]


theorem sum_faceEulerChar_link_edges (hd : ∀ u ∈ K, u.card ≤ 4) :
    ∑ s ∈ facesOfCard K 2, faceEulerChar (link K s) =
      3 * (facesOfCard K 3).card - 6 * (facesOfCard K 4).card := by
  have hsum (n : ℕ) (hn : 0 < n) :
      (∑ s ∈ facesOfCard K 2, ((facesOfCard (link K s) n).card : ℤ)) =
        ((2 + n).choose 2 : ℤ) * (facesOfCard K (2 + n)).card := by
    exact_mod_cast sum_card_facesOfCard_link K 2 n (by decide) hn
  calc
    _ = ∑ s ∈ facesOfCard K 2,
        (((facesOfCard (link K s) 1).card : ℤ) -
          (facesOfCard (link K s) 2).card) := by
      apply sum_congr rfl
      intro s hs
      apply faceEulerChar_eq_of_card_le_two
      intro t ht
      have hc := card_add_card_le_of_mem_link K hd ht
      have hs' := ((mem_facesOfCard K).mp hs).2
      omega
    _ = _ := by
      rw [sum_sub_distrib, hsum 1 (by decide), hsum 2 (by decide)]
      norm_num [Nat.choose]


theorem sum_faceEulerChar_link_vertices (hd : ∀ u ∈ K, u.card ≤ 4) :
    ∑ s ∈ facesOfCard K 1, faceEulerChar (link K s) =
      2 * (facesOfCard K 2).card - 3 * (facesOfCard K 3).card +
        4 * (facesOfCard K 4).card := by
  have hsum (n : ℕ) (hn : 0 < n) :
      (∑ s ∈ facesOfCard K 1, ((facesOfCard (link K s) n).card : ℤ)) =
        ((1 + n).choose 1 : ℤ) * (facesOfCard K (1 + n)).card := by
    exact_mod_cast sum_card_facesOfCard_link K 1 n (by decide) hn
  calc
    _ = ∑ s ∈ facesOfCard K 1,
        (((facesOfCard (link K s) 1).card : ℤ) -
          (facesOfCard (link K s) 2).card + (facesOfCard (link K s) 3).card) := by
      apply sum_congr rfl
      intro s hs
      apply faceEulerChar_eq_of_card_le_three
      intro t ht
      have hc := card_add_card_le_of_mem_link K hd ht
      have hs' := ((mem_facesOfCard K).mp hs).2
      omega
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib,
        hsum 1 (by decide), hsum 2 (by decide), hsum 3 (by decide)]
      norm_num [Nat.choose]

end

end Poincare.Topology.SimplicialComplex

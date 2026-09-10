import DifferentialGeometry.Topology.SimplicialComplex.LinkCounting
import Mathlib.Tactic.Linarith

open Finset

namespace Poincare.Topology.SimplicialComplex

noncomputable section

variable {ι : Type*}
  (K L : PreAbstractSimplicialComplex ι) [Finite K.faces] [Finite L.faces]

open Classical in
private theorem sum_ite_mem_faces (hLK : L ≤ K) (k : ℕ) (a b : ℤ) :
    ∑ s ∈ facesOfCard K k, (if s ∈ L then a else b) =
      b * (facesOfCard K k).card + (a - b) * (facesOfCard L k).card := by
  classical
  have hf : (facesOfCard K k).filter (· ∈ L) = facesOfCard L k := by
    ext s
    simp only [mem_filter, mem_facesOfCard]
    constructor
    · rintro ⟨⟨_, hc⟩, hs⟩
      exact ⟨hs, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨hLK hs, hc⟩, hs⟩
  calc
    _ = ∑ s ∈ facesOfCard K k, (b + if s ∈ L then a - b else 0) := by
      apply sum_congr rfl
      intro s hs
      split_ifs <;> ring
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter, hf]
      simp [mul_comm, sub_mul]

variable [DecidableEq ι]

open Classical in
theorem card_boundary_triangles (hLK : L ≤ K)
    (htri : ∀ s ∈ facesOfCard K 3, (cofaces K s 4).card = if s ∈ L then 1 else 2) :
    ((facesOfCard L 3).card : ℤ) =
      2 * (facesOfCard K 3).card - 4 * (facesOfCard K 4).card := by
  classical
  have hcount : (∑ s ∈ facesOfCard K 3, ((cofaces K s 4).card : ℤ)) =
      4 * (facesOfCard K 4).card := by
    exact_mod_cast sum_card_cofaces K 3 4 (by decide)
  have hlocal : (∑ s ∈ facesOfCard K 3, ((cofaces K s 4).card : ℤ)) =
      2 * (facesOfCard K 3).card - (facesOfCard L 3).card := by
    calc
      _ = ∑ s ∈ facesOfCard K 3, (if s ∈ L then (1 : ℤ) else 2) := by
        apply sum_congr rfl
        intro s hs
        rw [htri s hs]
        split_ifs <;> norm_num
      _ = _ := by rw [sum_ite_mem_faces K L hLK]; ring
  linarith

open Classical in
theorem card_boundary_edges (hLK : L ≤ K) (hd : ∀ u ∈ K, u.card ≤ 4)
    (hedge : ∀ s ∈ facesOfCard K 2,
      faceEulerChar (link K s) = if s ∈ L then 1 else 0) :
    ((facesOfCard L 2).card : ℤ) =
      3 * (facesOfCard K 3).card - 6 * (facesOfCard K 4).card := by
  classical
  rw [← sum_faceEulerChar_link_edges K hd]
  calc
    _ = ∑ s ∈ facesOfCard K 2, (if s ∈ L then (1 : ℤ) else 0) := by
      rw [sum_ite_mem_faces K L hLK]
      ring
    _ = _ := sum_congr rfl fun s hs => (hedge s hs).symm

open Classical in
theorem card_boundary_vertices (hLK : L ≤ K) (hd : ∀ u ∈ K, u.card ≤ 4)
    (hvertex : ∀ s ∈ facesOfCard K 1,
      faceEulerChar (link K s) = if s ∈ L then 1 else 2) :
    ((facesOfCard L 1).card : ℤ) = 2 * (facesOfCard K 1).card -
      2 * (facesOfCard K 2).card + 3 * (facesOfCard K 3).card -
        4 * (facesOfCard K 4).card := by
  classical
  have hlocal : (∑ s ∈ facesOfCard K 1, faceEulerChar (link K s)) =
      2 * (facesOfCard K 1).card - (facesOfCard L 1).card := by
    calc
      _ = ∑ s ∈ facesOfCard K 1, (if s ∈ L then (1 : ℤ) else 2) :=
        sum_congr rfl fun s hs => hvertex s hs
      _ = _ := by rw [sum_ite_mem_faces K L hLK]; ring
  have hcount := sum_faceEulerChar_link_vertices K hd
  linarith

open Classical in
theorem faceEulerChar_eq_two_mul_of_link_counts (hLK : L ≤ K)
    (hK : ∀ u ∈ K, u.card ≤ 4) (hL : ∀ u ∈ L, u.card ≤ 3)
    (htri : ∀ s ∈ facesOfCard K 3, (cofaces K s 4).card = if s ∈ L then 1 else 2)
    (hedge : ∀ s ∈ facesOfCard K 2,
      faceEulerChar (link K s) = if s ∈ L then 1 else 0)
    (hvertex : ∀ s ∈ facesOfCard K 1,
      faceEulerChar (link K s) = if s ∈ L then 1 else 2) :
    faceEulerChar L = 2 * faceEulerChar K := by
  rw [faceEulerChar_eq_of_card_le_three L hL, faceEulerChar_eq_of_card_le_four K hK,
    card_boundary_triangles K L hLK htri, card_boundary_edges K L hLK hK hedge,
    card_boundary_vertices K L hLK hK hvertex]
  ring

end

end Poincare.Topology.SimplicialComplex

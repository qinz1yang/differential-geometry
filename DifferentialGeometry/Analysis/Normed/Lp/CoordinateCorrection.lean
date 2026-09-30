import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Real

theorem dist_le_mul_of_directed_step {x y w α : ℝ}
    (h : if w ≤ x then
      α * dist x w ≤ x - y ∧ x - y ≤ dist x w
    else α * dist x w ≤ y - x ∧ y - x ≤ dist x w) :
    dist y w ≤ (1 - α) * dist x w := by
  by_cases hw : w ≤ x
  · rw [ite_eq_left hw, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hw)] at h
    have hy : w ≤ y := by linarith [h.2]
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hw),
      abs_of_nonneg (sub_nonneg.mpr hy)]
    nlinarith [h.1]
  · have hx : x ≤ w := (lt_of_not_ge hw).le
    rw [ite_eq_right hw, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx)] at h
    have hy : y ≤ w := by linarith [h.2]
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx),
      abs_of_nonpos (sub_nonpos.mpr hy)]
    nlinarith [h.1]

end Real

namespace PiLp

variable {ι : Type*} [Fintype ι]

theorem dist_le_sub_of_coordinate_correction
    {x y w : PiLp 1 (fun _ : ι => ℝ)} (i : ι) {α β : ℝ}
    (hi : dist (y i) (w i) ≤ (1 - α) * dist (x i) (w i))
    (hrest : ∀ j ≠ i, dist (y j) (x j) ≤ β * dist (x i) (w i)) :
    dist y w ≤ dist x w - (α - (Fintype.card ι - 1 : ℝ) * β) * dist (x i) (w i) := by
  classical
  have hsum : ∑ j ∈ univ.erase i, dist (y j) (w j) ≤
      ∑ j ∈ univ.erase i, dist (x j) (w j) +
        (Fintype.card ι - 1 : ℝ) * (β * dist (x i) (w i)) := by
    calc
      _ ≤ ∑ j ∈ univ.erase i, (dist (x j) (w j) + β * dist (x i) (w i)) := by
        apply sum_le_sum
        intro j hj
        exact (dist_triangle (y j) (x j) (w j)).trans
          (by linarith [hrest j (mem_erase.mp hj).1])
      _ = _ := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ i)]
        simp only [card_univ]
        rw [Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i⟩), Nat.cast_one]
  have hx := sum_erase_add univ (fun j => dist (x j) (w j)) (mem_univ i)
  have hy := sum_erase_add univ (fun j => dist (y j) (w j)) (mem_univ i)
  rw [dist_eq_of_L1, dist_eq_of_L1]
  change (∑ j, dist (y j) (w j)) ≤ _
  nlinarith

theorem dist_le_mul_of_largest_coordinate_correction
    {x y w : PiLp 1 (fun _ : ι => ℝ)} (i : ι) {α β : ℝ}
    (hμ : 0 ≤ α - (Fintype.card ι - 1 : ℝ) * β)
    (hmax : ∀ j, dist (x j) (w j) ≤ dist (x i) (w i))
    (hi : dist (y i) (w i) ≤ (1 - α) * dist (x i) (w i))
    (hrest : ∀ j ≠ i, dist (y j) (x j) ≤ β * dist (x i) (w i)) :
    dist y w ≤ (1 - (α - (Fintype.card ι - 1 : ℝ) * β) / Fintype.card ι) * dist x w := by
  have hm : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hsum : dist x w ≤ Fintype.card ι * dist (x i) (w i) := by
    rw [dist_eq_of_L1]
    simpa using sum_le_sum (s := univ) (fun j _ => hmax j)
  have hdiv : dist x w / Fintype.card ι ≤ dist (x i) (w i) := (div_le_iff₀ hm).mpr (by simpa [mul_comm] using hsum)
  have hmul := mul_le_mul_of_nonneg_left hdiv hμ
  have h := dist_le_sub_of_coordinate_correction i hi hrest
  calc
    dist y w ≤ dist x w - (α - (Fintype.card ι - 1 : ℝ) * β) * dist (x i) (w i) := h
    _ ≤ dist x w - (α - (Fintype.card ι - 1 : ℝ) * β) * (dist x w / Fintype.card ι) := by linarith
    _ = _ := by ring

end PiLp

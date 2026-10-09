import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Real
open scoped BigOperators

namespace PiLp

theorem card_le_of_bounded_separated_family {ι : Type*} [Fintype ι] {m : ℕ}
    (hm : 0 < m) (f : ι → PiLp 2 (fun _ : Fin m => ℝ)) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) (hnorm : ∀ x, ‖f x‖ ≤ B)
    (hsep : ∀ x y, x ≠ y → ε ≤ dist (f x) (f y)) :
    (Fintype.card ι : ℝ) ≤ (1 + 4 * B * sqrt m / ε) ^ m := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < sqrt (m : ℝ) := sqrt_pos.mpr hmR
  let h := ε / (2 * sqrt m)
  have hh : 0 < h := div_pos hε (by positivity)
  have hcoord (x : ι) (i : Fin m) : |f x i| ≤ B := by
    exact (norm_apply_le (f x) i).trans (hnorm x)
  have hnonneg (x : ι) (i : Fin m) : 0 ≤ (f x i + B) / h :=
    div_nonneg (by linarith [(abs_le.mp (hcoord x i)).1]) hh.le
  have hbound (x : ι) (i : Fin m) : (f x i + B) / h ≤ 2 * B / h := by
    apply div_le_div_of_nonneg_right _ hh.le
    linarith [(abs_le.mp (hcoord x i)).2]
  let N := ⌊2 * B / h⌋₊ + 1
  let label : ι → Fin m → Fin N := fun x i =>
    ⟨⌊(f x i + B) / h⌋₊, Nat.lt_succ_of_le (Nat.floor_mono (hbound x i))⟩
  have hdiff (x y : ι) (heq : label x = label y) (i : Fin m) : |f x i - f y i| < h := by
    have hfloor : (⌊(f x i + B) / h⌋₊ : ℝ) = ⌊(f y i + B) / h⌋₊ := by
      exact_mod_cast congrArg Fin.val (congrFun heq i)
    have hxlo := (le_div_iff₀ hh).mp (Nat.floor_le (hnonneg x i))
    have hylo := (le_div_iff₀ hh).mp (Nat.floor_le (hnonneg y i))
    have hxhi := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((f x i + B) / h))
    have hyhi := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((f y i + B) / h))
    rw [hfloor] at hxlo hxhi
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  have hscale : (m : ℝ) * h ^ 2 = ε ^ 2 / 4 := by
    dsimp [h]
    rw [div_pow, mul_pow, sq_sqrt hmR.le]
    field_simp
    ring
  have hinj : Function.Injective label := by
    intro x y heq
    by_contra hxy
    have hsum : dist (f x) (f y) ^ 2 ≤ (m : ℝ) * h ^ 2 := by
      rw [dist_sq_eq_of_L2]
      have hhcoord (i : Fin m) : dist (f x i) (f y i) ^ 2 ≤ h ^ 2 := by
        rw [Real.dist_eq]
        exact (sq_le_sq₀ (abs_nonneg _) hh.le).mpr (hdiff x y heq i).le
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hhcoord i)
    rw [hscale] at hsum
    have hsep' := hsep x y hxy
    have hsq := (sq_le_sq₀ hε.le dist_nonneg).mpr hsep'
    nlinarith [sq_pos_of_pos hε]
  have hcard : Fintype.card ι ≤ N ^ m := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective label hinj
  have hN : (N : ℝ) ≤ 1 + 4 * B * sqrt m / ε := by
    have hf := Nat.floor_le (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB) hh.le)
    have heq : 2 * B / h = 4 * B * sqrt m / ε := by
      dsimp [h]
      field_simp
      ring
    dsimp [N]
    push_cast
    rw [heq] at hf ⊢
    linarith
  exact (by exact_mod_cast hcard : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ m).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg N) hN m)

end PiLp

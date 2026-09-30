import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx]

def compNormSqMulti {r : ℕ} (A : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, (A m) ^ 2

theorem compNormSqMulti_nonneg {r : ℕ} (A : (Fin r → Idx) → Real) :
    0 ≤ compNormSqMulti A := by
  unfold compNormSqMulti
  exact Finset.sum_nonneg fun m _ => sq_nonneg _

theorem sq_le_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    (A m) ^ 2 ≤ compNormSqMulti A := by
  classical
  unfold compNormSqMulti
  exact Finset.single_le_sum (f := fun m' : Fin r → Idx => (A m') ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ m)

theorem abs_le_sqrt_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    |A m| ≤ Real.sqrt (compNormSqMulti A) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSqMulti A m)

theorem abs_bilinear_sum_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → κ → Real) (X : ι → Real) (Y : κ → Real)
    (C : Real) (hC : 0 ≤ C)
    (hF : ∀ i j, |F i j| ≤ C) :
    |∑ i, ∑ j, F i j * X i * Y j| ≤
      C / 2 *
        ((Fintype.card κ : Real) * (∑ i, (X i) ^ 2) +
          (Fintype.card ι : Real) * (∑ j, (Y j) ^ 2)) := by
  classical
  calc
    |∑ i, ∑ j, F i j * X i * Y j| ≤
        ∑ i, |∑ j, F i j * X i * Y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |F i j * X i * Y j| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, C / 2 * ((X i) ^ 2 + (Y j) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul]
      have hxy : 2 * |X i| * |Y j| ≤ (X i) ^ 2 + (Y j) ^ 2 := by
        simpa only [sq_abs] using two_mul_le_add_sq |X i| |Y j|
      have hnonneg : 0 ≤ |X i| * |Y j| :=
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hcoeff : |F i j| * (|X i| * |Y j|) ≤
          C * (|X i| * |Y j|) :=
        mul_le_mul_of_nonneg_right (hF i j) hnonneg
      calc
        |F i j| * |X i| * |Y j| =
            |F i j| * (|X i| * |Y j|) := by ring
        _ ≤ C * (|X i| * |Y j|) := hcoeff
        _ ≤ C / 2 * ((X i) ^ 2 + (Y j) ^ 2) := by
          nlinarith
    _ = C / 2 *
        ((Fintype.card κ : Real) * (∑ i, (X i) ^ 2) +
          (Fintype.card ι : Real) * (∑ j, (Y j) ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      have hX :
          (∑ i, C / 2 * (X i) ^ 2) =
            C / 2 * (∑ i, (X i) ^ 2) := by
        rw [Finset.mul_sum]
      have hY :
          (∑ j, C / 2 * (Y j) ^ 2) =
            C / 2 * (∑ j, (Y j) ^ 2) := by
        rw [Finset.mul_sum]
      have hXcard :
          (∑ i, (Fintype.card κ : Real) *
              (C / 2 * (X i) ^ 2)) =
            (Fintype.card κ : Real) *
              (∑ i, C / 2 * (X i) ^ 2) := by
        rw [Finset.mul_sum]
      rw [hXcard, hX, hY]
      ring

theorem abs_quadratic_sum_le
    {ι : Type*} [Fintype ι]
    (F : ι → ι → Real) (X : ι → Real)
    (C : Real) (hC : 0 ≤ C)
    (hF : ∀ i j, |F i j| ≤ C) :
    |∑ i, ∑ j, F i j * X i * X j| ≤
      C * (Fintype.card ι : Real) * (∑ i, (X i) ^ 2) := by
  have h := abs_bilinear_sum_le F X X C hC hF
  convert h using 1
  ring

theorem abs_sum_le_card_mul_of_bound
    {ι : Type*} [Fintype ι]
    (f : ι → Real) (C : Real)
    (h : ∀ i, |f i| ≤ C) :
    |∑ i, f i| ≤ (Fintype.card ι : Real) * C := by
  classical
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card ι : Real) * C := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem abs_double_sum_le_card_mul_card_mul_of_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → Real) (C : Real)
    (h : ∀ i j, |f i j| ≤ C) :
    |∑ i, ∑ j, f i j| ≤
      (Fintype.card ι : Real) * (Fintype.card κ : Real) * C := by
  have houter := abs_sum_le_card_mul_of_bound
    (fun i => ∑ j, f i j) ((Fintype.card κ : Real) * C)
    (fun i => abs_sum_le_card_mul_of_bound (f i) C (h i))
  simpa only [mul_assoc] using houter

end Tensor0SBundle
end DifferentialGeometry

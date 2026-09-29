import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open scoped BigOperators

namespace Matrix

variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

def entrywiseL1 (A : Matrix ι κ ℝ) : ℝ :=
  ∑ pq : ι × κ, |A pq.1 pq.2|

lemma entrywiseL1_nonneg (A : Matrix ι κ ℝ) : 0 ≤ entrywiseL1 A :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma abs_entry_le_entrywiseL1 (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    |A i j| ≤ entrywiseL1 A := by
  classical
  exact Finset.single_le_sum
    (f := fun pq : ι × κ => |A pq.1 pq.2|)
    (fun pq _ => abs_nonneg _) (Finset.mem_univ (i, j))

end Matrix

theorem _root_.Matrix.inv_entry_sub_abs_le_of_entry_bound
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) (hB : IsUnit B) {M D : ℝ}
    (hMinvA : ∀ p q, |A⁻¹ p q| ≤ M) (hMinvB : ∀ p q, |B⁻¹ p q| ≤ M)
    (hD : ∀ p q, |(B - A) p q| ≤ D) (i j : Fin n) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (n : ℝ) ^ 2 * M ^ 2 * D := by
  classical
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hMinvA i j)
  have hD_nonneg : 0 ≤ D :=
    le_trans (abs_nonneg ((B - A) i j)) (hD i j)
  have hAB : IsUnit A ↔ IsUnit B := ⟨fun _ => hB, fun _ => hA⟩
  have h_id : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv hAB
  have h_entry : A⁻¹ i j - B⁻¹ i j = (A⁻¹ * (B - A) * B⁻¹) i j := by
    have := congrArg (fun (X : Matrix (Fin n) (Fin n) ℝ) => X i j) h_id
    simpa using this
  have h_expand : (A⁻¹ * (B - A) * B⁻¹) i j =
      ∑ q : Fin n, ∑ p : Fin n,
        A⁻¹ i p * (B - A) p q * B⁻¹ q j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [h_entry, h_expand]
  calc |∑ q : Fin n, ∑ p : Fin n, A⁻¹ i p * (B - A) p q * B⁻¹ q j|
      ≤ ∑ q : Fin n, |∑ p : Fin n, A⁻¹ i p * (B - A) p q * B⁻¹ q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Fin n, ∑ p : Fin n, |A⁻¹ i p * (B - A) p q * B⁻¹ q j| := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Fin n, ∑ p : Fin n, M * D * M := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [abs_mul, abs_mul]
        have h1 : |A⁻¹ i p| ≤ M := hMinvA i p
        have h2 : |(B - A) p q| ≤ D := hD p q
        have h3 : |B⁻¹ q j| ≤ M := hMinvB q j
        have hstep : |A⁻¹ i p| * |(B - A) p q| ≤ M * D :=
          mul_le_mul h1 h2 (abs_nonneg _) hM_nonneg
        calc |A⁻¹ i p| * |(B - A) p q| * |B⁻¹ q j|
            ≤ (M * D) * |B⁻¹ q j| :=
              mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
          _ ≤ (M * D) * M :=
              mul_le_mul_of_nonneg_left h3
                (mul_nonneg hM_nonneg hD_nonneg)
    _ = (n : ℝ) ^ 2 * M ^ 2 * D := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

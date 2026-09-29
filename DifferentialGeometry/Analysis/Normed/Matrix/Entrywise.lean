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

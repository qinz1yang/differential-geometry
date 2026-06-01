import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Algebraic Σ-swap identities on `Finset` sums

This file collects a small library of purely algebraic identities that
re-arrange iterated `Finset` sums of products. They are pure
`Finset.mul_sum` / `Finset.sum_mul` consequences and are used by the
chart-coordinate assembly steps in the tensor regularity development,
where iterated sums over chart indices and frame indices have to be
combined into a single sum over a renamed pair of indices.

Each headline states an equality of the form

`(∑ over outer factor A) · (∑ over inner factor B · X) =
   ∑ over the "inner" indices, of (∑ over the "outer" indices, of A · B) · X`.

The `A`, `B`, `X` arguments are concrete real-valued functions; the proofs
only use ring associativity together with `Finset.mul_sum` and
`Finset.sum_mul`.

## Main results

* `Finset.sum_mul_inner_triple_sum_swap` — the `Σ_5` swap with a
  triple-index inner sum.
* `Finset.sum_mul_inner_double_sum_swap` — the `Σ_4` swap with a
  double-index inner sum.
* `Finset.sum_mul_inner_triple_swap_two_inner` — the `Σ_5` swap with a
  triple-index outer sum and a double-index inner sum.
* `single_eq_sum_diracPair` — the "Kronecker collapse" identity rewriting
  a single evaluation `X (Idx, Jdx)` as a double sum weighted by a
  pair-Kronecker delta.
-/

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {K L I J M I' J' : Type*}

/-- `Σ_5` swap with multiplicative distribute (double-index outer factor,
triple-index inner sum).

`Σ_{k, l} A k l · (Σ_{i, j, m} B i j m · X i j m)
   = Σ_{i, j, m} ((Σ_{k, l} A k l) · B i j m) · X i j m`. -/
theorem Finset.sum_mul_inner_triple_sum_swap
    [Fintype K] [Fintype L] [Fintype I] [Fintype J] [Fintype M]
    (A : K → L → ℝ) (B : I → J → M → ℝ) (X : I → J → M → ℝ) :
    (∑ k : K, ∑ l : L, A k l *
        ∑ i : I, ∑ j : J, ∑ m : M, B i j m * X i j m) =
      ∑ i : I, ∑ j : J, ∑ m : M,
        ((∑ k : K, ∑ l : L, A k l) * B i j m) * X i j m := by
  have hSumMul :
      (∑ k : K, ∑ l : L, A k l *
            ∑ i : I, ∑ j : J, ∑ m : M, B i j m * X i j m)
        = (∑ k : K, ∑ l : L, A k l) *
            (∑ i : I, ∑ j : J, ∑ m : M, B i j m * X i j m) := by
    simp_rw [_root_.Finset.sum_mul]
  have hDistI :
      (∑ k : K, ∑ l : L, A k l) *
          (∑ i : I, ∑ j : J, ∑ m : M, B i j m * X i j m)
        = ∑ i : I, ∑ j : J, ∑ m : M,
            ((∑ k : K, ∑ l : L, A k l) * B i j m) * X i j m := by
    simp_rw [_root_.Finset.mul_sum, ← mul_assoc]
  rw [hSumMul, hDistI]

/-- `Σ_4` swap with multiplicative distribute (double-index outer factor,
double-index inner sum).

`Σ_{k, l} A k l · (Σ_{i, j} B i j · X i j)
   = Σ_{i, j} ((Σ_{k, l} A k l) · B i j) · X i j`. -/
theorem Finset.sum_mul_inner_double_sum_swap
    [Fintype K] [Fintype L] [Fintype I] [Fintype J]
    (A : K → L → ℝ) (B : I → J → ℝ) (X : I → J → ℝ) :
    (∑ k : K, ∑ l : L, A k l *
        ∑ i : I, ∑ j : J, B i j * X i j) =
      ∑ i : I, ∑ j : J,
        ((∑ k : K, ∑ l : L, A k l) * B i j) * X i j := by
  have hSumMul :
      (∑ k : K, ∑ l : L, A k l *
            ∑ i : I, ∑ j : J, B i j * X i j)
        = (∑ k : K, ∑ l : L, A k l) *
            (∑ i : I, ∑ j : J, B i j * X i j) := by
    simp_rw [_root_.Finset.sum_mul]
  have hDistI :
      (∑ k : K, ∑ l : L, A k l) *
          (∑ i : I, ∑ j : J, B i j * X i j)
        = ∑ i : I, ∑ j : J,
            ((∑ k : K, ∑ l : L, A k l) * B i j) * X i j := by
    simp_rw [_root_.Finset.mul_sum, ← mul_assoc]
  rw [hSumMul, hDistI]

/-- `Σ_5` swap with multiplicative distribute (triple-index outer factor,
double-index inner sum).

`Σ_{i, l, k} C i l k · (Σ_{i', j'} D i' j' · X i' j')
   = Σ_{i', j'} ((Σ_{i, l, k} C i l k) · D i' j') · X i' j'`. -/
theorem Finset.sum_mul_inner_triple_swap_two_inner
    [Fintype I] [Fintype L] [Fintype K] [Fintype I'] [Fintype J']
    (C : I → L → K → ℝ) (D : I' → J' → ℝ) (X : I' → J' → ℝ) :
    (∑ i : I, ∑ l : L, ∑ k : K, C i l k *
        ∑ i' : I', ∑ j' : J', D i' j' * X i' j') =
      ∑ i' : I', ∑ j' : J',
        ((∑ i : I, ∑ l : L, ∑ k : K, C i l k) * D i' j') * X i' j' := by
  have hSumMul :
      (∑ i : I, ∑ l : L, ∑ k : K, C i l k *
            ∑ i' : I', ∑ j' : J', D i' j' * X i' j')
        = (∑ i : I, ∑ l : L, ∑ k : K, C i l k) *
            (∑ i' : I', ∑ j' : J', D i' j' * X i' j') := by
    simp_rw [_root_.Finset.sum_mul]
  have hDistI :
      (∑ i : I, ∑ l : L, ∑ k : K, C i l k) *
          (∑ i' : I', ∑ j' : J', D i' j' * X i' j')
        = ∑ i' : I', ∑ j' : J',
            ((∑ i : I, ∑ l : L, ∑ k : K, C i l k) * D i' j') * X i' j' := by
    simp_rw [_root_.Finset.mul_sum, ← mul_assoc]
  rw [hSumMul, hDistI]

/-- Kronecker collapse for a pair of indices.

`X (Idx, Jdx) = Σ_{i', j'} (if (i', j') = (Idx, Jdx) then 1 else 0) · X (i', j')`.

This rewrites a single evaluation of `X` at a fixed pair `(Idx, Jdx)` as a
double sum weighted by the pair-Kronecker delta. It lets a single
chart-component evaluation be presented in the same "Σ over (i', j')" shape
as the other terms of an assembly. -/
theorem single_eq_sum_diracPair
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (X : I' → J' → ℝ) (Idx : I') (Jdx : J') :
    X Idx Jdx =
      ∑ i' : I', ∑ j' : J',
        (if (i', j') = (Idx, Jdx) then (1 : ℝ) else 0) * X i' j' := by
  have hJ :
      ∀ i' : I',
        (∑ j' : J',
            (if (i', j') = (Idx, Jdx) then (1 : ℝ) else 0) * X i' j')
          = (if i' = Idx then (1 : ℝ) else 0) * X i' Jdx := by
    intro i'
    rw [Finset.sum_eq_single Jdx]
    · by_cases hi : i' = Idx
      · subst hi
        simp
      · simp [hi]
    · intro j' _ hjne
      have hne : ¬ ((i', j') = (Idx, Jdx)) := by
        intro hpair
        exact hjne (Prod.mk_inj.mp hpair).2
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  calc
    X Idx Jdx
        = (1 : ℝ) * X Idx Jdx := by ring
    _ = (if (Idx : I') = Idx then (1 : ℝ) else 0) * X Idx Jdx := by
          simp
    _ = ∑ i' : I',
          (if i' = Idx then (1 : ℝ) else 0) * X i' Jdx := by
          rw [Finset.sum_eq_single Idx]
          · intro i' _ hine
            simp [hine]
          · intro hnot
            exact (hnot (Finset.mem_univ _)).elim
    _ = ∑ i' : I', ∑ j' : J',
          (if (i', j') = (Idx, Jdx) then (1 : ℝ) else 0) * X i' j' := by
          refine Finset.sum_congr rfl (fun i' _ => ?_)
          exact (hJ i').symm

end DifferentialGeometry.Analysis.Laplacian.TensorRegularity

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Hilbert-Schmidt bound dominates operator norm for continuous multilinear maps

This file proves that for a finite-dimensional real inner-product space `E` with an
orthonormal basis `b : OrthonormalBasis ι ℝ E` and a continuous multilinear map
`A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ`, the square of the operator
norm of `A` is bounded above by the sum of squares of its values on all basis-index
tuples:

```
‖A‖² ≤ ∑ idx : Fin j → ι, |A (fun k => b (idx k))|²
```

This is the classical inequality "operator norm ≤ Hilbert-Schmidt norm" specialised to
multilinear maps on a finite-dimensional inner-product space, and is the foundational
pointwise estimate underlying all chart-by-chart bounds that convert pointwise
Hilbert-Schmidt squared-norm sums into operator-norm bounds for iterated derivatives.

## Main theorem

* `ContinuousMultilinearMap.opNorm_sq_le_sum_sq_basisEval`:
  `‖A‖^2 ≤ ∑ idx : Fin j → ι, |A (fun k => b (idx k))|^2`.
-/

noncomputable section

open Finset
open scoped BigOperators RealInnerProductSpace

namespace ContinuousMultilinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
**Hilbert-Schmidt vs operator norm**, pointwise form on a finite-dimensional inner-product
space.

Given an orthonormal basis `b : OrthonormalBasis ι ℝ E` on a finite-dimensional real
inner-product space and a continuous `j`-multilinear map `A : (Fin j → E) → ℝ`, the
square of the operator norm of `A` is bounded by the (Hilbert-Schmidt-type) sum of
squares of its values on all basis-index tuples:

`‖A‖² ≤ ∑ idx : Fin j → ι, |A (fun k => b (idx k))|²`.

This is the standard inequality: any `v : Fin j → E` expands in the basis as
`v k = ∑ i, ⟪b i, v k⟫ • b i`, and multilinearity together with Cauchy–Schwarz on the
index tuple and Parseval's identity on each slot yield the pointwise estimate
`|A v|² ≤ S · ∏ k, ‖v k‖²` where `S` is the right-hand-side sum. The conclusion
follows from `opNorm_le_bound`.
-/
theorem opNorm_sq_le_sum_sq_basisEval
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) :
    ‖A‖ ^ 2 ≤ ∑ idx : Fin j → ι, |A (fun k => b (idx k))| ^ 2 := by
  classical
  -- Abbreviation for the right-hand-side sum and a name for its square root.
  set S : ℝ := ∑ idx : Fin j → ι, |A (fun k => b (idx k))| ^ 2 with hS_def
  have hS_nonneg : 0 ≤ S := by
    refine Finset.sum_nonneg ?_
    intro idx _
    exact sq_nonneg _
  -- Step 1: pointwise bound `|A v| ≤ Real.sqrt S * ∏ k, ‖v k‖`.
  have hpoint : ∀ v : Fin j → E, ‖A v‖ ≤ Real.sqrt S * ∏ k, ‖v k‖ := by
    intro v
    -- Expand each `v k` in the orthonormal basis.
    have hv : ∀ k : Fin j, v k = ∑ i : ι, ⟪b i, v k⟫ • b i := by
      intro k
      exact (b.sum_repr' (v k)).symm
    -- Apply the multilinear map to the expanded form using `map_sum` from the
    -- underlying `MultilinearMap`, then pull each scalar factor out via
    -- `map_smul_univ`.
    have hAv : A v = ∑ idx : Fin j → ι,
        (∏ k : Fin j, ⟪b (idx k), v k⟫) • A (fun k => b (idx k)) := by
      have hexp : A v = A (fun k => ∑ i : ι, ⟪b i, v k⟫ • b i) := by
        refine congrArg A ?_
        funext k
        exact hv k
      -- Use `MultilinearMap.map_sum`.
      have hstep1 : A (fun k => ∑ i : ι, ⟪b i, v k⟫ • b i)
          = ∑ idx : Fin j → ι, A (fun k => ⟪b (idx k), v k⟫ • b (idx k)) := by
        have := A.toMultilinearMap.map_sum
          (g := fun (k : Fin j) (i : ι) => ⟪b i, v k⟫ • b i)
        -- `A` and `A.toMultilinearMap` coerce to the same function.
        simpa using this
      have hstep2 : ∀ idx : Fin j → ι,
          A (fun k => ⟪b (idx k), v k⟫ • b (idx k))
            = (∏ k : Fin j, ⟪b (idx k), v k⟫) • A (fun k => b (idx k)) := by
        intro idx
        exact A.map_smul_univ
          (fun k : Fin j => ⟪b (idx k), v k⟫) (fun k : Fin j => b (idx k))
      rw [hexp, hstep1]
      exact Finset.sum_congr rfl fun idx _ => hstep2 idx
    -- For ℝ-valued `A`, `‖A v‖ = |A v|`.
    have hAv_abs : ‖A v‖ = |A v| := Real.norm_eq_abs _
    -- Bound `|A v|` via Cauchy–Schwarz on the index sum.
    have habs : |A v|
        = |∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))| := by
      have : A v = ∑ idx : Fin j → ι,
          (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k)) := by
        rw [hAv]
        refine Finset.sum_congr rfl ?_
        intro idx _
        rw [smul_eq_mul]
      rw [this]
    -- Square version of Cauchy–Schwarz on finsets.
    have hCS : (∑ idx : Fin j → ι,
        (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2
        ≤ (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) *
          (∑ idx : Fin j → ι, A (fun k => b (idx k)) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin j → ι))
        (fun idx => ∏ k : Fin j, ⟪b (idx k), v k⟫)
        (fun idx => A (fun k => b (idx k)))
    have hS_eq : S = ∑ idx : Fin j → ι, A (fun k => b (idx k)) ^ 2 := by
      rw [hS_def]
      refine Finset.sum_congr rfl ?_
      intro idx _
      rw [sq_abs]
    have hCS' : (∑ idx : Fin j → ι,
        (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2
        ≤ (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) * S := by
      rw [hS_eq]; exact hCS
    -- Take square roots: `|x| = √(x²) ≤ √(C · S) = √C · √S`.
    have hsumC_nonneg :
        0 ≤ ∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsqrt_le :
        Real.sqrt ((∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2)
          ≤ Real.sqrt
            ((∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) * S) :=
      Real.sqrt_le_sqrt hCS'
    have heq1 :
        Real.sqrt ((∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2)
        = |∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))| := by
      rw [Real.sqrt_sq_eq_abs]
    have heq2 :
        Real.sqrt
          ((∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) * S)
        = Real.sqrt
            (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2)
          * Real.sqrt S :=
      Real.sqrt_mul hsumC_nonneg _
    rw [heq1, heq2] at hsqrt_le
    -- Identify the inner-product sum with `∏ k, ‖v k‖²` via Parseval.
    have hParseval :
        ∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2
          = ∏ k : Fin j, ‖v k‖ ^ 2 := by
      -- First: `(∏ k, c k)^2 = ∏ k, (c k)^2`.
      have hsq :
          ∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2
          = ∑ idx : Fin j → ι, ∏ k : Fin j, ⟪b (idx k), v k⟫ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro idx _
        rw [← Finset.prod_pow]
      -- Second: `∑ idx, ∏ k, f k (idx k) = ∏ k, ∑ i, f k i`.
      have hprod_sum :
          ∑ idx : Fin j → ι, ∏ k : Fin j, ⟪b (idx k), v k⟫ ^ 2
          = ∏ k : Fin j, ∑ i : ι, ⟪b i, v k⟫ ^ 2 := by
        have h := (Finset.prod_univ_sum
          (κ := fun _ : Fin j => ι)
          (t := fun _ : Fin j => (Finset.univ : Finset ι))
          (f := fun k i => ⟪b i, v k⟫ ^ 2))
        -- `Finset.piFinset (fun _ => univ) = univ`.
        have hpi : (Fintype.piFinset (fun _ : Fin j => (Finset.univ : Finset ι)))
                    = (Finset.univ : Finset (Fin j → ι)) := by
          ext idx; simp
        rw [h, hpi]
      -- Third: each slot is `‖v k‖²` by Parseval.
      have hslot : ∀ k : Fin j, ∑ i : ι, ⟪b i, v k⟫ ^ 2 = ‖v k‖ ^ 2 := by
        intro k
        exact b.sum_sq_inner_right (v k)
      rw [hsq, hprod_sum]
      refine Finset.prod_congr rfl ?_
      intro k _
      exact hslot k
    -- Combine.
    have hsqrt_prod :
        Real.sqrt (∏ k : Fin j, ‖v k‖ ^ 2) = ∏ k : Fin j, ‖v k‖ := by
      have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin j)), 0 ≤ ‖v k‖ ^ 2 :=
        fun k _ => sq_nonneg _
      rw [Real.sqrt_prod (Finset.univ : Finset (Fin j)) hnonneg]
      refine Finset.prod_congr rfl ?_
      intro k _
      rw [Real.sqrt_sq (norm_nonneg _)]
    -- Chain the inequalities:
    -- `‖A v‖ = |A v| = |∑ ...| ≤ √(∑ C²) · √S = √(∏ ‖v k‖²) · √S = (∏ ‖v k‖) · √S`.
    calc ‖A v‖
        = |A v| := hAv_abs
      _ = |∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))| := habs
      _ ≤ Real.sqrt
            (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2)
          * Real.sqrt S := hsqrt_le
      _ = Real.sqrt (∏ k : Fin j, ‖v k‖ ^ 2) * Real.sqrt S := by rw [hParseval]
      _ = (∏ k : Fin j, ‖v k‖) * Real.sqrt S := by rw [hsqrt_prod]
      _ = Real.sqrt S * ∏ k : Fin j, ‖v k‖ := by ring
  -- Step 2: from the pointwise bound deduce `‖A‖ ≤ Real.sqrt S`.
  have hopNorm_le : ‖A‖ ≤ Real.sqrt S := by
    refine ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _) ?_
    intro v
    exact hpoint v
  -- Step 3: square both sides.
  have hopNorm_nonneg : 0 ≤ ‖A‖ := norm_nonneg _
  have hsq : ‖A‖ ^ 2 ≤ (Real.sqrt S) ^ 2 :=
    pow_le_pow_left₀ hopNorm_nonneg hopNorm_le 2
  have hsqrt_sq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS_nonneg
  rw [hsqrt_sq] at hsq
  exact hsq

end ContinuousMultilinearMap

end

import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev

/-!
# Order-`k` decomposition of the iterated Euclidean Sobolev norm

The iterated norm `wkpNorm k p u Ω` is, by definition, the double sum

`∑_{j ≤ k} ∑_{α : Fin j → Fin d} eLpNorm (iterWeakPartial p j α u Ω) p (volume.restrict Ω)`.

Here we expose two structural reorganisations of this aggregate that downstream
component bounds consume:

* `wkpNorm_split_order_zero`: the `j = 0` term contributes exactly
  `eLpNorm u p (volume.restrict Ω)`, separating the `L^p`-piece from the
  positive-order partials.
* `wkpNorm_k_two_decomposition` (and its general-exponent companion
  `wkpNorm_k_decomposition`): the full order-`k` norm written as the `L^p`-norm
  of `u` plus the sum, over orders `1 ≤ j ≤ k` and basis multi-indices, of the
  `L^p`-norms of the iterated weak partials.

These are pure rearrangements of the definition: no analytical hypothesis is
needed. They generalise the order-one form
`eLpNorm u + ∑_i eLpNorm (chosenWeakPartial' i u)` to arbitrary order.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The order-`0` slice of `wkpNorm` — the sum over the unique empty
multi-index `α : Fin 0 → Fin d` — is just `eLpNorm u`. This is the building
block that lets us peel the `L^p`-piece off the iterated norm. -/
private theorem order_zero_sum_eq_eLpNorm
    (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    ∑ α : Fin 0 → Fin d,
        eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω) =
      eLpNorm u p (volume.restrict Ω) := by
  classical
  have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
    funext i; exact i.elim0
  haveI : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (hUniq α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
  simp [iterWeakPartial_zero]

/-- Split `wkpNorm` of any order `k` into its order-zero `L^p`-piece and the
sum of the positive-order slices `1 ≤ j ≤ k`. -/
theorem wkpNorm_split_order_zero
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNorm (d := d) k p u Ω =
      eLpNorm u p (volume.restrict Ω) +
        ∑ j ∈ Finset.range k,
          ∑ α : Fin (j + 1) → Fin d,
            eLpNorm (iterWeakPartial (d := d) p (j + 1) α u Ω)
              p (volume.restrict Ω) := by
  classical
  unfold wkpNorm
  rw [Finset.sum_range_succ']
  rw [order_zero_sum_eq_eLpNorm (d := d) p u Ω]
  rw [add_comm]

/-- **Order-`k` decomposition of the iterated Sobolev norm** (general exponent).
`wkpNorm k p u Ω` equals the `L^p`-norm of `u` plus the aggregate, over all
positive orders `1 ≤ j ≤ k` and all basis multi-indices `α : Fin j → Fin d`, of
the `L^p`-norms of the iterated weak partials `iterWeakPartial p j α u Ω`.

This is the order-`k` generalisation of `wkpNorm_one_two_decomposition`: it is a
pure reindexing of the defining double sum, separating the order-zero term as
the `L^p`-piece. -/
theorem wkpNorm_k_decomposition
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNorm (d := d) k p u Ω =
      eLpNorm u p (volume.restrict Ω) +
        ∑ j ∈ Finset.Icc 1 k,
          ∑ α : Fin j → Fin d,
            eLpNorm (iterWeakPartial (d := d) p j α u Ω)
              p (volume.restrict Ω) := by
  classical
  rw [wkpNorm_split_order_zero (d := d) k p u Ω]
  congr 1
  rw [Finset.sum_bij (i := fun (j : ℕ) (_ : j ∈ Finset.range k) => j + 1)]
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    omega
  · intro j₁ _ j₂ _ h
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  · intro j _
    rfl

/-- **Order-`k` decomposition at exponent `2`.** The `L^2` chart Sobolev norm of
order `k`, decomposed as the `L^2`-norm of `u` plus the aggregate of the
`L^2`-norms of all iterated weak partials of orders `1 ≤ j ≤ k`. This is the
structural form consumed by the order-`k` component Sobolev bound. -/
theorem wkpNorm_k_two_decomposition
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNorm (d := d) k 2 u Ω =
      eLpNorm u 2 (volume.restrict Ω) +
        ∑ j ∈ Finset.Icc 1 k,
          ∑ α : Fin j → Fin d,
            eLpNorm (iterWeakPartial (d := d) 2 j α u Ω)
              2 (volume.restrict Ω) :=
  wkpNorm_k_decomposition (d := d) k 2 u Ω

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry

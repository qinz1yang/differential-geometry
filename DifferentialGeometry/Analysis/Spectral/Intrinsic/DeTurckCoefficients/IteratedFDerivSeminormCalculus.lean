import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedFDerivProductDifferenceBound

/-!
# Seminorm calculus for the all-order chart-jet estimate

The order-`N` iterated-derivative seminorm `iteratedFDerivSeminorm N f s y` of a scalar
field obeys the expected sub-additivity and product rules, which the all-order
(Faà-di-Bruno) chart-jet estimate assembles term by term.  Two structural facts are
isolated here:

* **Sub-additivity through a finite sum** — the seminorm of a finite sum of `ContDiffOn`
  fields is bounded by the sum of seminorms (`iteratedFDerivWithin_sum_apply` + the
  triangle inequality, order by order).

* **Binary product-difference bound** — the order-`N` derivative of a difference of two
  binary products `f₁·f₂ − g₁·g₂`, with all four factors `ContDiffOn` and uniformly
  `Cᴺ`-bounded by `B` on a compact `K`, is controlled by the seminorms of the two factor
  differences:
  ```
  ‖iteratedFDerivWithin ℝ N (f₁·f₂ − g₁·g₂) s y‖ ≤
      2ᴺ·B·(iteratedFDerivSeminorm N (f₁−g₁) s y + iteratedFDerivSeminorm N (f₂−g₂) s y) .
  ```
  This is the algebraic telescoping `f₁f₂ − g₁g₂ = (f₁−g₁)f₂ + g₁(f₂−g₂)` followed by the
  single-difference Leibniz bound `norm_iteratedFDerivWithin_mul_le_uniformBound`.

These two facts, together with the partial-derivative order bridge, reduce every
chart-coordinate Ricci/Lie–DeTurck difference to the chart-Gram jet difference.

## Main results

* `norm_iteratedFDerivWithin_sum_le` — sub-additivity through a finite sum.
* `norm_iteratedFDerivWithin_two_prod_sub_le` — the binary product-difference bound.
-/

noncomputable section

open Set
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Sub-additivity of the order-`N` derivative through a finite sum.**  For a finite
family of `ContDiffOn ℝ ∞` fields on an open set `s`, the order-`N` iterated derivative
of the sum is bounded, pointwise, by the sum of the order-`N` iterated derivatives. -/
theorem norm_iteratedFDerivWithin_sum_le
    {ι : Type*} {F : ι → E → ℝ} {s : Set E} (hs : IsOpen s)
    (u : Finset ι) (hF : ∀ j ∈ u, ContDiffOn ℝ ∞ (F j) s)
    (N : ℕ) {y : E} (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ N (fun z => ∑ j ∈ u, F j z) s y‖ ≤
      ∑ j ∈ u, ‖iteratedFDerivWithin ℝ N (F j) s y‖ := by
  classical
  have hsum :
      iteratedFDerivWithin ℝ N (fun z => ∑ j ∈ u, F j z) s y =
        ∑ j ∈ u, iteratedFDerivWithin ℝ N (F j) s y := by
    have hpi : (fun z => ∑ j ∈ u, F j z) = (∑ j ∈ u, F j) := by
      funext z; simp
    rw [hpi]
    exact iteratedFDerivWithin_sum_apply (𝕜 := ℝ) (f := F) (u := u) (i := N)
      (s := s) (x := y) hs.uniqueDiffOn hy
      (fun j hj => ((hF j hj).contDiffWithinAt hy).of_le (by exact_mod_cast le_top))
  rw [hsum]
  exact norm_sum_le _ _

/-- **Binary product-difference bound.**  Let `s` be open and `f₁ f₂ g₁ g₂ : E → ℝ` all
`ContDiffOn ℝ ∞` on `s`.  Suppose the three plain factors `f₂`, `g₁` (and indeed any
factor needed) are uniformly `Cᴺ`-bounded by `B` on a compact `K ⊆ s`.  Then the
order-`N` derivative of the product difference `f₁·f₂ − g₁·g₂` is controlled by the
seminorms of the two factor differences `f₁ − g₁` and `f₂ − g₂`:
```
‖iteratedFDerivWithin ℝ N (fun y => f₁ y * f₂ y - g₁ y * g₂ y) s y‖ ≤
    2ᴺ·B·(iteratedFDerivSeminorm N (f₁ − g₁) s y + iteratedFDerivSeminorm N (f₂ − g₂) s y) .
```
The proof telescopes `f₁f₂ − g₁g₂ = (f₁−g₁)·f₂ + g₁·(f₂−g₂)` and applies the
single-difference Leibniz bound to each of the two single-difference products. -/
theorem norm_iteratedFDerivWithin_two_prod_sub_le
    {f₁ f₂ g₁ g₂ : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf₁ : ContDiffOn ℝ ∞ f₁ s) (hf₂ : ContDiffOn ℝ ∞ f₂ s)
    (hg₁ : ContDiffOn ℝ ∞ g₁ s) (hg₂ : ContDiffOn ℝ ∞ g₂ s)
    {K : Set E} (hKsub : K ⊆ s) {B : ℝ} (hB_nn : 0 ≤ B) (N : ℕ)
    (hf₂bound : ∀ y ∈ K, ∀ m : ℕ, m ≤ N → ‖iteratedFDerivWithin ℝ m f₂ s y‖ ≤ B)
    (hg₁bound : ∀ y ∈ K, ∀ m : ℕ, m ≤ N → ‖iteratedFDerivWithin ℝ m g₁ s y‖ ≤ B)
    {y : E} (hy : y ∈ K) :
    ‖iteratedFDerivWithin ℝ N (fun z => f₁ z * f₂ z - g₁ z * g₂ z) s y‖ ≤
      2 ^ N * B *
        (iteratedFDerivSeminorm N (fun z => f₁ z - g₁ z) s y +
          iteratedFDerivSeminorm N (fun z => f₂ z - g₂ z) s y) := by
  classical
  have hyS : y ∈ s := hKsub hy
  have htel : (fun z => f₁ z * f₂ z - g₁ z * g₂ z) =
      (fun z => (f₁ z - g₁ z) * f₂ z + g₁ z * (f₂ z - g₂ z)) := by
    funext z; ring
  rw [htel]
  have hcd1 : ContDiffOn ℝ ∞ (fun z => (f₁ z - g₁ z) * f₂ z) s :=
    ContDiffOn.mul (hf₁.sub hg₁) hf₂
  have hcd2 : ContDiffOn ℝ ∞ (fun z => g₁ z * (f₂ z - g₂ z)) s :=
    ContDiffOn.mul hg₁ (hf₂.sub hg₂)
  have hadd :
      iteratedFDerivWithin ℝ N
        (fun z => (f₁ z - g₁ z) * f₂ z + g₁ z * (f₂ z - g₂ z)) s y =
        iteratedFDerivWithin ℝ N (fun z => (f₁ z - g₁ z) * f₂ z) s y +
          iteratedFDerivWithin ℝ N (fun z => g₁ z * (f₂ z - g₂ z)) s y :=
    iteratedFDerivWithin_add_apply
      ((hcd1.contDiffWithinAt hyS).of_le (by exact_mod_cast le_top))
      ((hcd2.contDiffWithinAt hyS).of_le (by exact_mod_cast le_top))
      hs.uniqueDiffOn hyS
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have hbound1 :
      ‖iteratedFDerivWithin ℝ N (fun z => (f₁ z - g₁ z) * f₂ z) s y‖ ≤
        2 ^ N * B * iteratedFDerivSeminorm N (fun z => f₁ z - g₁ z) s y :=
    norm_iteratedFDerivWithin_mul_le_uniformBound hs (hf₁.sub hg₁) hf₂ hKsub hB_nn N
      hf₂bound hy
  have hbound2 :
      ‖iteratedFDerivWithin ℝ N (fun z => g₁ z * (f₂ z - g₂ z)) s y‖ ≤
        2 ^ N * B * iteratedFDerivSeminorm N (fun z => f₂ z - g₂ z) s y := by
    have hcomm : (fun z => g₁ z * (f₂ z - g₂ z)) =
        (fun z => (f₂ z - g₂ z) * g₁ z) := by funext z; ring
    rw [hcomm]
    exact norm_iteratedFDerivWithin_mul_le_uniformBound hs (hf₂.sub hg₂) hg₁ hKsub hB_nn N
      hg₁bound hy
  refine (add_le_add hbound1 hbound2).trans ?_
  rw [mul_add]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end

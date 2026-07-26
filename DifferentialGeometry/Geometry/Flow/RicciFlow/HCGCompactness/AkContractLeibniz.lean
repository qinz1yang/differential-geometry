import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.GammaAlgebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Single-step natural-contraction Leibniz (component algebra)

The `ric_bound` proof (MSM135 Lemma 3.11, `RicBoundProof.md` Claim 1) differentiates
the all-`(0,s)` relation `∇g_k = A_k ∗ g_k`, where `A_k = ∇ − ∇_k` is the `(1,2)`
connection-difference tensor and `∗` contracts `A_k`'s upper index against `g_k`.
This file proves the single-step Leibniz rule for that **natural** (upper–lower)
contraction, at the pure component-algebra level used by
`Evolution/Ricci/GammaAlgebra.lean` (`covD3`, `covDInv`, `covDChristoffelVariation`):

`covD3 Γ (A ∗ g) ∂(A ∗ g) = (covD12 Γ A ∂A) ∗ g + A ∗ (covD2 Γ g ∂g)`.

It is **metric-free**: the contracted-index Christoffel corrections — `+Γ` on `A`'s
upper slot, `−Γ` on `g`'s lower slot — cancel by an index relabel, so no `∇g⁻¹ = 0`
hypothesis is needed (unlike `raised_contract_covD_of_inv_zero`, which is for a
*raised* same-type contraction).

`covD2`/`covD12` here are the `(0,2)`/`(1,2)` fixed-direction covariant-derivative
steps, defined to match `covD3`'s `−Γ`-on-lower / `+Γ`-on-upper convention.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `(0,2)` fixed-direction covariant-derivative step (both indices lower). -/
def covD2 (Γ : ι → ι → Real) (g dg : ι → ι → Real) (i j : ι) : Real :=
  dg i j - (∑ p : ι, Γ p i * g p j) - (∑ p : ι, Γ p j * g i p)

/-- The `(1,2)` fixed-direction covariant-derivative step: upper index `k` gets the
`+Γ` correction (matching `covDInv`), the two lower indices `i, j` get `−Γ`. -/
def covD12 (Γ : ι → ι → Real) (A dA : ι → ι → ι → Real) (k i j : ι) : Real :=
  dA k i j + (∑ p : ι, Γ k p * A p i j) -
    (∑ p : ι, Γ p i * A k p j) - (∑ p : ι, Γ p j * A k i p)

/-- The natural contraction of a `(1,2)` tensor `A` with a `(0,2)` tensor `g`:
`(A ∗ g)_{ijd} = ∑_k A^k_{ij} g_{kd}` (contract `A`'s upper index against `g`). -/
def starAg (A : ι → ι → ι → Real) (g : ι → ι → Real) (i j d : ι) : Real :=
  ∑ k : ι, A k i j * g k d

/-- The directional derivative of `starAg` (ordinary product rule on the
direction-derivative arrays). -/
def dStarAg (A dA : ι → ι → ι → Real) (g dg : ι → ι → Real) (i j d : ι) : Real :=
  ∑ k : ι, (dA k i j * g k d + A k i j * dg k d)

/-- **Single-step natural-contraction Leibniz.**  The covariant derivative of the
natural contraction `A ∗ g` splits by the product rule, with the contracted-index
Christoffel corrections cancelling.  Pure component identity, no metric hypothesis. -/
theorem covD3_starAg_leibniz
    (Γ : ι → ι → Real) (A dA : ι → ι → ι → Real) (g dg : ι → ι → Real)
    (i j d : ι) :
    covD3 Γ (starAg A g) (dStarAg A dA g dg) i j d =
      starAg (covD12 Γ A dA) g i j d + starAg A (covD2 Γ g dg) i j d := by
  classical
  unfold covD3 starAg dStarAg covD12 covD2
  -- Distribute the two RHS product-sums into atomic sums.
  have hL :
      (∑ k : ι, (dA k i j + (∑ p : ι, Γ k p * A p i j) -
          (∑ p : ι, Γ p i * A k p j) - (∑ p : ι, Γ p j * A k i p)) * g k d) =
        (∑ k : ι, dA k i j * g k d) +
          (∑ k : ι, (∑ p : ι, Γ k p * A p i j) * g k d) -
          (∑ k : ι, (∑ p : ι, Γ p i * A k p j) * g k d) -
          (∑ k : ι, (∑ p : ι, Γ p j * A k i p) * g k d) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hR :
      (∑ k : ι, A k i j * (dg k d - (∑ p : ι, Γ p k * g p d) -
          (∑ p : ι, Γ p d * g k p))) =
        (∑ k : ι, A k i j * dg k d) -
          (∑ k : ι, A k i j * (∑ p : ι, Γ p k * g p d)) -
          (∑ k : ι, A k i j * (∑ p : ι, Γ p d * g k p)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- Split the leading directional-derivative sum too.
  have hD :
      (∑ k : ι, (dA k i j * g k d + A k i j * dg k d)) =
        (∑ k : ι, dA k i j * g k d) + (∑ k : ι, A k i j * dg k d) :=
    Finset.sum_add_distrib
  rw [hD, hL, hR]
  -- Reorder the free-index corrections to the LHS `∑_p Γ (∑_k …)` shape.
  have hC1 :
      (∑ k : ι, (∑ p : ι, Γ p i * A k p j) * g k d) =
        ∑ p : ι, Γ p i * ∑ k : ι, A k p j * g k d := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  have hC2 :
      (∑ k : ι, (∑ p : ι, Γ p j * A k i p) * g k d) =
        ∑ p : ι, Γ p j * ∑ k : ι, A k i p * g k d := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  have hC3 :
      (∑ k : ι, A k i j * (∑ p : ι, Γ p d * g k p)) =
        ∑ p : ι, Γ p d * ∑ k : ι, A k i j * g k p := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  -- The two contracted-index corrections cancel.
  have hcancel :
      (∑ k : ι, (∑ p : ι, Γ k p * A p i j) * g k d) =
        ∑ k : ι, A k i j * (∑ p : ι, Γ p k * g p d) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hC1, hC2, hC3, hcancel]
  ring

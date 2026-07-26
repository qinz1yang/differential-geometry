import DifferentialGeometry.Analysis.Calculus.RingInverseDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 C2 (`lbl430`(i)) — sub-brick (c4): the bilinear collection at `compL`

The all-order route differentiates the neighbourhood formula
`∇f =ᶠ −(inverse ∘ A).comp B` (`implicitFDeriv_eventuallyEq`,
`StepCDerivBounds.lean`).  Its `m`-th derivative splits by the Leibniz rule
for the composition bilinear map `compL`, whose operator norm is `≤ 1`:

`‖∇^m ((X ·).comp (Y ·))‖ ≤ ∑ᵢ C(m,i) ‖∇^i X‖ ‖∇^{m-i} Y‖`.

This file provides that collection lemma in `ContDiffAt` currency (the
Mathlib bilinear bound asks for global `ContDiff`; we localise to a common
open set exactly as `norm_iteratedFDeriv_graphComp_le` does).  Sub-brick (c5)
— the recursive majorant and the strong induction — consumes it together
with `norm_iteratedFDeriv_invComp_le` and `norm_iteratedFDeriv_graphComp_le`.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Topology
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The bilinear collection at `compL`** (`lbl430`(i) sub-brick (c4)).  For
CLM-valued families `X`, `Y` that are `C^m` at `x`, the `m`-th derivative of
the pointwise composition collects by the Leibniz rule with binomial
coefficients and no extra constant (`‖compL‖ ≤ 1`). -/
theorem norm_iteratedFDeriv_clmComp_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' F' G' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (X : P → (F' →L[ℝ] G')) (Y : P → (E' →L[ℝ] F')) (x : P) (m : ℕ)
    (hX : ContDiffAt ℝ (m : WithTop ℕ∞) X x)
    (hY : ContDiffAt ℝ (m : WithTop ℕ∞) Y x) :
    ‖iteratedFDeriv ℝ m (fun p : P => (X p).comp (Y p)) x‖ ≤
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i X x‖ *
          ‖iteratedFDeriv ℝ (m - i) Y x‖ := by
  obtain ⟨u, hu_mem, hXu⟩ := hX.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv_mem, hYv⟩ := hY.contDiffOn le_rfl (by simp)
  set s : Set P := interior u ∩ interior v with hs_def
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.2 hu_mem, mem_interior_iff_mem_nhds.2 hv_mem⟩
  have hXs : ContDiffOn ℝ (m : WithTop ℕ∞) X s :=
    hXu.mono (Set.inter_subset_left.trans interior_subset)
  have hYs : ContDiffOn ℝ (m : WithTop ℕ∞) Y s :=
    hYv.mono (Set.inter_subset_right.trans interior_subset)
  have h := (ContinuousLinearMap.compL ℝ E' F' G').norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hXs hYs hs_open.uniqueDiffOn hxs le_rfl
    (ContinuousLinearMap.norm_compL_le ℝ E' F' G')
  calc ‖iteratedFDeriv ℝ m (fun p : P => (X p).comp (Y p)) x‖
      = ‖iteratedFDerivWithin ℝ m (fun p : P => (X p).comp (Y p)) s x‖ := by
        rw [iteratedFDerivWithin_of_isOpen m hs_open hxs]
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i X s x‖ *
          ‖iteratedFDerivWithin ℝ (m - i) Y s x‖ := h
    _ = ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i X x‖ *
          ‖iteratedFDeriv ℝ (m - i) Y x‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iteratedFDerivWithin_of_isOpen i hs_open hxs,
          iteratedFDerivWithin_of_isOpen (m - i) hs_open hxs]

/-- **The one-step engine of the all-order implicit bound** (`lbl430`(i)
sub-brick (c5), induction step).  If the derivative of `f` agrees near `x`
with the implicit formula `−(inverse ∘ A).comp B`, the block families are
`C^m` at `x` with `‖∇^i A‖ ≤ DA^i` and `‖∇^i B‖ ≤ CB`, and the inverse at
the base point is bounded by `Λ`, then

`‖∇^{m+1} f x‖ ≤ 2^m · (m!·(m!·(max Λ 1)^{m+1})·(max DA 1)^m) · CB`.

Composition of the collection lemma (`norm_iteratedFDeriv_clmComp_le`), the
inverse Faà-di-Bruno bound (`norm_iteratedFDeriv_invComp_le`), and the
binomial identity `∑ᵢ C(m,i) = 2^m`.  The recursive majorant of the strong
induction feeds `DA`, `CB` from lower-order bounds. -/
theorem implicitDeriv_succ_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace E]
    (f : P → E) (A : P → (E →L[ℝ] E)) (B : P → (P →L[ℝ] E)) (x : P) (m : ℕ)
    (Lambda DA CB : ℝ)
    (hform : fderiv ℝ f =ᶠ[nhds x]
      fun p => -((Ring.inverse (A p)).comp (B p)))
    (hA : ContDiffAt ℝ (m : WithTop ℕ∞) A x)
    (hB : ContDiffAt ℝ (m : WithTop ℕ∞) B x)
    (hunit : ∀ᶠ p in nhds x, IsUnit (A p))
    (hLambda : ‖Ring.inverse (A x)‖ ≤ Lambda)
    (hDA0 : 0 ≤ DA)
    (hDA : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i A x‖ ≤ DA ^ i)
    (hCB : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i B x‖ ≤ CB) :
    ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤
      (2 : ℝ) ^ m * ((m.factorial : ℝ) *
        ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) * max DA 1 ^ m) * CB := by
  classical
  have hΛ0 : (0 : ℝ) ≤ max Lambda 1 := le_trans zero_le_one (le_max_right _ _)
  have hD0 : (0 : ℝ) ≤ max DA 1 := le_trans zero_le_one (le_max_right _ _)
  have hΛ1 : (1 : ℝ) ≤ max Lambda 1 := le_max_right _ _
  have hDA1 : (1 : ℝ) ≤ max DA 1 := le_max_right _ _
  -- the inverse family is `C^m` at `x`
  obtain ⟨w, hw⟩ := hunit.self_of_nhds
  have hXc : ContDiffAt ℝ (m : WithTop ℕ∞) (fun p => Ring.inverse (A p)) x := by
    have hinv : ContDiffAt ℝ (m : WithTop ℕ∞) Ring.inverse
        ((w : E →L[ℝ] E) : E →L[ℝ] E) := contDiffAt_ringInverse ℝ w
    rw [hw] at hinv
    exact hinv.comp x hA
  -- reduce `∇^{m+1} f` to `∇^m` of the formula
  have hfd : ‖iteratedFDeriv ℝ (m + 1) f x‖
      = ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ :=
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)).symm
  have hcongr : iteratedFDeriv ℝ m (fderiv ℝ f) x
      = iteratedFDeriv ℝ m
          (fun p => -((Ring.inverse (A p)).comp (B p))) x :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hform m).self_of_nhds
  have hneg : ‖iteratedFDeriv ℝ m
      (fun p => -((Ring.inverse (A p)).comp (B p))) x‖
      = ‖iteratedFDeriv ℝ m
          (fun p => (Ring.inverse (A p)).comp (B p)) x‖ := by
    rw [show (fun p => -((Ring.inverse (A p)).comp (B p)))
        = -(fun p => (Ring.inverse (A p)).comp (B p)) from rfl]
    rw [iteratedFDeriv_neg_apply, norm_neg]
  -- collect via `compL`
  have hcollect := norm_iteratedFDeriv_clmComp_le
    (fun p => Ring.inverse (A p)) B x m hXc hB
  set K : ℝ := (m.factorial : ℝ) *
    ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) * max DA 1 ^ m with hK_def
  have hK0 : 0 ≤ K := by rw [hK_def]; positivity
  -- per-term bound: each summand is at most `C(m,i) · K · CB`
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
        ‖iteratedFDeriv ℝ (m - i) B x‖ ≤ (m.choose i : ℝ) * (K * CB) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hinv_i := norm_iteratedFDeriv_invComp_le A x i Lambda DA
      (hA.of_le (by exact_mod_cast him)) hunit hLambda
      (fun j hj1 hjm => hDA j hj1 (hjm.trans him))
    have hfac : (i.factorial : ℝ) ≤ (m.factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le him)
    have hΛpow : max Lambda 1 ^ (i + 1) ≤ max Lambda 1 ^ (m + 1) :=
      pow_le_pow_right₀ hΛ1 (by omega)
    have hDApow : DA ^ i ≤ max DA 1 ^ m :=
      (pow_le_pow_left₀ hDA0 (le_max_left _ _) i).trans
        (pow_le_pow_right₀ hDA1 him)
    have hKi : (i.factorial : ℝ) *
        ((i.factorial : ℝ) * max Lambda 1 ^ (i + 1)) * DA ^ i ≤ K := by
      rw [hK_def]
      have h1 : (i.factorial : ℝ) * max Lambda 1 ^ (i + 1)
          ≤ (m.factorial : ℝ) * max Lambda 1 ^ (m + 1) :=
        mul_le_mul hfac hΛpow (by positivity) (by positivity)
      have h2 : (i.factorial : ℝ) *
          ((i.factorial : ℝ) * max Lambda 1 ^ (i + 1))
          ≤ (m.factorial : ℝ) * ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) :=
        mul_le_mul hfac h1 (by positivity) (by positivity)
      exact mul_le_mul h2 hDApow (by positivity) (by positivity)
    have hB_i : ‖iteratedFDeriv ℝ (m - i) B x‖ ≤ CB := hCB (m - i) (by omega)
    have hchoose0 : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
          ‖iteratedFDeriv ℝ (m - i) B x‖
        ≤ (m.choose i : ℝ) * K * CB := by
          refine mul_le_mul ?_ hB_i (norm_nonneg _) ?_
          · exact mul_le_mul_of_nonneg_left (hinv_i.trans hKi) hchoose0
          · positivity
      _ = (m.choose i : ℝ) * (K * CB) := by ring
  -- sum the per-term bounds and evaluate `∑ C(m,i) = 2^m`
  have hsum : ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
        ‖iteratedFDeriv ℝ (m - i) B x‖
      ≤ (2 : ℝ) ^ m * (K * CB) := by
    calc ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
            ‖iteratedFDeriv ℝ (m - i) B x‖
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (K * CB) :=
          Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * (K * CB) := by
          rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ m * (K * CB) := by
          have h := Nat.sum_range_choose m
          have : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ))
              = ((2 ^ m : ℕ) : ℝ) := by
            rw [← h]
            push_cast
            rfl
          rw [this]
          push_cast
          rfl
  calc ‖iteratedFDeriv ℝ (m + 1) f x‖
      = ‖iteratedFDeriv ℝ m
          (fun p => (Ring.inverse (A p)).comp (B p)) x‖ := by
        rw [hfd, hcongr, hneg]
    _ ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
            ‖iteratedFDeriv ℝ (m - i) B x‖ := hcollect
    _ ≤ (2 : ℝ) ^ m * (K * CB) := hsum
    _ = (2 : ℝ) ^ m * K * CB := by ring

end HCGCompactness
end DifferentialGeometry

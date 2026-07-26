# StepCDerivAll.lean

## 2026-07-19 created — `lbl430`(i) sub-bricks (c4) and (c5)-engine

Branch: `codex/short-time-existence-align`.  Both theorems focused-check
green AND `lake build`-verified (1988 jobs, clean), no `sorry`.

**Import decoupling + upstream observation:** the file initially imported
`C4/StepCDerivBounds.lean` but its two theorems only need
`Analysis/Calculus/RingInverseDeriv` + Mathlib `ContDiff.Bounds`, so the
import was narrowed (better layering).  This surfaced a tree-health fact:
**`StepCDerivBounds.lean` currently fails to REBUILD in this working tree**
— deterministic `isDefEq`/`whnf` heartbeat timeouts (200000) at lines
491/507/533/562/586/627 with cascading `Unknown identifier
CmHessianBoundInput` — even though its cached `.olean` exists and downstream
consumers work from the cache.  Likely cause: some module in its import cone
was refreshed (this session's Exponential/Comparison rebuilds and/or the
Volume lane's in-flight working-tree edits), changing unfolding costs past
the heartbeat budget.  NOT touched here — flagged for the owning lane; any
build that forces its rebuild will hit this.

Theorems:

- **(c4) `norm_iteratedFDeriv_clmComp_le`** — the bilinear collection at
  `compL` in `ContDiffAt` currency:
  `‖∇^m ((X ·).comp (Y ·))‖ ≤ ∑ᵢ C(m,i) ‖∇^i X‖ ‖∇^{m-i} Y‖`.
  Mathlib's `norm_iteratedFDerivWithin_le_of_bilinear_of_le_one` with
  `ContinuousLinearMap.compL` (`norm_compL_le`), localized to a common open
  set by the same interior-intersection dance as
  `norm_iteratedFDeriv_graphComp_le`.
- **(c5-engine) `implicitDeriv_succ_le`** — the induction step of the
  all-order implicit bound: from the neighbourhood formula
  `∇f =ᶠ −(inverse ∘ A).comp B` (`implicitFDeriv_eventuallyEq`), `C^m`
  block families with `‖∇^i A‖ ≤ DA^i` (`1 ≤ i ≤ m`) and `‖∇^i B‖ ≤ CB`
  (`i ≤ m`), and `‖(∂_zG)⁻¹‖ ≤ Λ` at the point:
  `‖∇^{m+1} f‖ ≤ 2^m · (m!·(m!·(max Λ 1)^{m+1})·(max DA 1)^m) · CB`.
  Chain: `norm_iteratedFDeriv_fderiv` (reduce to `∇^m` of `∇f`) →
  `Filter.EventuallyEq.iteratedFDeriv … |>.self_of_nhds` (swap in the
  formula) → `iteratedFDeriv_neg_apply` (drop the sign) → (c4) collection →
  `norm_iteratedFDeriv_invComp_le` per term (majorised into one constant
  `K`) → `Nat.sum_range_choose`.

Elaboration notes: the ring-inverse `ContDiffAt` is `contDiffAt_ringInverse`
(no underscore before `Inverse`); `hDA0 : 0 ≤ DA` is required (norm bounds
only force `DA^i ≥ 0` when some `i ∈ [1,m]` exists, so `m = 0` would leave
`DA` unconstrained); an initially-included `0 ≤ CB` was unused and dropped.

## What remains for the honest all-order `lbl430`(i) theorem (c5 proper)

1. The recursive majorant: define `Ctil : ℕ → ℝ` by strong recursion,
   `Ctil (m+1) := 2^m·(m!·(m!·(max Λ 1)^{m+1})·(max (DA m) 1)^m)·(CB m)`,
   where `DA m`, `CB m` are produced from lower-order `Ctil` values through
   `norm_iteratedFDeriv_graphComp_le` applied to the two blocks of
   `fderiv G_joint ∘ graph f` (post-composed with `inl`/`inr`; the fixed-CLM
   post-composition passes bounds with constant `1`).
2. The strong induction: `∀ j ≤ pOrd, ‖∇^j (chart ∘ cm)‖ ≤ Ctil j`, with
   order-`pOrd` regularity hypotheses (`centerOfMass_contDiffAt` for `f`,
   order-`pOrd` `CmGDerivBound` for the equation blocks) and the
   `CmHessianNbhdInput` neighbourhood facts feeding `hform`/`hunit`.
3. The cm-wiring (the concrete `G`, `A`, `B` of `cmChartDerivLe2`,
   generalized from `j ≤ 2` to `j ≤ pOrd`).

Step (1)–(2) are now assembly around `implicitDeriv_succ_le` — the analytic
content of the recursion is closed by this file.  Step (3) mirrors
`cmChartDerivLe2`'s wiring.  This discharges the "explicit recursive
numerical majorant" precondition that `StepCDerivBounds.md` set for stating
the arbitrary-order theorem.

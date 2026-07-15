# Tensor0SMetricContinuity.lean — spatial continuity of `normSq0S`

## What this file provides

`normSq0S_contAt` / `normSq0S_cont`: for a smooth metric `g` and a smooth
`(0,s)`-tensor field `T : Tensor0SField ∞ s`, the scalar map
`y ↦ normSq0S g y s (T y)` is continuous (at every point / globally).
Plus the reusable engine variant `tensor0SField_eval_cmdAt_slots`
(evaluation of a smooth `(0,s)`-field on `ContMDiffAt` moving slots is
`ContMDiffAt` — the local-slot version of
`tensor0SField_eval_smooth_slots_contMDiffAt`, whose slots must be global
sections).

This was the missing spatial-continuity API flagged in
`HCGCompactness/ConvFieldAssembly.md` (P4 Brick 4 `hbdd` head/mid wall) and
adjacent to the `LimitSolutionEquation.md` continuity needs.

## Route (what worked)

`normSq0S` is a pointwise recursive `MetricFiberData`; no direct continuity
handle.  Localize at `x₀` via the tangent trivialization
`e := trivializationAt E (TangentSpace I) x₀` with the Mathlib local frame
`e.localFrame b i` (`b := Module.finBasis ℝ E`):

1. Components `y ↦ T y (frame ∘ I₀)` are `ContMDiffAt` by
   `TensorMultilinear.contMDiffAt_section_apply_gen` + Mathlib
   `contMDiffAt_localFrame_of_mem` (named args `(e := e) (b := b) (i := …)`).
2. Gram entries: evaluate `metricTensorField g` (a `Tensor0SField ∞ 2`,
   `Tensor/RSTensor/MetricCompatibility.lean`) on `![i,j]`-frame slots;
   `metricTensorField_apply` rewrites to `g.inner`.
3. Gram invertibility on the baseSet: kernel vector `c` would give
   `g.inner y w w = 0` for `w := Σ cᵢ • frameᵢ ≠ 0` (CLM `map_sum`/`map_smul`
   expansion + `Matrix.exists_mulVec_eq_zero_iff` + basis
   `Fintype.linearIndependent_iff`) contradicting `g.pos`.
4. Inverse-Gram continuity by Cramer: `Matrix.inv_def` +
   `Ring.inverse_eq_inv` + `Continuous.matrix_det/adjugate` (on `continuous_id`)
   + `ContinuousAt.inv₀`; entries via `continuousAt_pi.1` (NOT
   `continuous_apply ∘ comp` — comp-form does not unify).
5. `MetricInverseInBasis` witness at each `y ∈ baseSet` for
   `e.basisAt b hy` with `gInv := (Gram y)⁻¹`: `Matrix.mul_apply` +
   `nonsing_inv_mul`/`mul_nonsing_inv` + `Matrix.one_apply`.
6. `normSq0S_eq_coord` (FiberMetric/Tensor0SMetric.lean:1306) rewrites the norm
   to `coordInner0S`; `unfold coordInner0S` + `tensor0SComponent_apply` +
   `congrArg (T y) (funext …)` swaps `basisAt` slots for `localFrame` slots
   (`localFrame_apply_of_mem_baseSet`).
7. Sum/product continuity via `tendsto_finset_sum` / `tendsto_finset_prod`
   (ContinuousAt is defeq a `Tendsto`); finish with `ContinuousAt.congr` on the
   baseSet-eventual equality.

## Gotchas (cost real iterations)

- **`set_option backward.isDefEq.respectTransparency false` is REQUIRED.**
  Without it, `α.contMDiff` on a `Tensor0SField` (an abbrev carrying a `letI`
  bundle topology) fails instance synthesis with
  `NormedSpace ℝ (Tensor0SModel s ℝ E)` — even though the instance exists
  (`Defs.lean:209`) and synthesizes fine at top level.  All the tensor-layer
  files that project `ContMDiffSection` fields set this option.
- `contMDiffAt_localFrame_of_mem` MUST get `(e := …) (b := …) (i := …)` named
  (positional puts the index into a `Trivialization` slot).
- Entry-of-matrix continuity: use `continuousAt_pi.1` twice; the
  `continuous_apply`-composition form leaves an un-unifiable `∘`.
- `Matrix.dotProduct` no longer exists; the root `dotProduct` (and
  `Matrix.mulVec` + `dotProduct` simp) unfolds `mulVec` pointwise.

## Verification

GREEN: focused check + targeted build (2929 jobs, module built, no warnings in
this file); `#print axioms` on all three public lemmas =
`[propext, Classical.choice, Quot.sound]` (audited via a temporary print at the
HCG consumer, then removed).

## Finding for a future shim (NOT built here)

There are TWO parallel (0,s)-fiber-inner APIs with NO identification lemma:
the intrinsic `inner0S`/`normSq0S` (`FiberMetric/Tensor0SMetric.lean`,
recursive `MetricFiberData`) and the chart-model
`tensorInnerPointwise_0s`/`innerBundleCLM`
(`Geometry/Metric/PointwiseInner/Defs.lean`,
`Geometry/Metric/TensorInner/Tensor0SInnerBundleCLM.lean`) with its own
continuity tower (`FiberMetric/Tensor0SInnerSectionContinuity.lean`,
`innerBundleCLM_continuous`).  A bridge
`tensorInnerPointwise_0s s g x (toModel A) (toModel B) = inner0S g x s A B`
would let the bundle route (`Continuous.inner_bundle`-style) replace this
file's frame/matrix proof and would dedup the two worlds.  Both sides have
coordinate formulas, so the bridge is an induction on `s` matching
`gramMatrixAt`-contraction against `normSq0S_eq_coord`.  Deferred: this file's
self-contained route was shorter and risk-free.

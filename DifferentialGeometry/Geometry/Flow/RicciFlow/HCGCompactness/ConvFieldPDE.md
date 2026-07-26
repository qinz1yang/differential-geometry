# ConvFieldPDE.lean — local PDE bridge for the P4 bump extension

## 2026-07-24 fixed-time Ricci norm producer

`gSeqExt_ricNorm` and `ConvOut.ricNorm_conv_at` are now proved without
`sorry`, `admit`, wrapper assumptions, or a new convergence predicate. Focused
verification and the exact module refresh both pass (`9563/9563`).

- `gSeqExt_ricNorm` identifies the intrinsic squared Ricci norm of
  `gSeqExt k t` on `bf.grow k` with the actual source `SolutionOn.ricciNorm`
  at `Φ.map k x`. Its proof stays on one open metric germ and composes
  restriction invariance with Ricci-norm pullback naturality.
- `ConvOut.ricNorm_conv_at` shifts past the grow-cover index and applies
  `ricNormConv_of_dn` to `co.convPt`, the existing uniform lower bound, and
  the existing covariant-derivative bounds. It therefore proves fixed-time
  convergence from the real source flow to the intrinsic squared Ricci norm of
  `co.gInf`, with constants independent of the shifted stage.

This closes the fixed-time Ricci-norm producer itself (100%) and leaves the
local Ricci/scalar/PDE producer chain at 100%. It does not prove the Hamilton
`ham3_cgh_limit` endpoint: that theorem remains unstated/unproved (0%), and its
next genuine seam is the trace-free curvature combination and endpoint data
plumbing. The unconditional Theorem 3.10 endpoint remains 0%; the conservative
whole-HCG machinery estimate remains about 60%.

## 2026-07-17 result

The new module is focused-green and contains no `sorry`/`admit`.  Its exact
target refresh passed after the canonical metric-extensionality dependency was
refreshed, and `ConvFieldEndgame.lean` now imports its PDE and scalar locality
producers directly.

- `gSeqExt_ricci` proves that, at `x ∈ bf.grow k`, the Ricci tensor of the
  total bump extension `gSeqExt k t` equals the Ricci tensor of the genuine
  pulled-back source-flow metric `srcMetric k t`.
- `gSeqExt_pde` takes a closed window `Icc β ψ ⊆ X.D.regular` and proves on
  that window
  `HasDerivWithinAt (fun s => (gSeqExt k s).inner x v w)
    (-2 * ricciTensor (gSeqExt k t) x v w) (Icc β ψ) t`
  whenever `x ∈ bf.grow k`.

The proof uses no new assumptions.  It extracts the source-flow equation from
`isSolutionOn_sourceFlow`, uses `BumpFamily.chi_one` for coefficient equality,
and proves the Ricci value equality by restricting both metrics to the same
open source-domain neighborhood and applying `ricciTensor_restrictOpen`.

## Earlier A.1-only boundary (superseded)

The initial pass stopped after the local `gSeqExt_pde` producer.  Its recorded
eventual/shift frontier has since been discharged by the limit-PDE result below.

## 2026-07-17 limit-PDE endpoint

`ConvOut.gInf_pde` is now proved and focused-green, with no `sorry` or new
assumption.  Its honest inputs are the regular closed window, the exact source
lower bound `hbound`, the source-tail covariant bound `hcovTail`, and
`co : ConvOut`; it does not repeat the raw endgame equivalence/Shi inputs.

For fixed `x`, the proof shifts the convergent sequence by the index supplied
by `bf.grow_cover {x}`.  Thus every shifted stage contains `x` in its agreement
region and source.  The resulting inputs to `metricLimit_pde'` are produced as
follows:

- eventual metric equations come from `gSeqExt_pde` at every shifted stage;
- coefficient convergence and order-`2` seminorm convergence come from
  `co.convPt` along the same subsequence;
- the uniform lower constant is `min cLow 1`, using the exact producer
  `gSeqExt_lower`; the limit retains it by coefficient convergence;
- the three constants supplied by `hcovTail` at orders `0`, `1`, and `2` are
  combined into one bound for the sequence and limit, with the limit estimate
  obtained from `covNorm_le_add` and one uniform order-`2`, epsilon-`1`
  convergence instance;
- `ricciConv_of_dnConv` then produces the uniform Ricci convergence consumed by
  `metricLimit_pde'`.

Accounting: `ConvOut.gInf_pde` and the A.1+A.2 limit-equation chain are 100%.
The theorem constructing the full `IsSolutionOn` package remains unstated and
therefore 0%; its dedicated P4 machinery is conservatively about 88%.  The
unconditional Theorem 3.10 endpoint remains 0%, and the whole-HCG machinery
estimate remains about 60%.

## 2026-07-17 scalar locality

`gSeqExt_scalar` is focused-green with no `sorry` or new assumption.  At a
point in `bf.grow k`, it identifies the scalar curvature of the total bump
extension with the scalar curvature of the original sequence flow at
`Φ.map k x`.

The proof reuses the same open-neighborhood germ equality as
`gSeqExt_ricci`, then composes the existing scalar-curvature naturality
theorems `metricScalarAt_restrictOpen`, `scalar_pullback`, and
`scalar_restrictOpen`.  This settles the reusable locality bridge needed by
the scalar-convergence lane; it is not itself the `ScalarPullbackTendsto`
endpoint.  The conservative P4-machinery and whole-HCG estimates therefore
remain about 88% and 60%, while unconditional Theorem 3.10 remains 0%.

The pointwise analytic passage now also lives at this layer as the checked
`ConvOut.scalar_conv_at`.  It combines `gSeqExt_scalar`, spatial exhaustion,
`co.convPt`, and `scalarConv_of_dnConv` for one time in the chosen closed
window.  The old carrier-wide `ConvOut.scalar_conv` remains in
`ConvFieldEndgame.lean` as a compatibility corollary; its whole-carrier
containment premise is no longer part of the analytic producer.

This extraction is what permits the open-interval route to choose a different
canonical compact window for each time.  It adds no assumption and leaves all
existing consumers source-compatible.  The local scalar and PDE producer
chain is 100%; the unconditional Theorem 3.10 endpoint remains 0%.

The module's focused verification and exact import refresh both pass.  The
refresh required only an unrelated canonical-name disambiguation in
`PolarisedLpFull.lean`; no P4 statement or proof changed as a result.

## 2026-07-18 grow-local covariant consumer

Both PDE-side consumers now request and apply `hcovTail` directly on
`bf.grow k`; the redundant intermediate whole-source membership proof was
removed. Focused verification and the exact module refresh pass.

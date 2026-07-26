# CurvatureCoefficientDifferenceJetTower

## 2026-07-12: fixed-frame independence elaboration

### Status

- `riemannMixedBiContrFib_eq_fixedFrame_on_nbhd`: proved and source-verified (100%).
- Its dedicated frame-independence machinery, including
  `double_frame_bilin_trace_indep`: available and reused (100%).
- This module's focused source verification and targeted build: passed (100%).
- Short-time-existence branch-alignment merge preparation: approximately 85%; the headline
  theorem is already proved, but downstream consumer and final merge-gate verification remain
  separate work.

### Simplification

The theorem differs from the nearby successful fixed-frame proofs only by an outer scalar factor
`2`. The old generic `congr 1` attempted to discover that congruence through a very large tensor
expression. It was replaced by the typed congruence
`congrArg (fun z : Real => 2 * z)`, after which the existing
`double_frame_bilin_trace_indep` theorem closes the actual geometric equality.

### Failed route and verification

The generic-congruence version hit a deterministic `whnf` heartbeat timeout and a retry with a
larger heartbeat budget consumed roughly 6 GB of memory. Increasing the budget is not a viable
route. The simplified proof passed focused verification and a targeted module build at the normal
heartbeat limit with two Lean threads. No new mathematical frontier remains in this theorem.

## 2026-07-15: antidiagonal product integral API

`grid_prod_int_le` exposes the existing antidiagonal product integration
engine.  Given a pointwise zeroth-jet bound, the top `L2` jet, and the
Gagliardo--Nirenberg intermediate estimates, it controls each product term by
the square of the top jet.  This is the reusable input needed for the
three-dimensional order-two inverse-metric estimate.

The mathematical proof was already present as the private product-term engine;
this change only gives it a public canonical name.  Verification is still
running because this module is unusually large.

## 2026-07-19: public moving-trace split

`pureTrace` gives a small public name to the canonical cometric double-trace
coefficient, and `pureTrace_split` exposes its exact decomposition into the
fixed parallel trace plus the inverse-metric-difference correction.  This is
the algebraic input for the low-regularity fixed-curvature `lieCorr0` arm; it
avoids estimating that arm as an undifferentiated whole.

These aliases are source-complete but await a focused recheck after the
exclusive shared artifact refresh.  No endpoint theorem is credited by this
source-only addition.

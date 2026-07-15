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

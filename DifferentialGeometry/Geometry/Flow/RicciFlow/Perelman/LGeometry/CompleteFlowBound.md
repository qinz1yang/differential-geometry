# CompleteFlowBound

## Purpose

This module discharges the two geometric hypotheses of `lRegRange_compact`
from one honest global bound on the squared Riemann-tensor norm over the
regular backward spacetime slab.

## Route

- `lRegPot_lower_rm` applies the native Riemann-to-scalar norm estimate and
  controls the square-root-time weight on `[0,b]`.
- `lRegPot_upper_rm` gives the matching upper scalar-potential estimate from
  the same squared-Riemann bound. Together the two bounds control the signed
  potential contribution when comparing minimizing-ray heads.
- `lRegMetric_le_rm` applies the native Riemann-to-Ricci quadratic estimate and
  the checked Ricci-flow logarithmic metric-distortion theorem, giving the
  explicit comparison factor `exp(2 * n^2 * sqrt K * b^2)`.
- `lRegRange_of_rm` feeds both producers into `lRegRange_compact`, so the whole
  image of an action-bounded curve lies in a compact intrinsic ball whenever
  the terminal metric is complete.
- `lRegRanges_of_rm` applies the same bounds uniformly to a sequence with one
  initial point and action budget, producing one compact terminal-metric target
  for every curve in the sequence.

No compactness assumption on the manifold and no new curvature-bound package
or class is introduced.

## Downstream reuse

For a family of minimizing rays, `lRegRanges_of_rm` supplies one compact target
`Cpt`. The native `gradSq_joint` continuity result can then bound the scalar
gradient on the compact product of the regular time interval with `Cpt`; no
ambient compactness is needed. The slab Riemann bound already gives the Ricci
quadratic estimate globally, while `lRegPot_lower_rm` and `lRegKinetic_le` give
the uniform kinetic budget. These three bounds feed `lRegInit_bdd` curve by
curve and then `initNorm_bdd`, producing the compact-target replacement for
the old ambient-compact initial-vector bound.

There is no existing exact compact-target scalar-gradient endpoint elsewhere in
the native tree. Its canonical home is `MinMaxCompact`, which is currently
owned by another active claim; this module does not duplicate it.

## Verification and progress

Focused verification passes without `sorry` or linter warnings, and the
targeted module artifact has been refreshed successfully for all five results,
including the family specialization and the new upper potential bound.

The complete noncompact minimizer and the later minimum-time/fencing consumers
are now proved downstream. This bounded-curvature adapter stage is 100%; it is
infrastructure for the larger complete-flow L8--L9 chain rather than the final
smooth-noncollapsing theorem.

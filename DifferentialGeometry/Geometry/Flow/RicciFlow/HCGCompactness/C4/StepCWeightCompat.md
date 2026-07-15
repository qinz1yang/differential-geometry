# StepCWeightCompat.lean

## 2026-07-09 Representation bridge

This compatibility layer connects the new arbitrary-base pointwise producer to
the existing Step-B chart-convergence formulas:

- `raw_eq_normWeights` identifies `rawWeights` with the older model-space
  `normWeights` definition;
- `cutRaw_eq_bumpNum` identifies the base-kill formula with `bumpNum` after
  writing the book multiplier as `1 - cut`;
- `rawBump_eq_weight` lifts that equality through normalization;
- `normalRaw_eq_bump` reads the global normal-coordinate raw numerator in a
  beta normal chart and recovers the existing transition formula exactly.
- `normalWeight_eq` performs the same readout after finite normalization, so
  the pulled-back global family is pointwise the existing
  `normWeights (bumpNum ...)` expression.

Focused verification and the targeted module build passed.  These are
representation adapters only: they do not by themselves prove atom coverage,
denominator positivity, or convergence of the metric-dependent quadratic
atoms.

Honest progress remains: the `StepB1RawInput` producer theorem 0%; its dedicated
machinery about 52%.  The compatibility gap is closed, while the intrinsic atom
family and its sequence-level convergence remain the live producer work.

# CostJointParam

## Role

This module supplies the missing joint terminal-time/initial-point compact
L-cost upper-semicontinuity producer needed by the reduced-volume lower
semicontinuity route.

## Implemented route

- `chartKin_param` (private) proves convergence of fixed-chart kinetic action
  when both the chart `timeH1` representative and terminal-time function vary
  uniformly inside one compact regular time-coordinate slab.
- `lScalar_param` (private) proves the matching scalar-action convergence by
  dominated convergence on the compact slab.
- `lAction_head_param` (private) assembles those two producers into a genuine
  varying-terminal-time one-chart action limit.
- `chart_head_T_lim` is the public short chart-head producer.  It perturbs the
  initial endpoint with `timeH1.rampDown` while the terminal forward time also
  converges.
- `lCost_lt_param` combines the perturbed head with the unchanged tail, smooths
  the joined competitor, and applies the native regularized cost bound at each
  perturbed terminal time.  Its hypotheses are geometric regularity and an
  explicit fixed competitor, not an assumed continuity property.

## Verification

Warning-free focused verification passed.  The module contains no `sorry` or
`admit`; its public producers are now checked source.  A named module refresh is
still needed before a downstream file can import these new declarations.

## Progress accounting

- `lCost_lt_param`: theorem source and verified theorem 100%; dedicated
  joint-parameter machinery source and verified machinery 100%.
- Joint `(T,x)` compact L-cost strict-upper-bound production: verified 100%.
- `redVolume_lsc`, `redVolume_unif_low`, and `smooth_nlc`: endpoint theorems 0%;
  this module is upstream infrastructure only.
- Whole Perelman L-geometry program: approximately 45%; the eventual Poincare
  project remains below 1%.

## Remaining frontier

The next mathematical step is `redVolume_lsc`: combine `lCost_lt_param` with
Fatou's lemma in the finite chart partition-of-unity decomposition of the
moving Riemannian volume measure.  After that, compactness and the already
checked zero-time limit and antitonicity yield `redVolume_unif_low`.  No further
source/basepoint parameter bridge remains.

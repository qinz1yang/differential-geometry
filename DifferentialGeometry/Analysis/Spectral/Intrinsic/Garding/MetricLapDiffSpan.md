# MetricLapDiffSpan

## Goal

Produce the moving scalar `H² → H⁰` operator data on every requested
backward interval below one radius chosen uniformly over a compact regular-time
slab.

## 2026-07-19 source assembly

`lapA20_span` uses `metric_c1_span` with the dimension-adjusted smallness
threshold required by `lapDiffOp_core`.  After the terminal time and requested
length are supplied, it proves reflected regularity, operator-norm continuity,
a finite uniform norm bound on the exact compact interval, and the genuine
finite-core evaluation identity throughout that interval.

This removes the eventual-neighborhood dependency of `lapDiffA20_core` for the
target-length Galerkin route.  No spectral spaces at different terminal metrics
are compared, and no consumer assumption or local-chart constancy hypothesis
is introduced.

Verification is pending the in-progress exported-object refresh of the earlier
compact-span Garding producers.  Until focused verification passes,
`lapA20_span` is theorem-level 0% with approximately 98% dedicated source and
machinery.  It is the operator-continuity/core input for `gal_span`; the
noncollapsing and Hamilton endpoints remain theorem-level 0%.

The active refresh first exposed a missing `CovDerivPointwise.olean`; its
narrow module rebuild passed.  The subsequent `ScalarFluxJetBound` source
check passed, while its exported-object refresh remains active.  No diagnostic
has yet reached the `lapA20_span` proof body.

# ConjPotentialSpan

## Goal

Package the existing conjugate-potential continuity theorem on an exact compact
interval chosen by the caller, without selecting another lifespan.

## 2026-07-19 source assembly

`conjA1_on` applies `conjA1_cont` under the supplied reflected-regularity proof
and bounds the operator norm by compactness of `Icc 0 h`.  The result supplies
exactly the lower-order continuity and finite bound required by a
prescribed-length Galerkin ODE.

The theorem adds no assumptions and contains no local `sorry`.  Focused
verification is pending completion of the active upstream export refresh.
Until then it is theorem-level 0% with approximately 99% dedicated source and
machinery.  `gal_span` and all downstream noncollapsing endpoints remain
theorem-level 0%.

The first focused check stopped before elaborating this file because the
imported object `ComponentSobolevBoundDerivBridge.olean` is missing.  This is a
stale-artifact/tooling blocker, not a theorem error.  A broader upstream export
refresh is already active, so no overlapping build was started.

`conjCoeff_span` has also been assembled.  It bounds the scalar conjugate-heat
coefficient uniformly on a compact regular-time slab by applying compactness to
the already proved joint scalar continuity.  This is the coefficient bound
needed by exact-interval positivity; it adds no PDE or convergence assumption.
It remains theorem-level **0%** pending the same focused verification.

## 2026-07-23 post-merge check

The span file now uses the fully qualified `RealTimeInterval` namespace where
needed and omits unused inherited section variables around `conjCoeff_span`.
Focused verification and the module artifact refresh both passed.

# MinimizingNoConj

## Purpose

This module transports the checked interior no-conjugate theorem from a
unit-speed minimizing geodesic to the shifted tail based at an arbitrary
interior point.  It owns the canonical finite-distance segment identity
`minSeg_edist`, endpoint reversal `tail_not_conj_of_min`, and the whole closed
tail statement `tail_no_conj`.

## Current state

The source implementations follow the fixed-first Route B′ ruling:

- exact distance splitting on minimizing intrinsic radial segments;
- reverse unit launch at the terminal point;
- arbitrary-length minimizing no-conjugacy on the reverse segment;
- conjugacy reversal at the tail endpoint;
- ordinary interior no-conjugacy on the normalized forward tail.

Focused verification is GREEN with zero diagnostics.  The public
`tail_not_conj_of_min` and `tail_no_conj` proofs are sorry-free, as are the
supporting `minSeg_edist`, shifted-curve, shifted-velocity, and tail-distance
lemmas.  The endpoint proof uses the exact-current `conjVec_reverse` and
`not_conj_of_min_len` producers; the interior proof uses the same
arbitrary-length minimizing theorem on the normalized tail.  No new
minimizing predicate, endpoint nonconjugacy assumption, raw exponential
radius, or connectedness hypothesis was introduced.

The source theorem implementations and their dedicated machinery are 100%.
The targeted artifact refresh is GREEN, so all three public results are
exact-current.

The final `calabiDist_support` theorem remains a separate 0% theorem until it
consumes these checked tail outputs together with the fixed-first branch and
intrinsic Bishop comparison.

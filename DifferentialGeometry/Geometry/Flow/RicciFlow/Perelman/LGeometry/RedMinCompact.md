# RedMinCompact

## Role

This module is the complete bounded-curvature producer for spatial reduced-
length minimum attainment.  It keeps the terminal point free in the compact
direct method instead of assuming that a desired spatial minimum already
exists.

## Source state

- `lRmFree_subseq` is the fixed-start, varying-endpoint Arzela--Ascoli
  generalization of the existing fixed-endpoint compact subsequence theorem.
- `lRmFree_lsc` threads that subsequence through the existing finite-chart weak
  lower-semicontinuity machinery.
- `exists_redMin_rm` minimizes regularized action over all global `C1` curves
  with the prescribed start.  Connectedness supplies nonempty competitor
  classes for arbitrary endpoints, and the positive reduced-length
  normalization transfers the resulting cost comparison.

Focused verification passes without warnings or placeholders, and the explicit
named module artifact is refreshed.  No minimum-existence assumption or
compact-manifold assumption is used.

## Remaining frontier

Compactness of the full set of minimizing `(tau, y)` pairs on a compact
positive `tau` interval is not claimed.  The current endpoint and parameter
continuity APIs provide strict-upper-bound stability, which is upper
semicontinuity of cost.  The missing producer is joint lower semicontinuity of
`(tau, y) |-> lCost S T x y tau` for varying positive `tau` together with the
uniform compact localization needed to keep all minimizing curves in one
target.  Fixed-`tau` free-endpoint attainment does not imply that joint result.

## Progress

`exists_redMin_rm` and its dedicated fixed-positive-time spatial-attainment
machinery are **100%**.  This is one Claim 8.1 producer, not the separate
all-point spacetime Calabi barrier or `exists_redLen_le`; those theorem
endpoints remain **0%**.  Dedicated complete-flow L8 machinery is roughly
**40--45%**, dedicated L-geometry across the still-open L8--L9 endpoints is
about **49--51%**, and
the whole P0--P9 program infrastructure remains about 15--25%.

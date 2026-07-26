# MinimizingGeodesic

## 2026-07-24 — canonical finite-pair minimizing exponential

- `minExp_of_ne_top` is now the proof-owning finite-pair Hopf–Rinow theorem.
  It assumes only the explicit component condition
  `riemannianEDist I p q ≠ ⊤`, together with completeness and the existing
  metric/norm identity; it does not require `ConnectedSpace M`.
- The theorem reuses the established ray/sphere minimizing-vector proof.
  Every internal finiteness step is derived from the supplied pairwise
  hypothesis or from the checked radial/path-length estimates.
- The former long name
  `hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top` remains a
  compatibility theorem, while the connected headline is now a corollary of
  `minExp_of_ne_top`.
- Focused verification passed without diagnostics.  No targeted refresh was
  run in this lane.

Accounting: `minExp_of_ne_top` is proved (100%), and its dedicated Hopf–Rinow
machinery is 100%.  This is a canonical producer/API cleanup; the downstream
nonzero inverse-branch theorem remains separate, and `calabiDist_support`
remains unstated (0%).  Route B-prime producer machinery remains about 45%,
while whole HCG support remains about 60%.

## 2026-07-23 — point-pair Hopf–Rinow refactor

- Added the finite-pair endpoint
  `hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top` and retained the
  connected headline as a compatibility corollary.
- The ray/sphere proof no longer obtains finiteness of intermediate path
  points, moving feet, or the final radial point from global connectedness.
  Radial points are finite by the intrinsic-geodesic length bound, while points
  on the comparison path are finite by its already available strict finite
  length estimate.
- The complete intrinsic-geodesic producer spine through
  `expMapIntrinsic_continuous` is now exact-current without ambient
  `ConnectedSpace`; the refactored file is focused- and exact-current with a
  genuinely componentwise exported signature.
- The finite-pair theorem body and its lower producer migration are complete.
  The remaining downstream task is the disconnected closed-eball compactness
  consumer in `Comparison/HopfRinowProper.lean`.

## 2026-07-10 — named intrinsic/realized exponential agreement radius

- Added `expDiffeoRadius`, a named positive pointwise radius obtained by
  intersecting the intrinsic/realized agreement radius with `expRadiusGp`.
- Added `expDiffeo_mem_of_lt` and `expDiffeo_eq_intr`.  Below the named radius,
  a tangent vector lies in the source of `NormalCoordinates.expMapDiffeo`, and
  the realized exponential equals `expMapIntrinsic`.
- Focused verification and the targeted module build passed.
- Scope limitation: this is a fixed-base, pointwise producer.  It gives no
  continuity or uniform positive lower bound for `p ↦ expDiffeoRadius g hEnorm p`.
  Consequently the common moving-base `C^infty` domain and finite-hat
  containment remain separate Step-C frontiers.


# `ActionPieceAccel.lean`

## Result

`lStrict_piece_accel` proves that a strict finite chart-`H¹` realization of
a genuine global fixed-endpoint regularized L-action minimizer satisfies the
intrinsic regularized L-geodesic acceleration equation at every global time
strictly inside each realized piece.

The conclusion is stated for the original curve `gamma`, not only for its
shifted inverse-chart reconstruction.

## Proof route

For a selected piece, strictness gives positive length.  The global competitor
inequality is converted by `lChartAct_local` into the genuine fixed-chart local
minimum required by `lChart_min_accel`.  The latter supplies the intrinsic
equation for the shifted inverse-chart curve.

At an interior global time, `hrep` and the chart inverse identify that shifted
curve with `gamma` on an open neighborhood.  Germ congruence for `mfderiv`
identifies their velocities, and `covDerivAlong_congr_curve` transports the
covariant derivative.  The proof compares only the fully applied tangent
vectors through their model-space coercions; it does not unfold tangent bundles,
tensor fibers, or continuous-linear-map representations.

No Euler equation, acceleration equation, extra regularity conclusion,
reference-tree import, new class, or frontier wrapper is assumed.

## Verification and progress

Focused verification passed without warnings or placeholders.  The theorem is
100% complete and closes the strict finite-piece intrinsic-equation consumer.

The focused noncompact recheck also passed without warnings.
`lStrict_piece_accel` now exports without an ambient `CompactSpace M` instance;
its downstream refresh passed.
The terminal `exists_lMinimizer` and `redVolume_anti` remain 0%; dedicated
L-geometry machinery is approximately 97--98%, reused generic infrastructure
is 100%, P2 remains below 1%, and the whole Poincare program remains
approximately 3--5%.

# Interior regularity of strict finite L-action minimizers

## Result

`lStrict_curve_reg` assembles the full intrinsic regularized L-geodesic triple
at every point of the open global interval of a strict finite minimizing
realization.  An interior time is placed in a closed subdivision piece using
the native finite-segment `Nat.find` pattern already used by
`ActionDensityGeom`; strict interior points use `lStrict_piece_c2_at`,
`MFDerivAlongCurve.velocity_coord_diff`, and `lStrict_piece_accel`, while an
endpoint equality is necessarily an internal node and uses `lFinNode_reg`.

No node equation, regularity conclusion, or new foundational subdivision API
is assumed.

## Verification

Focused verification passed without warnings or placeholders.  The shared
open-piece `C²` producer was extracted into `ActionStrictC2`, both downstream
consumers were rechecked, and the targeted export refresh passed.

The focused noncompact recheck also passed without warnings.
`lStrict_curve_reg` now exports without an ambient `CompactSpace M` instance;
its downstream refresh completed successfully, replaying only the unrelated
pre-existing `ActionNodeLocal` linter warning.

## Project position

This theorem is the strict-finite interior assembly immediately before
compressing arbitrary monotone realizations.  The terminal
`exists_lMinimizer` and `redVolume_anti` remain unproved at 0%; their dedicated
L-geometry machinery is about 98%, while the generic infrastructure used here
is complete.

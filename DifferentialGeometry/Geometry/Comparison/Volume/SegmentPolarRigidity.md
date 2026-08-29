# SegmentPolarRigidity

## Role

This module contains the strict pointwise and integrated consequences of the
segment-polar equality-rigidity theorem. It introduces no almost-everywhere or
consumer-side strictness assumption.  Euclidean normalization and the final
sectional-curvature consumer live in `SegmentBallEuclideanStrict`.

## Route and reuse

`expJac_lt_of_ricci` starts from the existing `expJacDensity_le`. If equality
held, a perpendicular orthonormal frame supplied by `exists_perp_pos` and
`expJacDensity_eq_ncd0_mul_transverse` would identify the endpoint transverse
density with its model value after cancelling the positive pole factor. The
positivity is the native `paramDensity_pos` theorem at the zero vector.
`transDens_eq_rigid` would then force radial Ricci saturation at every interior
time, contradicting the supplied non-saturation witness.

`segBall_vol_lt` applies the pointwise theorem at `t = 1 / 2`.  The native
`intrGeo_vel_ne` turns global strict Ricci positivity into the required
non-saturation witness.  A smaller metric tangent ball lies in `SegDom` by
`radial_riemannianEDist_eq_of_small'`; its openness and nonemptiness give the
segment domain positive `modelHaar` measure.  Mathlib's
`setLIntegral_strict_mono` then upgrades the pointwise inequality to a strict
integral inequality.  The volume-to-integral bridge is `segBall_vol_le_int`,
and the final model normalization is the existing proof now exported as
`gBall_model_int`.  No geometric or polar-integration producer is duplicated.
The public statement does not separately assume nonnegative Ricci: global
strict Ricci positivity already supplies `RicciBoundedBelow g 0`, which is
constructed locally for the non-strict comparison input.

The equality-rigidity dependency comes from the dedicated
`SegmentPolarEquality` module rather than living in `SegmentPolar`.  The
Euclidean wrappers were moved, not duplicated, into
`SegmentBallEuclideanStrict`, whose global inner-product context gives the
canonical volume measure a single measurable-space instance path.

## Verification

After three local repair passes, the fourth focused check completed warning-free
and green for both `expJac_lt_of_ricci` and `segBall_vol_lt`.  The final measure
repair bypasses typeclass synthesis by calling the existing additive-Haar
instance's `toIsOpenPosMeasure.open_pos` field directly.  The refreshed
`SectionalRicci` dependency is focused-green.  The latest Rigidity check reached
only the now-moved Euclidean conclusions; both general producers elaborated
without an error.  Two attempts to keep the Euclidean declarations in this file
left a `MeasureSpace.toMeasurableSpace`/private-`borel` diamond.  The declarations
now live in a dedicated module patterned exactly on the checked
`SegmentBallEuclideanUpper` instance order.  After the unused lambda binder was
repaired, that downstream module passed a warning-free focused check and its
named refresh completed 4045/4045.  The public axiom audit remains pending.

## Project status

The two local rigidity producers are focused-green, but they are machinery and
do not increase the endpoint count.  Across P1a, checked endpoints remain 6/8
(75%); dedicated machinery is about 96% complete pending the public axiom
audit.  The final strict Euclidean endpoint is
now source-written in the exact Morgan--Tian 9.56 sectional-curvature form, but
remains 0% until that final gate is green.  At the authoritative whole-program
denominator, P0--P9 infrastructure remains 15--25% complete, while the final
`poincare_of_inputs` theorem remains 0%.

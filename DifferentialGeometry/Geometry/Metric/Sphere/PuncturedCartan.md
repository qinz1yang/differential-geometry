# PuncturedCartan

## Role

This module builds the one-pole Cartan map from the round sphere to a complete
curvature-one target.  It is the local-to-global geometry layer between the
verified round logarithm and the later two-chart Killing--Hopf gluing.

## Route

- Compose `roundLog` with the supplied tangent metric isometry and the target
  intrinsic exponential.
- Prove smoothness on the open complement of the antipode.
- Differentiate `round_exp_log_ne` to cancel the source exponential
  differential.
- Apply `expDiff_sq_xfer` and polarization for metric preservation.
- Derive local-diffeomorphism status from the resulting invertible
  differential; do not add it as a consumer assumption.
- Record the center value and center differential explicitly.  These two jet
  readouts let the second Cartan map be aligned with the first one before
  applying overlap rigidity.
- Thread the source sphere pseudo-metric and the `CompleteSpace` instance for
  its induced uniformity through the Cartan API.  This prevents the local map
  from reverting to the unrelated canonical chordal metric.

## Verification and progress

Focused verification and exact module verification passed after the
metric-world parameterization.  The module contains no `sorry` or `admit`.

`ham3_space_box` remains unproved and therefore 0%.  Its dedicated positive
Killing--Hopf machinery is approximately 74% complete after this module:

- the one-pole Cartan map is genuinely smooth on the punctured sphere;
- its differential preserves the full Riemannian inner product;
- it is a genuine smooth local diffeomorphism there.
- its value and differential at the chosen center are available in the exact
  normal form needed to align two local Cartan constructions.

The next frontier is the global two-chart assembly.  Build Cartan maps based at
two distinct sphere points, prove agreement on their connected overlap using
`localIso_rigid`, glue the total map, and upgrade the resulting compact-source
local diffeomorphism to a global diffeomorphism by the existing covering-space
API.  This is not yet implemented, so that global assembly remains 0%.

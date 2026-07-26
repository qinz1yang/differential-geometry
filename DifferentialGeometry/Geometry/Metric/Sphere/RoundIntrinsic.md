# RoundIntrinsic

## Purpose

This module connects the native explicit great circle to the complete
intrinsic geodesic and exponential map of the round metric.

## Route

The inclusion differential puts every sphere tangent vector in the ambient
orthogonal complement of the radius (`dIncl_orth`).  The explicit great circle
therefore has the same foot and launch velocity as `intrinsicGeodesic`.
`geo_eqOn_of_init` gives equality on all real times from global geodesicity and
continuity.  Spray homogeneity then supplies the radial exponential formula.

No connectivity or chart-selection assumption is introduced.  The theorem
uses the caller's honest Riemannian-bundle, pseudo-metric, completeness, and
continuous-bundle instances together with the explicit norm-compatibility
hypothesis required by `intrinsicGeodesic`.  The completeness instance is
indexed explicitly by the uniformity induced by that pseudo-metric; this keeps
the intrinsic round metric world separate from the sphere's canonical chordal
metric world.

## Verification

Focused verification and exact module verification passed after the
metric-world parameterization.  The module is `sorry`-free.

## Project status

`intrinsic_eq_gc`, `round_exp_radial`, and `round_exp_val` are proved and
verified (100%).  Together with the great-circle producer, the dedicated
explicit sphere-exponential/punctured-sphere package is approximately 40%
complete.  The final `ham3_space_box` theorem remains unproved (0%); its
dedicated classification machinery remains approximately 45% complete.

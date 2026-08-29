# TimeH1Flat

## Role

This module is the lower analytic producer for endpoint-flat time-Sobolev density.  It approximates
an arbitrary time-`L²` coefficient on a positive compact time interval by a globally smooth function
whose support lies strictly inside the interval.  Endpoint correction and integration into a
`timeH1` curve belong to the higher `TimeH1Density` layer.

## Route

The proof first uses Mathlib's finite-dimensional smooth compact-support density theorem.  It then
chooses an interior scalar bump whose transition region has sufficiently small measure.  Absolute
continuity of the `L²` norm on indicators controls the cutoff error.  The two approximation errors
are combined in the native `timeL2` metric.

## Status

Focused verification passed without warnings.  The theorem is sorry-free.

## Project progress

- `exists_flat_deriv`: proved and focused-check green (100%).
- Dedicated derivative-density machinery for endpoint-flat `timeH1` approximation: 100% for this
  lower producer.
- The higher endpoint-flat strong-density theorem is now 100% in
  `TimeH1Density.lean`; this lower module remains responsible only for its
  derivative approximation input.
- Perelman reduced-volume monotonicity (`redVolume_anti`): 0%; this generic analytic producer is
  reusable infrastructure and does not prove that geometric endpoint.

# StrongDuhamelBack

## Source status

Source implementation complete.  The focused Lean check passes without local
warnings, and the file contains no `sorry`, `admit`, axiom, opaque replacement,
or heartbeat override.

## Mathematical result

`strongPair_zero` proves uniqueness for an independently supplied strong pair
with zero trace and zero forcing.  It uses the existing cross-scale scalar
energy identity.  For every tensor eigenmode, the homogeneous equation gives

`c_i(t)^2 = integral (0,t) (-2 * lambda_i * c_i(s)^2) ds`.

Since every `lambda_i` is nonnegative, the integral is nonpositive, while the
left side is nonnegative.  Thus every continuous lower-scale mode vanishes.
The a.e. cross-scale link then implies that the `H^(a+2)` field vanishes too.

`duhField_pin` proves that the canonical Duhamel field and Duhamel `timeH1` map
represent the same lower-scale time-`L2` class.  Subtracting this canonical pair
from any independently supplied strong pair and applying `strongPair_zero`
gives `strongPair_eq_duh`, the reverse Duhamel realization theorem.

Finally, `strongNemy_fixed` converts an independently supplied strong solution
whose forcing equals its Nemytskii nonlinearity into the exact forcing fixed
point consumed by `quasilinear_strong_unique`.

`strongPair_unique` performs that final composition for two arbitrary strong
pairs.  The existing contraction theorem first identifies their forcing
terms; their reverse Duhamel representations then identify both top-scale
fields and both `timeH1` carriers.  Thus the abstract local uniqueness result
no longer applies only to solutions originally constructed by the fixed-point
solver.

`eqOn_of_step` supplies the abstract continuation wrapper.  On any compact
target interval where the local uniqueness horizon has a uniform positive
lower bound `delta`, it divides the segment to an arbitrary target time into
finitely many steps shorter than `delta` and iterates local forward uniqueness.
It is independent of the geometric gauge construction.

No Duhamel representation is assumed for the supplied pair, and this file adds
no axiom, opaque producer, `sorry`, or strengthened regularity hypothesis.

## Remaining Phase B bridge

The abstract reverse-realization layer is proved and focused-verified.  The
geometric uniqueness lane must now construct the common DeTurck
gauge for arbitrary smooth Ricci flows and verify that each gauged flow supplies
the trace, cross-scale link, strong equation, and Nemytskii forcing identity
expected here.  To use `eqOn_of_step`, the geometric layer must additionally
package time-translated/restricted strong pairs on each local window and supply
a uniform positive local horizon on each compact target interval.  The current
time-Sobolev API has no general translation/restriction constructor, so this
bridge is deliberately not hidden as an assumption here.  The harmonic-map
gauge construction is likewise not assumed in this file.

## Honest progress

- Exact endpoint `ricci_flow_forward_unique`: 0% until the existing theorem is
  proved and checked.
- Reverse Duhamel machinery: 100% in this abstraction layer, source-proved and
  focused-verified.
- Arbitrary-strong-pair local uniqueness machinery: 100% in this abstraction
  layer, source-proved and focused-verified.
- Abstract finite-step continuation machinery: 100% in this abstraction layer,
  source-proved and focused-verified.

# SecondVariationMinimiser.lean

## 2026-06-24

Factored the exponential-variation constructor used by the second-variation
minimum argument.

What landed:

- `Variation.exists_expVar_field`: the core intrinsic-exponential variation
  constructor. From a smooth base curve `gamma` and a bundle-smooth launch field
  `V`, it constructs a smooth two-parameter variation whose central curve is
  `gamma` and whose `s`-velocity at `s = 0` realizes `V` on `[0, L]`. Endpoint
  fixing is returned conditionally: if `V` vanishes at `0` or `L`, the
  corresponding endpoint is fixed.
- `Variation.exists_expVar_fixEnd`: the moving-start, fixed-final wrapper.
  This is the Step C-relevant form: if `V L = 0`, the final endpoint is fixed
  while the initial endpoint may move.
- `Variation.exists_variation_realising_field_via_exp` is preserved as the old
  endpoint-fixed API, now as a thin wrapper of the generalized constructor.

Why this matters:

- The first-variation/center-of-mass route needs moving-start, fixed-target
  variations. The previous constructor only exposed the endpoint-vanishing
  special case, which was too narrow for differentiating `q |-> d(q, pt)`.
- This does not construct the moving-base inverse-exponential field
  `s |-> exp_{beta s}^{-1}(pt)`. It only says that once a smooth launch field
  with final endpoint vanishing data is supplied, the corresponding smooth
  fixed-final variation exists.

Remaining frontier:

- Build the local smooth launch field for the fixed target `pt`, prove its
  exponential endpoint equation, and prove the corresponding local
  distance-equals-length statement. That is the next producer needed before the
  one-summand `grad (1/2 d(., pt)^2)` theorem can be closed.

Verification status: passed. The focused check and targeted module build for
this module succeeded. Axiom prints for `exists_expVar_field`,
`exists_expVar_fixEnd`, and the preserved
`exists_variation_realising_field_via_exp` wrapper are
`[propext, Classical.choice, Quot.sound]`; no new `sorryAx`.

## 2026-06-24 - field-level half-squared-distance derivative

Added `Variation.exists_sqDeriv_field`.

This theorem composes the moving-start/fixed-final exponential-variation
constructor with `Variation.halfSq_deriv_length`. From a smooth base geodesic
`gamma`, a bundle-smooth launch field `V`, and `V L = 0`, it constructs a smooth
variation realizing `V` and fixing the final endpoint. If that constructed
variation also locally realizes distance by arc length, then the derivative of
`1/2 * dist (f s 0) (gamma L)^2` is the first-variation boundary term with the
initial variation vector rewritten as `V 0`.

What this closes:

- The field-realization and first-variation pieces are now wired together.
- The remaining input is not the existence of a smooth variation from a field;
  it is the geometric construction of the correct moving-base inverse field and
  the proof that its resulting geodesic family realizes distance locally.

Verification status: passed. Focused check, targeted module build, and axiom
print for `exists_sqDeriv_field` succeeded; the axiom set is
`[propext, Classical.choice, Quot.sound]`.

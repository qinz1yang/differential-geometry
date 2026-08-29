# ChartTimeC1Overlap

## Shifted derivative

`chartDeriv_shift` identifies the `derivWithin` of a shifted `timeH1`
representative with the derivative of the original model-space curve on the
translated closed interval.  It uses Mathlib's native translation formula and
requires only equality of the representatives on the interval; no smoothness
or manifold assumptions are added.

`chartDeriv_change` transports the coordinate derivative of a `C¹` manifold
curve at one point between two charts.  The source chart contains the represented
set, while the target chart is required only at the point, which is the exact
form needed for node-centered one-sided derivatives.

Focused verification passed without warnings.

## Status

- `chartDeriv_overlap`: verified, 100%.
- `chartDeriv_head`: verified, 100%.  It compares a short representative with
  a longer representative on their common positive initial interval, while
  retaining the longer interval in the derivative on the right-hand side.
- The theorem is a generic fixed-interval chart adapter. It does not itself prove
  the Perelman node momentum-matching theorem, which remains 0% until stated and
  proved in its geometry layer.

## Native route

The proof uses only the existing `DifferentialGeometry` chart and time-Sobolev
APIs. On the closed interval, the two coordinate representatives are related by
the native transition map

`extChartAt I q ∘ (extChartAt I p).symm`.

The existing `hasFDerivWithinAt_tangentCoordChange` theorem identifies its
Fréchet derivative with `tangentCoordChange`. Composing it with the within
derivative of the first `C¹` representative and using uniqueness of derivatives
on a nondegenerate real interval gives the pointwise formula, including both
endpoints. No almost-everywhere extension, supplied transition object, or
cotangent wrapper is needed.

## Verification

Focused verification passed without warnings, `sorry`, or `admit`.

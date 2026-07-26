# HalfSqDistGradMain

## 2026-07-13 minimizing-tangent gradient producer

`grad_halfSqDist_min` is implemented, focused-green, and sorry-free. It proves
that the gradient of `1/2 d(., pt)^2` at `q` is `-v` from exactly the intrinsic
minimizing data used by the HCG selected branch:

- `expMapIntrinsic g hEnorm q v = pt`;
- the metric length of `v` equals the global Riemannian distance;
- the half-squared-distance summand is differentiable at `q`.

The non-diagonal proof normalizes `v` to a unit-speed intrinsic geodesic and
reuses `exists_gradVariation` and `halfSqDist_dir_deriv`. The diagonal proof
uses positive definiteness to show `v = 0` and the existing local-minimum
gradient theorem. No normal-chart source, qualitative radius, or realized-exp
agreement hypothesis is present.

This producer theorem is complete (100%). It is one comparison-geometry input
to the B1 minimizing-branch lane; it does not itself prove the center equation,
the uniform branch scale, `StepB1RawInput`, or a compactness endpoint.

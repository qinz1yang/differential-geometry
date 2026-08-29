# CovariantDerivativeComponents

## Status

- `covDerivComp_joint` is implemented without placeholders.
- Focused verification passed without warnings.
- The module artifact was refreshed successfully for downstream consumers.

## Result

`covDerivComp_joint` lifts joint smoothness of every component of a
time-dependent covariant tensor and every local-frame Christoffel coefficient
to joint smoothness of each component after one covariant derivative.

The proof is the reusable arbitrary-rank form of the successor step previously
embedded in `iterRmComp_joint`: joint smoothness of the frame directional
derivative is combined with the finite Christoffel correction sum. It stays at
the component layer and does not unfold tensor representations.

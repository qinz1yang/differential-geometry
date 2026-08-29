# Square-root reparameterization

## Checked content

`sqReparam gamma s = gamma (s^2)` reads a backward-time curve in regularized
time. `sqrtReparam alpha tau = alpha (sqrt tau)` is the inverse reading on
nonnegative time.

`lVelocity_sq` is the ordinary intrinsic chain rule under pointwise manifold
differentiability. `lVelocity_sq_pos` proves the same identity for every raw
curve at positive square-root time by using the totalized manifold derivative
in the nondifferentiable branch.

`lDensity_sq` and `lLength_sq` retain the original differentiable interface.
The stronger `lDensity_sq_pos` needs only `0 < s`, and `lLength_sq_ae` removes
all curve differentiability assumptions by discarding the possible pointwise
failure at the singleton `s = 0`. Both interval orientations are supported.

The proofs fully apply the metric to tangent velocities before doing scalar
algebra; no tangent-bundle or tensor representation is unfolded.

## Verification and next use

Focused verification and the targeted module export pass without warnings.
The inverse bridge is completed in `RegAction.lean` by `lLength_sqrt`.

`redVolume_anti` remains **0%**. The square-root and inverse square-root
change-of-variables infrastructure is **100%**; dedicated L-geometry machinery
overall is approximately **64--68%**, and reusable generic infrastructure is
approximately **94--96%**.

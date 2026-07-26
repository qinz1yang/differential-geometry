# CartanNorm.lean

## Role

This module is the first geometric consumer of
`Variation.jacobi_coord_xfer`.  It aims to identify the squared norm of the
intrinsic exponential differential on two curvature-one manifolds with
launch tangent metrics related by a continuous linear equivalence.

## Route

- choose a full orthonormal basis at the first launch point;
- map it through the supplied tangent metric isometry;
- parallel-transport both bases along the intrinsic geodesics;
- apply the cross-manifold scalar Jacobi-coordinate transfer to the two
  initial-velocity variations;
- recover the endpoint squared norms by `inner_self_eq_sum_sq`;
- identify the endpoint Jacobi fields with the exponential differentials via
  `intrinsic_jacobi_one`.

## Status

- `expDiff_sq_xfer` is proved without `sorry`.
- Focused verification passed, warning-free.
- Exact module verification passed (`3858/3858`).

## Elaboration lesson

The stable normal form keeps the intrinsic geodesic `γ` itself in theorem
statements, while deriving its finite-order smoothness from the central slice
of the smooth variation.  The explicit scalar equality `Fvar 0 = γ` then
transports the variation-field regularity lemmas.  This avoids asking Lean to
identify two hidden `RiemannianBundle` instance arguments in a direct use of
the global intrinsic-geodesic smoothness theorem.

## Honest progress

- `ham3_space_box`: 0%.
- The theorem `expDiff_sq_xfer`: 100%.
- The exponential-differential square-norm transfer producer: 100%.
- Dedicated positive Killing--Hopf machinery: about 30%.  Local Cartan map
  assembly and global sphere
  classification remain separate substantial phases.

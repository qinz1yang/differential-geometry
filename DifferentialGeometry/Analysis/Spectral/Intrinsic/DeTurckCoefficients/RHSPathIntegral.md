# RHSPathIntegral

## Role

This module integrates the public three-arm Ricci--DeTurck slope identity along
the realized metric segment. It is independent of the legacy oversized
remainder file.

## Verified state

`rhsTopPathIntegral`, `rhsLow0PathIntegral`, and `rhsLow1PathIntegral` are the
three concrete path coefficients. `rhsArm_sub_eq_paths` proves the exact
realized RHS difference as their actions on the order-zero, order-one, and
order-two covariant derivatives of the metric difference. The theorem has no
high-regularity or high-`a` assumption and is sorry-free. Focused verification
passes.

The named module refresh is currently blocked by an unrelated shared-tree
failure in `Geometry/Operator/Operators.lean`: the in-flight logarithm
gradient/Laplacian additions fail before this target is reached. This is a
verification blocker, not an open goal in this module.

The exact integrated identity is complete (100%). The mixed `H3 -> H1`
endpoint remains unstated and theorem-level 0%; uniform low-order coefficient
bounds and final Sobolev assembly remain.

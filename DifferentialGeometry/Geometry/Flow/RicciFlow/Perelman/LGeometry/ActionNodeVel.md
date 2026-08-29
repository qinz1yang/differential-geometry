# ActionNodeVel

## Status

`lNode_vel_match` is verified without warnings. It upgrades the cross-chart
momentum equation to equality of coordinate velocities after tangent-coordinate
transport, under exactly the assumptions of `lNode_mom_match`.

## Route

Use `chartGramOp_change` and the reverse tangent-coordinate change to turn the
scalar momentum identity into equality of the two vectors after applying the
right-chart Gram operator. Then use `chartGramOp_unit` to cancel that operator.
No bundle-valued comparison or new transition wrapper is introduced.

The reverse coordinate change is used only through the native
`tangentCoordChange_comp` and `tangentCoordChange_self` identities. Gram
invertibility is derived from the solution's smooth metric and the node's
regular backward time; it is not supplied as an assumption.

## Progress

The velocity-matching theorem and its dedicated momentum-to-velocity step are
100% complete. This closes the pointwise corner regularity input, not the global
minimizer or reduced-volume endpoints: `exists_lMinimizer` and
`redVolume_anti` remain 0%. Dedicated L-geometry machinery is approximately
90--92%; P2 remains below 1%, and the whole Poincare program remains
approximately 3--5%.

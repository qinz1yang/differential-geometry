# AppCcLpProduct

## Scope

This file isolates the closed-manifold product cells needed for a low-regularity
operator coefficient.  It deliberately does not import the high-order
`AppCcJetWindowTame` tower.

## Implemented facts

- `fiberLpFun` is the intrinsic pointwise fibre norm as a real-valued function.
- `fiberLp_slotExtend` gives the exact `sqrt(dim)` scaling under `slotExtend`.
- `fiberLp3_le_lp6` is the finite-volume `L6 -> L3` comparison.
- `appCc_l2_right` is the `L2 x L-infinity -> L2` arm.
- `appCc_l6_l3_l2` is the intrinsic Holder `L6 x L3 -> L2` arm.

The Holder proof uses `riemannianFiberNormSq_compRS_le_mul` pointwise and the
canonical mixed tensor `L2` integral bridge.  No Sobolev embedding is hidden in
this layer.

## Route notes

An initial import through `AppCcJetWindowTame` exposed unrelated stale exported
dependencies.  The source was narrowed to the canonical fibre-calculus and
mixed-`L2` packaging modules actually used by these facts.

## Verification

Focused source verification passes without local warnings, and the named
`AppCcLpProduct:olean` target is exported.  The product-cell machinery in this
file is 100% complete; the downstream `H1 x H2 -> H1` assembly is recorded in
`H1H2AppCc.md`.

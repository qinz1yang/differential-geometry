# LieCorr0Readout

## Role

This module is the public center-chart readout layer for the zeroth-order
DeTurck correction. It keeps raw-component and Euclidean conversion lemmas
private and exports only the first- and second-covariant-derivative readouts
and the exact first-jet split needed by the geometric reanchoring identities.

## Verified state

`lieArm1_center`, `lieR4_center`, and `lieU3_readout` are proved without
`sorry`, Sobolev-ball hypotheses, or high-regularity assumptions. Focused
verification and the named module build pass. The implementation is a small
extraction of the settled legacy path chain and reuses the public
realized-Gram derivative API.

## Frontier

The module itself is complete for its current role. Its next consumer is
`LieCorr0Field.lie0_order0_eq` and the first-order Lie reanchoring identity,
followed by the public three-arm lower-order residual identity. The mixed
`H3 -> H1` endpoint remains unstated and 0%; these readouts are supporting
machinery only.

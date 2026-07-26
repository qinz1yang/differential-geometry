# Weighted Hessian identities

## 2026-07-16 square completion

The checked producers are `weighted_hess_split`, `weighted_bochner`, and
`weighted_w_square`.  They combine the canonical Ricci drift, scalar weighted
Green identities, the Hessian trace bridge, and the metric tensor norm formula
to prove the weighted negative-square identity for
`Ric + Hess f - g / (2s)`.

The proof is dimension-uniform: rank zero is discharged directly and the
nonzero-dimensional instance is local to the other branch.  Every
varying-fiber tensor is fully contracted to a scalar before continuity or
integration is proved.  Focused verification and the targeted module refresh
passed with no local `sorry`.

`weighted_w_square` and its dedicated machinery are 100%.  The reverse-flow
derivative consumer is checked in `WVariation`; the global interval-monotone
wrapper, cutoff contradiction, Perelman no-local-collapsing, and
`ham3_noncollapse` remain separate theorem frontiers.

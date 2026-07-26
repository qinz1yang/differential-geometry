# ConnAddTrace status

## Source theorem

`connAddTrace_split` contracts the already proved full-state local-addition
Hessian split against an arbitrary finite coefficient matrix.  The only
second derivative of the state remains inside the vertical derivative of the
local addition.  `connAddTrace_cancel` proves that the inverse vertical
derivative cancels this factor after the whole contraction, not merely one
direction pair at a time.

`connAddTrace_blocks` then contracts the existing four-block decomposition.
It separates the remaining term into its value-only, two first-derivative
linear, and first-derivative quadratic pieces.  No second derivative of the
state occurs in any of these four blocks.

`exists_connAddTrace` chooses the compact state tube before the finite trace
data and supplies invertibility plus the cancellation for every coefficient
matrix and every section state in that tube.  This is the consumer-shaped
fixed-chart output; it does not move the radius after selecting a state.

This is the missing top-order Banach-calculus bridge needed before the
coordinate trace in harmonic-map tension can be turned into a prescribed
rough-Laplacian coefficient plus a first-jet remainder.  It introduces no
existence hypothesis and does not assume that a harmonic-map heat flow or a
diffeomorphism family already exists.

## Verification

The source contains no `sorry`, `admit`, axiom, or opaque producer.  Per the
shared serial-Lake assignment, no Lean or Lake process was started in this
lane, so the file is source-only and not yet counted as verified.

## Exact remaining bridge

The next producer must identify, in one fixed manifold chart, the coordinate
trace defining `diffeoTension` with `connAddTraceD2` plus the source and target
Christoffel corrections.  After `connAddTrace_cancel`, those corrections and
`connAddTraceRem` depend only on the state and its first spatial derivative;
their finite-cover coefficient bounds are what should instantiate
`HmfStateQuad` and the prescribed principal coefficient in `quad_fixed`.

The repository still lacks that general-map/chart tension realization and the
rough heat-potential/finite-atlas gluing producer.  It also lacks the common
edge `C1` persistence theorem that converts the resulting maps into a
diffeomorphism family on one fixed short window.  Therefore
`ricci_flow_forward_unique` remains theorem-level 0%; this file is only one
source-written machinery brick.

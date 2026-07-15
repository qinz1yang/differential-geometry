# OpenSubtype

## Role

This module is the canonical locality bridge between geodesics of a metric on
an ambient manifold and geodesics of its restriction to an open subtype.

## Current state

`geodesicOn_open_iff` is complete: on any time set `s`, a curve valued in an
open subtype is a geodesic for `g.restrictOpen U` exactly when its
`Subtype.val` curve is a geodesic for `g`. The global `geodesic_open_iff`
remains the corresponding all-time theorem. No independent smoothness
assumption on the curve is needed, because both proofs compare
`HasGeodesicEquationAt` directly.

The checked producer chain is:

- open-subtype tangent chart-coordinate changes agree with the ambient ones;
- centered Gram matrices and their local chart pullbacks agree;
- `christoffel_open` and `contr_open` identify the centered Christoffel data;
- `geodesicOn_open_iff` transports the moving-foot geodesic equation pointwise
  on an arbitrary time set; `geodesic_open_iff` gives the all-time form.

The theorem assumes `I.Boundaryless`. This is an honest condition for the
current `chartChristoffel` definition: its ordinary Frechet derivative uses a
full model-space neighborhood, while a model with boundary only supplies a
neighborhood within `Set.range I`. Removing this hypothesis would require a
separate intrinsic/corners-compatible Christoffel interface, not a local
rewrite.

Focused verification and the targeted module refresh passed without `sorry` or
`admit`.

## Project position

This open-domain locality producer is complete (100%). It is only one side of
the cross-model geodesic endpoint bridge (about 25% of that bridge); naturality
under the normal-coordinate diffeomorphism and endpoint identification remain.
The moving quantitative inverse theorem itself is still unstated (0%); its
dedicated machinery is about 65%, Step B/B1 infrastructure about 70%, and the
whole HCG compactness infrastructure about 47%.

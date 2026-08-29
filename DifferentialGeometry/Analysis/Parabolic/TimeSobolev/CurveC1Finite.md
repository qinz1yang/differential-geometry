# CurveC1Finite

## Result

`curve_c1_fin` iterates the generic two-piece manifold theorem
`curve_c1_join` over the first `m` adjacent intervals determined by a node
function `t : Nat → Real`.  It assumes `0 < m`, strict increase only for the
used adjacent nodes, closed-interval `C¹` regularity on every piece, and the
node-centered chart derivative equality at every internal node.  It concludes
closed-interval `C¹` regularity from `t 0` through `t m`.

The bounded natural-number interface avoids dependent-index transport while
remaining directly usable by finite `Fin` subdivisions.  Its hypotheses are
weaker than global `StrictMono t`: no values after `t m` are constrained.

## Boundary

This theorem is intentionally the positive strict-subdivision producer.
Repeated nodes and zero-length pieces require a separate compression theorem;
they are not handled by strengthening downstream consumer assumptions.

## Verification

Focused verification passed without warnings or placeholders.  The exported
module is refreshed for downstream finite-node assembly.

This file is generic C¹ infrastructure.  It does not prove any L-geometric
corner equation or reduced-volume theorem; `redVolume_anti` remains **0%**.

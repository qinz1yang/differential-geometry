# CurveC1Glue

## Result

`curve_c1_join` is the generic manifold-valued two-piece `C¹` gluing
producer.  For `a < c < b`, it assumes that the same curve is `ContMDiffOn`
on `[a,c]` and `[c,b]`, together with equality of the two `derivWithin`
values after composing with the extended chart centered at `gamma c`.  It
concludes `ContMDiffOn` on `[a,b]`.

The full pieces do not have to lie in one chart.  The proof uses continuity
to shrink both sides to a positive node neighborhood in the node-centered
chart, applies the existing model-space `contDiffOn_Icc_join`, and reuses the
original manifold regularity away from the node.  No completeness, finite
dimensionality, separation, compactness, or Ricci-flow assumptions are used.

## Finite-node use

After cross-chart velocity matching is transported into the chart centered at
each subdivision node, apply `curve_c1_join` inductively to merge consecutive
positive pieces.  Repeated nodes or zero-length pieces should first be removed
or compressed; the theorem deliberately records the honest strict inequalities
needed for one-sided derivatives on both sides.

## Verification

Focused verification passed without warnings.  The source contains no
`sorry` or `admit`.  This generic gluing producer is complete for its stated
interface; it does not prove the geometric node-velocity match or any reduced
volume theorem.  In particular, `redVolume_anti` remains at **0%**; this file
is reusable C¹ infrastructure rather than progress on that capstone theorem.

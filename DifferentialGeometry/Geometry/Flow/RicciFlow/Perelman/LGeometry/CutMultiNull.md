# CutMultiNull.lean

## Result

lCutMulti_null proves that the multiple-minimizer part of the fixed-time
L-cut image has zero Riemannian volume. It places every such endpoint either
in the already-null conjugate image or in the nondifferentiability set of the
fixed-time L-cost. lCut_null then combines this result with lCutConj_null and
lCut_split.

The public statements expose no time-positivity assumption. If the multiple
part is nonempty, positivity and the regular backward-time slab follow from a
minimizing cut tangent; if it is empty, nullity is immediate.

## Verification

Focused verification passed without warnings or placeholders after refreshing
the two direct cut-branch dependencies needed by this new module.  No cut-set
measurability is required: nullity is passed through set inclusion and finite
union at the outer-measure level.

## Project status

`lCutMulti_null` and `lCut_null` are 100% proved and focused green.  Their
direct producers `lCost_chart_lip`, `lCost_nondiff_two`, and `lCutConj_null`
are also focused green.  This completes the fixed-time cut-image nullity stage;
it does not prove reduced-volume monotonicity.  The endpoint `redVolume_anti`
remains unstated and unproved at 0%.

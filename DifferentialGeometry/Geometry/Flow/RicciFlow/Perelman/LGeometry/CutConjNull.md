# CutConjNull

## Result

`lCutConj_null` proves that the conjugate part of the fixed-time L-cut image
has zero Riemannian volume on a compact manifold, for an arbitrary smooth
Riemannian metric.

## Route

Choose finitely many canonical chart sources covering the compact manifold.
In each chart, `lConjChart_null` applies finite-dimensional Sard to the
fixed-time L-exponential and makes its conjugate coordinate image null for the
canonical model Haar measure.  The generic `chart_model_null` theorem pulls
that null set back to Riemannian volume.  `null_of_chart_cover` assembles the
finite family.

## Scope

This closes only the conjugate branch.  The multiple-minimizer branch
`lCutMulti_null` remains separate and requires the L-cost nondifferentiability
route.  No measurability or nullity hypothesis is added as an assumption.

## Verification

Focused verification passed without warnings or placeholder proofs.

Project accounting: `lCutConj_null` is 100%; the separate
`lCutMulti_null` theorem and hence the full cut-image null theorem remain 0%.
`redVolume_anti` remains 0%.  Dedicated compact ordinary-flow L-geometry is
about 97--98%; generic measure/chart infrastructure used here is 100%; P2
remains below 1%, and the whole Poincare program remains about 3--5%.

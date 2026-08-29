# CutConjSard

## Goal

Prove the Euclidean Sard component of the conjugate L-cut-locus argument in a
single fixed target chart, without assuming the missing manifold-volume
transfer theorem.

## Route

Compose the fixed-time L-exponential with one extended target chart.  At an
L-conjugate tangent, the L-exponential differential has a nonzero kernel
vector; composing with the chart differential preserves that kernel vector,
so the coordinate differential has determinant zero.  Mathlib's
finite-dimensional Sard theorem then makes the coordinate image null.

## Scope

This file deliberately stops before transporting the coordinate null set back
to Riemannian volume or assembling a chart cover.  Those are generic measure
and atlas-localization producers, not L-geometry assumptions.

## Verification

Focused verification passed without warnings or placeholder proofs.  The
export was refreshed for the downstream global conjugate-null theorem.

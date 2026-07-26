# LocalDiffeomorph

## Role

This module exposes the canonical smooth local-diffeomorphism property of the
universal-cover projection.

## Route

`proj_localDiffeo` uses the pulled-back chart identity
`extChartAt_proj_eq`.  In those preferred charts the projection has derivative
`ContinuousLinearMap.id`; the existing infinite-order manifold inverse-function
theorem then gives a local diffeomorphism at every cover point.

This route uses only the manifold hypotheses already required to construct the
smooth universal cover.  In particular, it does not introduce a metric,
positive dimension, or a new structure class.

## Verification

Focused verification and exact module verification both passed without local
warnings.  The imported `UniversalCover.Manifold` module still reports its
pre-existing unrelated `sorry`; this new module contains no `sorry`.

## Downstream composition seam

The intended round-quotient map has the form `proj ∘ d`, where `d` is a
diffeomorphism onto the universal cover.  Mathlib's local-diffeomorphism file
does not currently expose a composition theorem, and its internal
`PartialDiffeomorph` API deliberately lacks composition.  The next reusable
seam is therefore a generic `IsLocalDiffeomorph.comp` theorem (or a short
project-local `hloc_comp` adapter) at the coordinates layer.

## Project position

This is infrastructure only.  It closes the projection half of the
round-quotient local-diffeomorphism witness, but does not prove the quotient
assembly or `ham3_space_box`; both endpoint theorems remain at 0%.

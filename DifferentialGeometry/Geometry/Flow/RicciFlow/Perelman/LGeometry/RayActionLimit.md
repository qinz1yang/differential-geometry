# RayActionLimit

## Status

`RayActionLimit.lean` is focused-check green and contains no placeholders or
warnings.

## Public result

- `lRayAct_tendsto` proves continuity of the regularized action of the maximal
  L-ray when both its initial tangent and its positive terminal square-root time
  converge, provided the limiting terminal time lies in the limiting ray's
  regularized domain.

The theorem evaluates the moving metric and velocity completely to real-valued
Lagrangians before taking limits; it does not compare tangent-bundle or Hom
objects directly.

## Proof route

The local smooth family supplied by `lRegFamily_extend` gives joint continuity
of the scalar regularized Lagrangian.  After discarding a finite prefix, the
initial tangents and terminal times lie in compact subsets of that family.
Compactness supplies a uniform scalar bound.  Dominated convergence handles a
fixed limiting interval, while the uniform bound makes the residual interval
between the varying and limiting endpoints tend to zero.  Action additivity
then identifies the result with the maximal L-rays.

## Role and next use

This is the varying-length action-continuity producer needed by minimizing-ray
stability.  It should be combined with upper semicontinuity of `lCost` to prove
that a convergent sequence of minimizing initial tangents has a minimizing
limit.  It does not itself provide boundedness or a convergent subsequence of
minimizing tangents.

## Honest progress

- `lRayAct_tendsto`: 100%.
- Minimizing-vector stability theorem: 0%; this file supplies its ray-action
  limit input.
- `lCut_alt`: 0% until stated and proved.
- `redVolume_anti`: 0%.

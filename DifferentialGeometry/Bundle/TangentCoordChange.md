# TangentCoordChange

## Role

This module exposes the pointwise compatibility between tangent-coordinate
changes and inverse tangent-bundle trivializations.  It stays at the bundle
layer and does not depend on metric or Ricci-flow objects.

## Public API

- `symmL_coordChange`: applying the inverse trivialization for the target chart
  after `tangentCoordChange` gives the same tangent vector as applying the
  inverse trivialization for the source chart.

## Route

The proof identifies the target-chart forward trivialization composed with the
source-chart inverse trivialization with `tangentCoordChange`, using the native
three-chart composition theorem, and then cancels the target trivialization
pointwise.  It compares only fully applied tangent vectors, not whole bundle or
Hom representations.

## Verification

Focused verification passed without warnings or placeholders.  The theorem
uses only the `C¹` manifold instance needed by tangent-coordinate changes.

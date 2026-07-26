# RightDerivative

## Role

This file provides the reusable analysis bridge from a continuous right-sided
ODE interface on a compact real interval to ordinary differentiability in the
interior.

## Current state

- `hasDerivAt_of_right` compares the original curve with the interval-integral
  primitive of its continuous prescribed derivative.
- `contDiffOn_of_right` upgrades an autonomous smooth right-sided ODE to
  `C^∞` regularity on the open interior, using compact subintervals around
  each interior time.
- Focused verification passed without warnings.

## Frontier

The Hamilton compactness consumer can now apply both bridges directly to the
fenced phase flow.  The remaining regularity issue is only the local-manifold
interface needed by cross-model geodesic naturality.

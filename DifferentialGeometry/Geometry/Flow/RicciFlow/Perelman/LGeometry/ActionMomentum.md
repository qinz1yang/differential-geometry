# ActionMomentum

## Role

This file supplies the fixed-chart closed-interval momentum regularity needed
before the Weierstrass--Erdmann node matching step.

## Status

- `lChart_mom_c1` is implemented and verified without placeholders.
- The theorem retains exactly the assumptions of `lChart_min_c1`.
- It returns a continuous coordinate velocity and a `C¹` momentum, with the
  momentum and its derivative identified pointwise on the full closed interval.

## Route

The proof reuses `lChart_min_c1`, replaces the raw weak force almost everywhere
by `lChartForceRep`, applies the generic `mom_rep_c1` primitive theorem, and
extends the almost-everywhere momentum identity to the endpoints using
continuity.  No cotangent-transition API or new frontier wrapper is introduced.

## Verification

Focused verification passed cleanly.

## Project position

- `lChart_mom_c1`: verified (100%).
- `lNode_mom_match`: not started (0%).
- `redVolume_anti`: not proved (0%).

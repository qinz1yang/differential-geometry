# Scalar time-dependent heat equations

## State — 2026-07-09

`IsHeatPotOn` is the canonical low-layer predicate for a classical solution of

`∂ₜu = Δ_{g(t)}u + V(t)u`

on a `RealTimeInterval`.  The function `u` remains separate data.  The
predicate records joint smoothness on the regular interior, joint continuity
on the full carrier, smooth spatial slices including endpoints, and the actual
pointwise equation at regular times.

This is the intended target interface for the forward time reversal of
Perelman's conjugate heat equation, where the reversed potential is `-R`.
Positivity, normalization, terminal data, existence, and uniqueness are not
fields of this predicate and must be supplied by genuine producer theorems.

## Remaining frontier

`IsHeatPotOn.mono` now restricts a classical solution along inclusions of the
carrier and regular time sets.  It is the canonical interval-shrinking bridge
used when independent coefficient and reconstruction windows are intersected.

The generic low-layer existence problem remains separate, but the Ricci-flow
Galerkin specialization now constructs `IsHeatPotOn` in
`Entropy/ConjGalerkinClassical.lean`.  The next shared low-layer frontier is
strict positivity and interval-local moving-mass variation, not existence of
the Ricci-flow specialization.

## Honest progress

- `IsHeatPotOn` interface: 100%.
- `IsHeatPotOn.mono`: theorem and dedicated restriction machinery 100%, with
  focused and targeted verification passing.
- Generic `exists_heat_pot`: still not stated or proved (0%); the separate
  Ricci-flow Galerkin existence theorem is complete in its higher layer.
- Perelman no-local-collapsing and `ham3_noncollapse`: not proved (0%).

Focused verification passed without warnings or `sorry`.

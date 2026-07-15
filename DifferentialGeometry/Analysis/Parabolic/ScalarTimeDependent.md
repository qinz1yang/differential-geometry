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

The missing producer is non-autonomous scalar parabolic existence for a smooth
time-dependent metric and potential on a closed manifold.  Existing heat
semigroup and mild-solution APIs use one fixed metric and one fixed
`L²(dμ_g)` space, so they do not construct an `IsHeatPotOn` witness for a
moving metric.

## Honest progress

- `IsHeatPotOn` interface: 100%.
- `exists_heat_pot` theorem: not stated or proved (0%).
- Dedicated conjugate-heat existence machinery: about 5%; the analytic
  existence producer itself remains 0%.
- Perelman no-local-collapsing and `ham3_noncollapse`: not proved (0%).

Focused verification passed without warnings or `sorry`.

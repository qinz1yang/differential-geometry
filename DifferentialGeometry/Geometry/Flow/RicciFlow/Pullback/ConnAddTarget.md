# ConnAddTarget

## Scope

This module is the small target-coordinate interface between the intrinsic
component-local addition and the harmonic-map gauge calculus.  It deliberately
does not import the maximal-regularity, spectral, energy, or Ricci-DeTurck
principal-operator layers.

## Facts

- `localAddZeroCoord` is the chart coordinate of the zero tangent vector.
- `localAddTarget` is the target projection of `connAddChart`.
- `localAddTarget_fd` identifies its full derivative at zero with the
  unipotent target projection.
- `localAddTarget_vert` specializes that derivative to the identity on a
  vertical direction.

The names differ from the older copies embedded in `HarmonicPrincipal` so that
the two modules can coexist while that large source-only file is refactored.
There is no axiom, placeholder, new class, or global instance.

## Verification

Focused checking is green with no warning in this file, and the named targeted
export build is green at **3786/3786**.  The target-coordinate producer is
therefore 100% source-written and 100% Lean-verified.

This is supporting gauge machinery only, so `ricci_flow_forward_unique` remains
**0%** until its exact theorem is proved and verified.

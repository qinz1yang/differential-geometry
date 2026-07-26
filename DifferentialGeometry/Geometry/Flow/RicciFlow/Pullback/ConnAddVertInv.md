# ConnAddVertInv

## Result

This file adds the fixed-chart vertical-invertibility package for the
component-local exponential addition.

- `connAdd_part_zero` identifies
  `partialFDeriv₂ (localAddTarget g p)` at `localAddZeroCoord p` with the identity
  continuous linear map.
- `connAdd_part_cd` proves that the vertical derivative field is `C¹` at that
  point.  It uses the existing total-space `C²` producer `connAdd_cd`, converts
  it to the fixed chart through `contMDiffAt_iff`, and composes `fderiv` with
  the canonical vertical inclusion.
- `connAdd_inv_cd` proves `C¹` regularity of the totalized inverse derivative
  at the zero section, using the open invertible-operator locus.
- `exists_connAdd_tube` chooses `r > 0` so that the closed coordinate ball of
  radius `r` is compact, every vertical derivative on it is invertible, and
  the inverse field is continuous on the ball.

No new class, global instance, notation, axiom, opaque declaration, or
placeholder is introduced.  The inverse-map calculus is given the standard
private local `CompleteSpace E` instance obtained from
`FiniteDimensional.complete`; it does not install or change a global instance.

## Scope and remaining uniformity gap

The radius produced by `exists_connAdd_tube` depends on the fixed basepoint
`p` and its component-local chart.  This is enough for pointwise chart
realization and is the strongest direct consequence of the current API.

A single radius uniform over all `p : M` does not follow merely by applying
compactness to these statements: `localAddTarget g p` is written in a chart
whose center and connected-component subtype both depend on `p`, and the tree
currently has no common finite-atlas coefficient map whose vertical derivative
is jointly continuous in `(p,z)`.  The smallest missing global producer is a
finite fixed-chart local-addition family, with overlap compatibility, carrying
joint `C¹` regularity of its vertical derivative.  Compactness could then shrink
the finitely many chart radii to one positive radius.

## Verification

The file now imports only the verified `ConnAddTarget` interface rather than
the large source-only `HarmonicPrincipal` module.  Focused checking is green
with no local warning, and the named targeted export build is green at
**3800/3800**.  This fixed-chart vertical-inverse package is therefore 100%
source-written and 100% Lean-verified.

The exact endpoint `ricci_flow_forward_unique` remains **0%**; this file is
supporting gauge machinery and does not yet supply the finite-atlas uniform
tube or the harmonic-map heat-flow solution.

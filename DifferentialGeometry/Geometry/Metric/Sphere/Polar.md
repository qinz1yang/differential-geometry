# Polar

## Role

This module supplies the ambient polar-coordinate algebra needed by the
positive constant-curvature classification route.  It is independent of the
intrinsic exponential-map implementation.

## Route

- `spherePolar` is the usual cosine/sine polar map about a unit pole.
- `spherePolarInv` is its arccosine/radial inverse on the open ambient locus
  `|⟪p,x⟫| < 1`.
- `polar_decomp` proves the canonical decomposition of every unit vector away
  from the two antipodes.

The statement shape was informed by the read-only
`frenzymath/Poincare-Conjecture` Exercise 1.6.20 implementation, but only the
small decomposition and smooth-inverse facts needed by the native
classification route were implemented.

## Verification and progress

Focused verification passed without warnings.

`ham3_space_box` itself is still unproved and therefore 0%.  This file supplies
one coordinate producer for the global sphere-gluing phase; the dedicated
positive Killing--Hopf machinery is approximately 32% complete.  The remaining
substantive frontier is to turn the Cartan/Jacobi differential comparison into
compatible local isometries and then perform the two-chart global gluing.

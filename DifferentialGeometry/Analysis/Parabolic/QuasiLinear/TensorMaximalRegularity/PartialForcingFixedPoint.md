# PartialForcingFixedPoint

## 2026-07-19

The implementation is focused-check green and warning-free, and its named
`.olean` has been refreshed.  It contains no `sorry`, `admit`, axiom, or
replacement hypothesis.

The file defines the lower-order state ball and a quantitative forcing-space
fixed-point theorem `partial_sol_const`.  Its output retains the existing
solution-space, state-membership, forcing, trace, PDE, and forcing-radius
fields.  The horizon depends only on the displayed quantitative constants.

This theorem assumes a global Lipschitz constant on the state subtype.  It is
a valid generic producer, but it is not by itself the final Ricci--DeTurck
solver: the concrete nonlinearity on an `H2` state ball has unbounded
pointwise `H3` norm and instead satisfies the three-arm tame estimate packaged
in `TameForcingFixedPoint.lean`.

Endpoint accounting: this generic fixed-point machinery is verified; both
exact endpoint theorems remain 0%.

# TimeQuadraticBoundary

## Scope

This module evaluates the time-quadratic weak Euler pairing against the two
affine endpoint ramps.  It is a generic real Hilbert-space API below the
Perelman L-geometry consumer layer.

## Theorems

- `mom_ramp_up`: the ramp from `0` to `z` returns `inner (P T) z`.
- `mom_ramp_down`: the ramp from `z` to `0` returns `-inner (P 0) z`.

The assumptions are only `T > 0`, closed-interval `C¹` regularity of `P`, and
the pointwise identity `derivWithin P = F`.  No finite-dimensionality,
completeness, or separate continuity hypothesis on `F` is used.

## Verification

Focused verification passed without warnings.  The generic product-rule route
through the closed-interval `C¹` fundamental theorem of calculus was sufficient;
no missing API or failed proof frontier remains in this module.

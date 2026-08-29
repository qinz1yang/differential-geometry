# `TimeH1Buffer.lean`

## Purpose

This file supplies the reusable compact affine-line buffer for time-`H¹`
curves.  It belongs in the generic time-Sobolev layer because it uses only the
continuous representative and its compact-interval norm bound.

## Result

- `exists_line_scale` chooses a positive scale at most one such that the full
  coefficient-time rectangle `[-1,1] × [0,T]` stays in any prescribed open
  neighborhood of the base curve image.
- No nonnegativity assumption on `T` is needed; the compact-set proof also
  handles an empty interval.
- The construction combines a positive compact-neighborhood thickness with a
  uniform bound for the variation and then takes the minimum with one.

## Verification

Focused verification passed without warnings.  The file contains no placeholder
proofs.

## Project accounting

The theorem is generic reused infrastructure and does not itself prove a
Perelman node condition or minimizer theorem.  This helper is complete at the
source level; its downstream L-geometry consumer remains a separate frontier.

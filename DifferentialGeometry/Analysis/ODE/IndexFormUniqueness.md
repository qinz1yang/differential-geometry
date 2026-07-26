# IndexFormUniqueness

## 2026-07-23

This module carries the first continuation brick of Route B, N-d, without
editing the actively claimed `IndexForm.lean`.

`IsJacobiSolOn.eq_zero_of_interior` states that a bounded-coefficient Jacobi
ODE solution whose position and velocity both vanish at an interior time
vanishes on the entire interval.  The proof uses the zero-data second-order
Gronwall estimate to the right and repeats it after time reversal to the left;
velocity vanishing then follows from uniqueness of derivatives on the
interval.

Focused verification passed.  The downstream use is to show that the Jacobi
field coming from a nonzero conjugate direction has nonzero covariant
derivative at its interior zero.  The truncated-field cross term and smooth
corner perturbation remain separate, unproved N-d bricks.

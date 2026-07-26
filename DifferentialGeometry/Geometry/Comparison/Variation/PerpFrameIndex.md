# PerpFrameIndex

## Purpose

This module is the geometric realization bridge for the abstract negative
index-form direction used in the minimizing-implies-no-interior-conjugate
argument.  Coefficients live in `EuclideanSpace`, not the sup-norm plain
function space, so the abstract Hilbert index form has the intended sum inner
product.

## Current state

Focused verification passes without warnings.  The module now supplies:

- the finite-frame lift and the symmetric smooth curvature operator;
- smoothness, perpendicularity, endpoint, pointwise, and integrated
  index-form identifications for lifted coefficient fields;
- a pointwise expansion theorem for a complete orthonormal frame of the
  perpendicular space, including the one-dimensional empty-frame case;
- coefficient reconstruction and preservation of nonzeroness;
- the exact first-order coefficient Jacobi ODE in a parallel frame; and
- perpendicularity of a globally differentiable Jacobi field that vanishes at
  two distinct times.

The module also exports `perpCoeff_smooth`, the smooth coefficient field used
by the arbitrary-length minimizing-geodesic assembly.  That downstream source
now exists in `MinimalGeodesicNoConjugate`; it still awaits the ordered
artifact refresh and focused verification before its public theorem is
counted as complete.

## Project accounting

`perpCoeff_smooth` and the fixed-frame bridge are focused-green (100% theorem
and dedicated machinery).  The downstream arbitrary-length no-conjugacy
theorem remains 0% until its own verification passes; this module alone does
not prove it.  The final Calabi support theorem is a separate 0% endpoint.

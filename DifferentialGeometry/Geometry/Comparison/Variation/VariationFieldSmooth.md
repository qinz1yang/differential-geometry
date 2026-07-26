# VariationFieldSmooth

## Purpose

This module supplies the missing global regularity bridge for the
no-interior-conjugate-point argument: the transverse derivative of a
globally `C∞` two-parameter manifold variation is itself a globally `C∞`
section of the tangent bundle along the central curve.

## Current state

`varField_smooth` is implemented using the manifold partial-derivative API
and total-space trivialization coordinates.  Focused verification passes
without warnings.

## Project accounting

This is regularity infrastructure for Route B, brick N-d.  It does not prove
the minimizing-geodesic no-conjugate endpoint, which remains 0% until its
final theorem is stated and checked.

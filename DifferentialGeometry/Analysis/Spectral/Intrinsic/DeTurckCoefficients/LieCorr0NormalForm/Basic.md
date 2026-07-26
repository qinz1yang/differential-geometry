# Basic zeroth-order DeTurck normal forms

## Role

This module is the public finite-dimensional algebra base for the zeroth-order
DeTurck coefficient readout.  It was extracted from the settled private
`M0Abstract` chain in `DeTurckRemainderTameLipschitz.lean`.

It exposes the scalar blocks `p1B` through `p4B`, the insertion and contraction
forms, and the three stage equalities.  The statements contain no manifold,
regularity, Sobolev, metric-ball, or high-norm assumptions.

## Verification

Focused verification passed without `sorry`.

## Frontier

These identities are algebraic inputs to the still-unproved public lower Lie
readout.  They do not by themselves prove the mixed H3 to H1 estimate.


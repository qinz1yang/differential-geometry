# ScalarPotentialTime

## Purpose

This module transfers jointly smooth rank-zero scalar coefficients through the
completed Sobolev multiplier on a moving input path. It is the scalar
potential arm of the all-order Galerkin velocity bootstrap.

## Verified state

`scalarPot_dyn_fin` proves finite-order `ContDiffOn` regularity and
`scalarPot_dyn_cd` proves `C^infinity` regularity. Both compose
`scalarCc_joint`, `appHs_dyn_fin`, and the fully applied `scalarPotHs_app`
adapter. No whole-operator equality, locally constant chart selector, or new
consumer hypothesis is used.

Focused verification and the targeted export refresh are green. Both theorems
and their dedicated machinery are **100%**.

## Frontier

The scalar potential time-regularity frontier is closed. Its Galerkin consumer
`galLimExt_smooth` is also proved; the next separate producer is the
compact-interior spectral jet majorant used for rank-zero reconstruction.

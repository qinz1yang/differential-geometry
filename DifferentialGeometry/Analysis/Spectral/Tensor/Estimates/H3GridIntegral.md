# H3GridIntegral

## Purpose

This file is the three-dimensional integration bridge used by the
low-regularity Ricci--DeTurck coefficient estimates.  A four-term squared
metric jet (covariant orders zero through three) controls every intrinsic
antidiagonal product grid of total order at most three in `L1`.

## Current state

- `h3_grid_int` has been written from the existing pointwise `C0` and
  Gagliardo--Nirenberg estimates and the canonical grid-product integral API.
- The statement uses no derivative of the metric perturbation above order
  three.
- Source verification is pending the shared sequential artifact refresh.  No
  focused Lean check has yet succeeded or failed on the theorem body.

Endpoint theorem progress remains 0%; this is producer machinery only.

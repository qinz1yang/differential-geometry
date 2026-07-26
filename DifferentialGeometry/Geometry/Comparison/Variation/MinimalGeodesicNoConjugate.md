# MinimalGeodesicNoConjugate

## Purpose

This is the Route B, brick N-d endpoint: a unit-speed intrinsic geodesic that
minimizes length on an arbitrary positive interval `[0,L]` has no conjugate
vector at an interior radial time.  The former unit-interval theorem remains a
compatibility wrapper.

## Current state

The final contradiction is written through the conjugate-vector rescaling,
parallel perpendicular frame, coefficient Jacobi ODE, globally smooth
negative index direction, geometric frame lift, and second-variation
nonnegativity.  The arbitrary-length source endpoint is
`not_conj_of_min_len`.  The initial covariant derivative is transported from
the canonical intrinsic Jacobi curve to the local let-bound curve using
`covDerivAlong_congr_curve`, avoiding a dependent-function rewrite.
Focused verification passes without diagnostics; no mathematical frontier
remains inside this file.

## Project accounting

`not_conj_of_min_len` and its dedicated source machinery are 100% at source
level; the targeted artifact refresh is still pending.  The shifted-tail
no-conjugacy theorems and final Calabi support theorem are separate downstream
0% endpoints until their own proofs are checked.

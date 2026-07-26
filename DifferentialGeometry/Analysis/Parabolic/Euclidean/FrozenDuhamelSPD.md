# FrozenDuhamelSPD

## Scope

This file is the fixed positive-definite coordinate-conjugation layer over
the isotropic producer in `FrozenDuhamel.lean`.  It is dimension-generic in
the finite coordinate index and Banach-valued in the evolved field.

## Current source state

- `linPullBcf`, `pullJet1`, and `pullJet2` package pullback of a bounded
  spatial datum and its realized first and second Frechet jets through a
  continuous linear equivalence.
- `linPull_fderiv` and `pullJet1_fderiv` prove that those are the actual
  transformed jets; no regularity is assumed for the conjugated functions.
- `lapEval_basis` proves basis-independence of the trace using Mathlib's
  canonical covariant tensor.
- `factorLap_pull` identifies the factor-direction trace of a Hessian pulled
  back by the inverse equivalence with the isotropic trace.
- `spd_factorLap` expands the self-adjoint square-root factor and identifies
  it with the explicit double contraction `sum_i sum_j A_ij B(e_i,e_j)`.
- `spdDuh`, `spdDuhD1`, and `spdDuhD2` are the value, gradient, and Hessian
  maps in the original coordinates.
- `spdDuh_zero`, `spdDuhD1_zero`, and `spdDuhD2_zero` expose the common zero
  trace.
- `spdDuh_pde` states the consumer-shaped result: the first two conjuncts
  realize the value/gradient/Hessian chain and the third is
  `∂t spdDuh = matrixLap A spdDuhD2 + a(t)u`.

## Verification

The source was written while another shared lane owned the sole Lean build
slot.  No Lean command has yet been run on this file.  It contains no
`sorry`, `admit`, axiom, opaque placeholder, or assumed conjugation/PDE
identity.  The matrix-factor expansion and all source percentages remain
unverified until the focused check is allowed to run.

## Honest progress

- Exact endpoint `ricci_flow_unif_existence`: **0%** (unchanged).
- Fixed-SPD zero-trace Duhamel producer: **100% source-level**, **0%
  verified**.
- Consumer-visible value/gradient/Hessian/PDE interface: **100%
  source-level**, **0% verified**.

The exact next action is focused verification of `FrozenDuhamel.lean`
followed by this file.  The first exact obstruction, if any, must be recorded
as an elaborated Lean goal/error rather than inferred from this source-only
state.

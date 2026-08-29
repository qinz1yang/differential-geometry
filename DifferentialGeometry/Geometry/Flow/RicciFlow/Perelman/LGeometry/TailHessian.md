# TailHessian

## Scope

This module is the noncompact positive-start Hessian brick for the Calabi
tail branch. It mirrors the checked fixed-base `LocalBranch.lActBranch_hess`
route while retaining the actual positive-start family and its native endpoint
local inverse.

## Source state

`lTailBranch_hess` is source-written. For a jointly smooth family on an open
parameter-time product, fixed positive-start position, regular backward times,
injective terminal endpoint differential, and the honest hypothesis that every
nearby parameter curve satisfies the regularized L-Euler equation on `[a,b]`,
it identifies the fixed-`b` tail-action Hessian with the terminal metric pairing
against the covariant derivative of the induced parameter-variation L-Jacobi
field.

The proof first differentiates the actual action at every nearby parameter
using `lTailAct_joint`, cancels the endpoint local-inverse differential, and
identifies the branch gradient with terminal L-velocity. A bounded endpoint
curve and smooth time clamp then produce a global smooth variation;
`commute_ds_dt_intrinsic` identifies the covariant derivative of terminal
velocity with the terminal covariant derivative of the parameter field, and
`hessFun_eq_cov_local` gives the Hessian formula. No `CompactSpace`, desired
inequality, supplied index nonnegativity, new class, frontier wrapper, `sorry`,
or `admit` is present.

Focused verification is warning-free green after the coordinated named refresh
of `TailActionBranch`. Thus `lTailBranch_hess` and its dedicated derivative,
gradient, and covariant-commutation machinery are **100% theorem-complete**.

## Tail comparison brick

`lTail_hess_le` is source-written and warning-free focused green. Its inputs
retain the original minimizing regularized L-curve on the full span `[0,b]`,
while the positive-start family supplies the actual endpoint branch only on
`[a,b]`. The comparison field is required to be merely `C^8` on an open
neighborhood of `[0,b]`, with `W(a)=0` and `W(b)=Y`; no global smoothness,
tail minimality, or caller-supplied index nonnegativity is assumed.

The proof defines the induced affine-line Jacobi field `J` using
`lTailLine_jacobi` and identifies its terminal value with `Y` using
`lTailLine_deriv` and the endpoint local inverse. It globalizes only the smooth
`J`/base pair on `K ∩ Omega`, composes `W` with the same clamp, and forms the
global `C^8` field `Q = W - J`. Germ transfer by `lRegData_congr` and
`lRegAction_congr` preserves the original full-ray geometry and minimizing
property. `lIndex_sum_nonneg` applied to a zero head on `[0,a]` and the `Q`
tail on `[a,b]` gives tail-index nonnegativity, which is transferred back by
`lIndex_germ_congr`. Finally, `lRegIndex_jacobi`, `lIndex_sq_add`, and
`lTailBranch_hess` identify the branch Hessian and prove the comparison.

No new cutoff API was needed. The initial failed check exposed only local Lean
issues: a needed `NeZero` instance, a missing reflexivity closure in one germ
proof, global-versus-local bundle smoothness algebra, and zero-field coercions.
Using the already-globalized fields for integrability and proving the zero-head
index with `lRegIndex_smul` resolved them without changing the mathematical
route.

## Progress accounting

- Whole P0--P9 infrastructure: approximately **15--25%**.
- Dedicated noncompact L8--L9 L-geometry: approximately **58--60%**.
- `lTailBranch_hess`: theorem endpoint and dedicated machinery **100%**.
- `lTail_hess_le`: theorem endpoint and dedicated assembly **100%**.
- Tail Laplacian and Hamilton-tail barrier formulas: **0% theorem endpoints**.
- All-point spacetime weak barrier, `exists_redLen_le`, `redVolume_late_low`,
  `smooth_nlc`, P2, and the final Poincare endpoint: **0% theorem endpoints**.

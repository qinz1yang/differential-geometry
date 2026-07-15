# Scalar Laplacian-difference core realization

## 2026-07-14 status

`lapDiffCore_eq_cc` is stated in its canonical low-layer location.  It
identifies the genuine finite spectral operator value `lapDiffCore q h v` with
the `L²(q)` realization of
`scalarLapDiffCc q h (tensorHsSmoothRepr v)` and adds no assumptions.

The former localized `sorry` in `lapDiff_unit` has been removed in source.
The proof now follows the invariant identity already provided by
`lap_sub_conn`:

```text
Δ_h u - Δ_q u
  = (tr_h Hess_q u - tr_q Hess_q u)
      - tr_h ((∇^h - ∇^q) ⋅ du).
```

The realization boundary is closed by three genuine producers:

- connection layer: `secondRS_scalar` for the explicit rank-zero second
  covariant derivative;
- spectral realization layer: `grad_repr_apply` for `duSec`;
- spectral realization layer: `grad2_repr_diag` for diagonal `hessianSec`
  readout.

The consumer keeps the remaining conversions private and scalar-valued:
`traceFib_diag` and `lapTrace_diag` compare both trace notions through the same
centered smooth orthonormal frame; `trace_eq_lap` folds any supplied diagonal
scalar equality.  The spectral Hessian and connection corrections are named as
local fibre tensors inside `lapDiff_unit`, so Lean never elaborates a private
statement containing the whole nested spectral Hom expression.  `lift_unit`
normalizes the canonical rank-zero lift.  No
global frame, whole-Hom equality, synonymous assumption, or
`HasLocallyConstantChartAt` is introduced.  A proposed
`covGrad2_diag_sub` wrapper was deliberately not added because it would only
duplicate `hess_sub_conn`.

Low-layer and rank-zero realization focused and targeted verification pass.
The first consumer check exposed whole nested tensor statements timing out at
`isDefEq`/`whnf`; replacing them by `trace_eq_lap` plus local typed aliases
removed that performance path, and the consumer focused check now passes.

Honest accounting: `lapDiffCore_eq_cc` is verified (100% at theorem level), and
its dedicated machinery is 100% for this finite-core realization boundary.
`scalar_crit_tame` and `scalar_gal_exists` are source-written but remain 0% at
theorem level pending Lean verification.  The Galerkin limit and second-order
bootstrap are 0%.  Perelman no-local-collapsing and `ham3_noncollapse` remain
0%; their dedicated analytic machinery is about 43%, and whole HCG machinery
is about 54%.

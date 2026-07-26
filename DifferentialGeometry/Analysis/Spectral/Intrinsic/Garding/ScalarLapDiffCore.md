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

## 2026-07-16 arbitrary smooth scalar bridge

`scalarLapDiff_eq` is now proved for every smooth compactly supported
rank-zero tensor `U`, not only a finite spectral representative.  It identifies
the scalar readout of `scalarLapDiffCc q h U` pointwise with

```text
Δ_h (scalar0 U) - Δ_q (scalar0 U).
```

The proof stays in the fully applied scalar normal form.  Two private helpers
read the first and diagonal second fixed-background covariant jets of arbitrary
`U` as `duSec (scalar0 U)` and `hessianSec (scalar0 U)`.  They use the existing
rank-zero identity `TensorRSField.lift_scalar0`, then the existing
`tensorRSCovariantDerivative_zeroS_unit_eval`, `secondRS_scalar`, and
`lap_sub_conn` producers.  Traces are compared only after evaluation on the
centered smooth orthonormal frame.  No whole-Hom equality, global frame,
consumer assumption, or `HasLocallyConstantChartAt` is introduced.

The former finite-core helper `lapDiff_unit` now delegates its geometric
content to `scalarLapDiff_eq`; it retains only the genuine finite-core
realization conversion.  Focused verification passes.  The first check was
temporarily blocked by a missing upstream `RankZeroRealization` object file;
the narrow upstream refresh succeeded, and this was not a proof obstruction.

Honest accounting: `scalarLapDiff_eq` is 100% at theorem level and its dedicated
arbitrary-smooth realization bridge is 100%.  The eventual Galerkin
heat-potential endpoint remains unstated/unproved (0%); this closes one genuine
geometric producer but does not by itself prove passage of the Galerkin PDE to
the limit.  Perelman noncollapsing remains 0% at endpoint-theorem level; its
dedicated machinery is approximately 95% through the current heat-potential
lane, while whole HCG machinery remains approximately 59%.

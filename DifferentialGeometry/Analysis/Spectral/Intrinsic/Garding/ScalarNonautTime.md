# ScalarNonautTime

## Purpose

This module factors the completed scalar Laplacian difference through the
fixed-background iterated covariant derivatives and the generic completed
coefficient action. It then proves time regularity only after applying the
operator to a fixed Sobolev input, avoiding whole-CLM equality and topology
normalization.

## Verified state

`lapDiffHs_decomp` is implemented and focused verification passes without
`sorry`. On one common backward slab and for every natural Sobolev order it
identifies the genuine completed Laplacian difference with

```text
appHs scalarTraceCoeff (iterCovGradHs 2 U)
  - appHs connTraceCoeff (iterCovGradHs 1 (inclusion U)).
```

The dense-extension proof is fully applied on smooth tensors. In particular,
it does not compare whole reducible Hom objects.

`lapDiffHs_path_cd` is implemented and focused verification passes without
warnings or `sorry`. It combines `scalarTrace_joint`,
`connTrace_joint`, `appHs_path_cd`, and the backward affine time map to state
that every fixed `H^(m+2)` input has a `C∞` `H^m` Laplacian-difference path on
the same slab.

The earlier unknown-constant diagnostic was confirmed to be stale-import
fallout. After refreshing `ScalarFluxJetBound`, the unchanged scalar theorem
checked successfully. No mathematical or API obstruction remained.

## Resume point

1. Import the refreshed scalar path producer only in its Galerkin consumer.
2. Normalize `galLimExt_deriv` to the explicit all-scale velocity, then prove
   the dynamic-input completed-action rule needed for Banach ODE induction.

No consult is needed at this point. The scalar fixed-input route is closed; the
next genuine frontier is the dynamic-input Galerkin ODE step.

## Honest accounting

- original finite-support `A2` estimate: **100%**;
- all-scale completed `A2` bound and convergence: **100%**;
- completed iterated covariant derivative: **100%**;
- generic fixed-input coefficient derivative and `C∞` path: **100%**;
- scalar loss-two decomposition: **100%**, focused-green;
- scalar fixed-input `C∞` path theorem: **100%**, focused-green;
- `galLimExt_smooth`: theorem **0%**; dedicated machinery approximately
  **63%**;
- compact-interior Galerkin jet mass: theorem **0%**;
- classical conjugate-heat reconstruction: **0%**;
- Perelman noncollapsing endpoint theorem: **0%**;
- broader HCG machinery: approximately **57%**, with endpoint theorems still
  **0%**.

## 2026-07-16 dynamic-input completion

`lapDiffHs_dyn_fin` and `lapDiffHs_dyn_cd` now preserve finite-order and
`C^infinity` time regularity for a moving `H^(m+2)` input on every smaller
backward interval `Ioo 0 a` inside the common coefficient slab. They combine
the loss-two decomposition with the reflected coefficient producers and the
generic dynamic `appHs` rule.

Focused verification and the targeted export refresh are green. Both theorems
are **100%**. Their immediate consumer `galLimExt_smooth` is also proved, so
the live frontier is no longer a dynamic-action rule: it is
`galLim_jet_mass`, followed by rank-zero joint reconstruction.

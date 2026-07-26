# MetricDiffJoint

## 2026-07-19 source-only state

This file publicizes the fixed-background metric-difference facts needed by
the reverse-realization uniqueness route.  It is deliberately below the
Ricci--DeTurck strong-pair assembly layer.

Current producers in `MetricDiffJoint.lean`:

- `metricDiff_raw`: the unsymmetrized tensor extracted from
  `metricDifferenceCcTensor q h` evaluates to `h.inner - q.inner`.
- `metricDiff_unit`: the same identity in the `unitModel` component idiom used
  by the spectral strong-solution bridge.
- `metricDiff_symm`: a metric-difference tensor is already symmetric, before
  applying `ccTensorBilinSymm`.
- `metricDiff_symVal`: its symmetrization is exactly `h.inner - q.inner`.
- `realize_metricDiff`: realizing this tensor about `q` recovers `h` exactly.
- `metricDiff_joint`: a `MetricFamilySmoothOn` family gives a jointly smooth
  fixed-background metric-difference path on `D.regular`.
- `metricDiff_shift`: the same joint smoothness after translating time by a
  fixed interior restart time, provided the translated open set remains in
  `D.regular`.

The joint-smoothness proof is the generic version of the formerly private
argument in `Garding/ScalarFluxJetBound.lean`; it uses the live
`MetricFamilySmoothOn.pairSmoothAt` API and the canonical parametric tensor
section criterion.

Verification status: **source-only / not yet Lean-checked**.  A named shared
build was active while this file was written, so no competing focused check
was started.  No `sorry`, `admit`, axiom, opaque placeholder, or replacement
hypothesis was introduced.

Scope warning: `metricDiff_shift` is an **interior regular-time** producer.  It
does not assert joint smoothness at an original flow edge where only `C0`
control is known, and it is not an endpoint-startup uniqueness theorem.

Endpoint accounting: `ricci_flow_forward_unique` remains **0%** until its exact
public theorem is proved and Lean-verified.  These lemmas are producer
machinery only.

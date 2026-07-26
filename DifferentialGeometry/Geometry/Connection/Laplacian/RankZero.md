# Rank-zero connection-Laplacian bridge

## Goal

Provide the honest scalar bridge needed by conjugate heat: the mixed-tensor
connection Laplacian on the canonical rank-zero image of a scalar field agrees
with the invariant scalar Laplacian.  This replaces the misleading old wrapper
whose existential scalar was independent of its raw mixed tensor.

## Status (2026-07-10)

The source is `sorry`-free and passed focused and targeted-module verification.
The rank-zero lane is complete:

- `nablaRS_toRS0` proves that the induced mixed-tensor connection preserves the
  canonical rank-zero embedding.
- `rawLap_toRS0` proves second-order frame-trace compatibility.  Its original
  unverified proof was repaired by normalizing only each summand after
  `ContinuousLinearMap.sum_apply`; no whole-sum mixed-Hom `change` remains.
- `rawLap_scalar` proves the final object-level specialization: the raw mixed
  connection Laplacian of `fromScalarField f` is exactly `toRS0` of the
  canonical rank-zero tensor representing
  `laplacian (LeviCivita g) g f`.
- `secondRS_scalar` exposes the cheaper pre-trace producer needed downstream:
  the explicit second covariant-derivative difference of a canonical scalar
  lift is `toRS0` of its diagonal Hessian.  Its internal
  `cov0_diag_hess` lemma remains private, so no private field construction
  leaks into the public API.

The final theorem deliberately targets the invariant `laplacian` rather than
the `Delta_g` smooth wrapper.  This avoids adding the independent
`[I.Boundaryless]` model assumption.  The proof uses the canonical Hessian
section and `scalarLap_smooth`, then evaluates its intrinsic metric trace in the
smooth orthonormal frame.  It adds no consumer realization hypothesis and does
not use `HasLocallyConstantChartAt` or unfold the mixed-tensor Hom
representation.

Focused and targeted-module verification pass for the new producer.  The proof
stays in the connection layer and does not import the curvature-layer
`tensorSecondCovDeriv`; that later definition unfolds to this explicit normal
form in its own consumer layer.

## Honest progress

- rank-zero smooth-field embedding producer: 100%;
- first-order rank-zero connection compatibility: 100%;
- second-order rank-zero frame-trace compatibility: 100%;
- scalar connection-Laplacian realization `rawLap_scalar`: 100%;
- dedicated rank-zero scalar machinery: 100%;
- the actual `A2(s)` operator theorem: not stated, 0%; its dedicated geometric
  realization machinery is now roughly 50%;
- conjugate-heat existence theorem: 0%, with dedicated analytic machinery
  roughly 25%;
- Perelman no-local-collapsing and `ham3_noncollapse`: 0%, with current
  entropy/conjugate-heat machinery roughly 20%;
- whole HCG compactness machinery: roughly 45%, while its endpoint theorems
  remain 0%.

## Next consumer

The next layer should use `rawLap_scalar` to identify the rank-zero spectral
smooth representative with the actual invariant scalar Laplacian, then prove
the fixed-metric graph estimate.  Do not reintroduce a scalar realization
assumption at the consumer.

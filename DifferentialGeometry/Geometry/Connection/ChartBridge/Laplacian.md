# Laplacian

## 2026-07-23: local Hessian-trace adapter

### Canonical placement

`ChartBridge/Laplacian.lean` is the lowest existing bridge layer that already
owns the scalar connection-Laplacian comparison and imports the chart Hessian.
Adding the object adapter here does not create a cycle with
`Geometry/Operator/RoughLaplacian.lean`.

### Added API

- `hessTensorAt` packages `hessFun g f x` as an intrinsic covariant
  two-tensor.
- `hessTensorAt_apply` is its evaluation rule on `vec2 v w`.
- `lap_eq_hess_on` identifies the realized Levi-Civita scalar Laplacian with
  the intrinsic metric trace of `hessTensorAt` at a point where `f` is smooth
  on an open neighborhood.

The proof reuses the already checked local-germ theorem
`hessFun_eq_cov_local`, so it does not introduce a global smooth extension as
an input.  Both sides are expanded in the same coordinate basis using the
canonical inverse metric.

### Verification

Focused verification passed, and the exact module artifact is current.  The
new declarations have no placeholders.  The check reports only
unused-section-variable warnings; attempts to omit those instances were not
definitionally compatible with the declaration bodies, so no file-wide linter
suppression was added.

### Project accounting

- This Layer-D adapter theorem: 100%.
- `branchLap_eq_mean`: theorem-level 0%.
- `radialLap_eq_mean`: theorem-level 0%.
- This work does not change the independent HCG endpoint accounting:
  unconditional `compactnessSol` remains theorem-level 0%.

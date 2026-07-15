# Intrinsic Levi-Civita Hessian norm

## Goal

Identify the intrinsic squared norm of the canonical Levi-Civita Hessian with
the inverse-Gram chart Frobenius square used by the scalar graph estimate.

## 2026-07-10

- Added `leviHessSec`, a named canonical Hessian section. Naming the section
  before putting it under `normSq0S` avoids normalization of the full bundled
  `hessianSec` constructor in theorem statements.
- Added scalar component bridges from `leviHessSec` to `abstractHessian`, then
  to `chartHessianTensor`.
- Added `hessSec_normSq`, proving the intrinsic norm identity by expanding in
  the point-centered chart basis and rewriting only fully applied scalar
  components.
- A direct statement containing the full `hessianSec` term timed out during
  `whnf`. Passing the whole generalized inverse-metric predicate into the old
  coordinate norm theorem also timed out through the bundle-topology diamond.
  The successful proof reconstructs the legacy inverse predicate entrywise
  from scalar matrix inverse identities.
- Focused verification and targeted module verification passed without local
  warnings. This producer is complete; the moving-Laplacian `A2` theorem is
  still unstated and unproved.

# BishopIntrinsic notes

## 2026-07-24 whole-tail intrinsic comparison

This module is the intrinsic replacement for the small chart-radius wrapper
`exists_radial_mean`.  The raw exponential is retained only as a germ at the
pole, where the already checked radial density lower bound initializes the
Riccati comparison.

The checked implementation consists of:

- `intrinsic_jacobi_at`, in `JacobiVariation.lean`, identifying the intrinsic
  Jacobi field at arbitrary time with the vector-slot intrinsic-exponential
  differential at the scaled launch vector;
- `intrJacobi_raw`, the eventual raw/intrinsic geodesic and Jacobi-field
  agreement used only at the pole;
- intrinsic time-rescaling for the radial velocity, endpoint Gauss
  orthogonality, and the differentiated orthogonality identity;
- all-time Jacobi regularity, zero Wronskian, and linear independence obtained
  from the supplied nonconjugacy interval;
- `exists_intrMean`, consuming nonconjugacy on `Ioo 0 b` with `1 < b` and the
  Ricci lower bound, with no long-tail raw radius;
- an explicit transverse-dimension-zero branch using the empty `Fin 0` family.

Focused and exact verification are green with no local diagnostics, and the
module contains no `sorry`, `admit`, or new axiom.  A direct axiom replay for
`exists_intrMean` reports only `propext`, `Classical.choice`, and `Quot.sound`.
Theorem-level `exists_intrMean` and its dedicated whole-tail machinery are both
100%.  This closes the intrinsic Bishop brick, roughly 20% of the fixed-metric
Calabi-support producer.  The separate `calabiDist_support`, the evolving-
distance barrier theorem, and the unconditional HCG endpoint remain theorem-
level 0%.

The exact-build linter cleanup weakens the private orthogonality helper to an
arbitrary index type and removes unused finite/decidable index instances from
the intrinsic-Jacobi independence helper.  Public statements and the comparison
argument are unchanged; focused verification remains green.

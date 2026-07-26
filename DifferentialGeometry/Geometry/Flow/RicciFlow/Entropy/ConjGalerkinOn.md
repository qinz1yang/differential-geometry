# Exact-interval Galerkin reconstruction

## 2026-07-19 source assembly

This module removes the independent lifespan choices from the classical
Galerkin reconstruction.  Starting from a caller-supplied regular reflected
interval and the genuine finite-core Laplacian identity, it constructs the
velocity lifts, coefficient derivatives, time jets, joint interior smoothness,
and pointwise conjugate-heat equation on that same interval.

`gallim_on` packages the result as `IsHeatPotOn` on the exact closed interval.
`gallim_pos_on` then applies the existing scalar maximum principle using the
compact-slab bound for `conjCoeff`; it does not shorten the interval.  The
proofs keep dependent tensor identities inside a fixed terminal spectral space
and reduce the moving equation to scalar evaluations before rewriting.

The source contains no local `sorry`.  Focused verification is pending the
active upstream spectral object refresh, so these declarations remain
theorem-level **0%** with approximately **95%** dedicated source until the file
check passes.  Exact W comparison, finite Good-set propagation,
`NoLocalCollapsing`, and `ham3_noncollapse` remain separate theorem-level
frontiers at **0%**.

## 2026-07-23 post-merge check

The file now opens the exact namespaces needed for quasi-linear, metric
realization, divergence, and tensor scalar notation.  Focused verification and
the module artifact refresh both passed.

## 2026-07-23 scalar spectral cutover

The three exact-interval rank-zero tail inputs now use
`IntrinsicSpectral.scalar_eigen_tail`.  `ScalarWeyl` is imported directly
rather than relying on a transitive import through `ConjGalerkinClassical`.
Focused verification passes, and the file has no remaining reference to the
deferred generic Weyl theorem.
This supersedes the older pending-refresh and downstream-frontier paragraph:
the exact-interval scalar tail consumers are theorem-level **100%** with
dedicated machinery **100%**, and the later Perelman/Hamilton notes record
`NoLocalCollapsing` and `ham3_noncollapse` as closed.

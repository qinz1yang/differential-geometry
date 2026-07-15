# Rank-zero spectral realization

## Goal

For a finite-support `v : tensorHs g 0 0 2`, identify its smooth mixed-tensor
representative with a genuine smooth scalar, identify its rough connection
Laplacian pointwise with the invariant scalar Laplacian, and identify the same
rough Laplacian in fixed-metric `L²` with `tensorScaleLaplacian 0 v`.

## Status

The source contains the scalar readout `reprScalar0`, its canonical-lift
roundtrip `repr_eq_lift`, the pointwise actual-scalar theorem
`rawLap_repr_scalar`, and the spectral `L²` theorem `rawLap_repr_toL2`.  The
fixed-order operator `scalarScaleLap : H² →L[ℝ] H⁰` removes the otherwise
awkward `0 + 2` exponent from the public rank-zero interface.

`rawLap_repr_norm` proves the support-independent fixed-metric estimate
`‖Δu_v‖₂ ≤ ‖v‖_{H²}`.  `grad_repr_norm` proves the matching first-order
estimate `‖∇u_v‖₂ ≤ ‖v‖_{H²}` by the fixed-metric Green identity.  Both
constants are independent of the finite spectral support.

The pointwise readout API now also contains `grad_repr_apply` and
`grad2_repr_diag`.  They identify the fully applied first covariant gradient
with `duSec` and the diagonal second covariant gradient with `hessianSec`.
The second bridge factors through the connection-layer `secondRS_scalar` and
the existing two-leftmost-slot covariant-gradient theorem; it never compares a
whole dependent Hom-bundle model.

Focused verification and the targeted object refresh pass for the new
readouts.  The downstream scalar-energy readout
and Hessian graph estimate live in `ScalarHessBound.lean`; they are not folded
into this rank-zero realization layer.

The current realization necessarily imports both `FaithfulH1Embedding` and the
smooth spectral representative API.  Each reaches the large eigenvector
regularity tree through an independent dependency chain, so deleting either
direct import is not a sound local performance fix.  Reducing that build cost
would require an upstream module split rather than import pruning here.

No theorem adds a consumer realization assumption or uses
`HasLocallyConstantChartAt`.

Honest accounting: the two new realization theorems are proved and focused
verified (100% at theorem level).  `lapDiffCore_eq_cc` remains 0% until its
consumer file verifies; its dedicated realization machinery is about 95%.
The conjugate-heat endpoint and Perelman noncollapsing endpoints remain 0%;
their dedicated analytic machinery is about 43%, and whole HCG machinery is
about 54%.

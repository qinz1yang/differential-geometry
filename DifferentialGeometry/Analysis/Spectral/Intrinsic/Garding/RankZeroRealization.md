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

`scalarLapHs_core` is the canonical smooth-input bridge at every spectral base
order `m`: applying `tensorScaleLaplacian m` to
`ccTensorToHs g 0 (m + 2) S` equals `ccTensorToHs g 0 m` of the geometric
`rawTensorConnLapSmooth` of `S`.  Its proof is coefficient extensionality plus
`rawLap_coeff`; it introduces no realization hypothesis.  The general order is
needed by the all-scale Galerkin velocity, while `m = 0` recovers the original
fixed-order endpoint.  Focused verification passes.

`rawLap_repr_norm` proves the support-independent fixed-metric estimate
`‖Δu_v‖₂ ≤ ‖v‖_{H²}`.  `grad_repr_norm` proves the matching first-order
estimate `‖∇u_v‖₂ ≤ ‖v‖_{H²}` by the fixed-metric Green identity.  Both
constants are independent of the finite spectral support.

`rawLap_cc_scalar` removes the finite-support restriction at the smooth-core
layer: for every smooth rank-zero tensor, the fully applied scalar readout of
`rawTensorConnLapSmooth` is `Δ_g` of its scalar readout.  It factors through
the canonical `lift_scalar0` roundtrip, `rawLap_scalar`, and the existing
`laplacian_levi_eq` operator bridge; it does not compare whole bundle models.
Focused verification and the targeted object refresh pass.

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

Honest accounting: `scalarLapHs_core` is proved and focused verified (100% at
theorem level), and this all-order fixed-metric smooth-input bridge is complete
(100%).
The real heat-potential endpoint remains unstated/unproved (0%); its dedicated
machinery is about 98%, with the pointwise PDE assembly still remaining.  The
initial scalar realization is already complete.  The Perelman noncollapsing
endpoint remains 0%; whole HCG
machinery is conservatively about 59%.

# LieCorr0Field

## Role

This module is the public coefficient-layer home of the zeroth-order field
created when the raw DeTurck Lie chart Hessian is rewritten using the fixed
background covariant Hessian.

## Verified state

`lieCorr0Field`, its fibrewise readout `lieCorr0Field_apply`, and the exact
component identity `lie0_order0_eq` are public. The last theorem combines the
complete Ricci-DeTurck zeroth-order reanchoring calculation with the extracted
`LieCorr0NormalForm` master identity. All generated component and fibre
constructions remain private. The module has no Sobolev-ball or
high-regularity hypothesis, and focused verification passes without local
warnings or `sorry`s.

The center-chart arm readouts now come from the small public
`LieCorr0Readout` module. Existing canonical center-evaluation, Gram symmetry,
Gram-inverse contraction, and rank-zero chart-frame APIs replace duplicate
private proofs from the legacy file.

## 2026-07-16 downstream completion

The exact three-arm residual and its concrete path-integral packaging now live
in `RHSThreeArmCancel` and `RHSPathIntegral`. Thus the frontier formerly listed
here is closed. The remaining work is the uniform C0/C1 coefficient estimate
and final Sobolev assembly.

The mixed `H3 -> H1` remainder theorem remains unstated and theorem-level 0%.
Its dedicated machinery is approximately 78% complete; this is infrastructure
coverage, not theorem completion.

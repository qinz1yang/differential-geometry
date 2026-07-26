# FourierL2Bridge

## Proved producer

`fourier_toLp_two` identifies the classical Fourier transform of an integrable
scalar function with Mathlib's Plancherel `L²` Fourier transform, provided both
the function and its classical transform belong to `L²`.

The proof embeds both `L²` classes into tempered distributions, uses the
injectivity of that embedding and `Lp.fourier_toTemperedDistribution_eq`, then
proves the remaining classical-transform pairing identity with Mathlib's
existing Fubini theorem
`VectorFourier.integral_fourierIntegral_smul_eq_flip`.

## Scope decision

No relaxed convolution Fourier theorem was added.  It is not needed to prove
this compatibility bridge, and any later convolution statement should be
introduced only at the damped-kernel consumer where its exact hypotheses are
known.

This file is machinery only.  It does not prove either endpoint theorem:

- `ricci_flow_unif_existence`: 0% at the exact theorem level.
- `ricci_flow_forward_unique`: 0% at the exact theorem level.

## Verification

The focused lock-aware check of `FourierL2Bridge.lean` passed with no local
warnings.  The producer contains no `sorry`, `admit`, axiom, or opaque
declaration.

# KochLammProduct

## Purpose

This file is the nonlinear source producer for the exact Koch--Lamm carrier.
It uses the genuine Hölder pairs `L² × L² → L¹` and
`L^(n+4) × L^(n+4) → L^((n+4)/2)`.

## Source content

- `klL1_eq_L2_sq` and `klLq_eq_Lp_sq` prove the two exact parabolic scale
  cancellations.
- `klP_holder` supplies the finite supercritical Hölder triple.
- `eLpNorm_bilin_le` proves Hölder control for a space-dependent uniformly
  bounded bilinear coefficient.
- `klBilin_source` packages both arms as a genuine `KLSource0`.
- `klPathBilin_source` specializes this to the gradient fields of two
  `KLPath`s.

No weighted pointwise gradient bound, hidden heat-map hypothesis, or horizon
smallness is used.

## Verification state

Focused verification passes with no local warning, including the path
specialization.  The complete `Y_T → X_T` heat-potential theorem and the
geometric HMF realization remain; `ricci_flow_forward_unique` therefore
remains 0%.

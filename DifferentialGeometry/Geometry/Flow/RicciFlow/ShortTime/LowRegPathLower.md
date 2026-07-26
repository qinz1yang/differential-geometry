# LowRegPathLower

## Role

This module packages the dimension-three Sobolev estimate for lower
Ricci--DeTurck path arms after an exact C0/C1 coefficient realization has been
constructed.

## Current state

`lower_coeff_h1` proves that a C0 coefficient with a pointwise bound and one L2
covariant derivative, together with a C1 coefficient controlled through two L2
covariant derivatives, acts from spectral H2 to spectral H1.  The theorem is
independent of any high metric Sobolev order.

Focused verification passed without local `sorry`s.  This analytic packaging
is a proved conditional consumer, but it is not the viable unconditional
interface for the candidate Sobolev contraction ball.  The 2026-07-18
normal-form ruling in `LowRegRemainderH1.md` shows that the requested pointwise
zero-order bound fails on an `H3`-bounded, `H2`-small ball.  The replacement
frontier is `lower_jet_h1`: integral `H1` control of the zero-order coefficient
and `H2` control of the first-order coefficient, assembled through an
`H1 x H2 -> H1` tensor-product estimate.  The unconditional mixed theorem and
uniform-existence endpoint remain 0%.

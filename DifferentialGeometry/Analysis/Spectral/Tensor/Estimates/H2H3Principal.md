# H2H3Principal

## Purpose

This module isolates the low-regularity principal product estimate used by the
three-dimensional Ricci--DeTurck remainder.  Mixed tensor coefficients remain
in pointwise fibre-norm form, while the evolving covariant tensor is measured
in the intrinsic spectral scale used by the parabolic solver.

## Current state

`appCc_h3_h1` is the stronger-assumption helper.  It assumes pointwise bounds for a mixed
coefficient and its first covariant derivative and controls the spectral `H1`
norm of its action on `nabla^2 U` by the spectral `H3` norm of `U`.

The actual low-regularity theorem is `appCc_h2_h3_h1`.  Its derivative arm
uses `appCc_grad_l2`, a genuine `L4 x L4` two-arm estimate, so the coefficient
needs only a pointwise order-zero bound and an order-zero-through-two `L2` jet
square-sum.  This avoids the false route that tried to obtain a pointwise first
coefficient derivative from three-dimensional `H2` data.  Focused verification
passes without local sorries.

`appCc_h2_cov_h1` applies the same `L4 x L4` cell one derivative lower. An
`H2` mixed coefficient acting on the first covariant derivative of an `H2`
field is controlled in spectral `H1`. This is the product estimate required by
the order-one path arm in the low-regularity Ricci--DeTurck remainder.

`appCc_h2_h2_h1` handles the generic zeroth-order product: an `H2` mixed
coefficient acting on an `H2` covariant tensor is controlled in spectral
`H1`.  Its differentiated product uses the pointwise `H2` bound on the tensor
factor and the `L2` first derivative of the coefficient, so it does not require
a false pointwise derivative bound.  It is now a compatibility wrapper around
the sharper `appCc_c1_h2_h1`, which assumes only a pointwise zeroth-order bound
and an `L2` bound for the first coefficient derivative.  This is the actual
regularity available for the zero-order DeTurck path coefficient from a `C3`
metric jet.  Focused verification passes.

The first wrapper attempt relied on an unavailable `add_self` rewrite and did
not normalize multiplication associativity.  An explicit `calc` followed by
`ring` is stable and keeps the constant-factor conversion visible.

## Frontier

The next geometric producer must supply the separated pointwise and first-jet
coefficient bounds for the zero-order DeTurck path arm, and the corresponding
`H2` coefficient envelope for the first-order arm.  The non-pure second-order
arm must first be folded through the covariant-derivative commutator into a
zero-order curvature coefficient.  These estimates do not themselves prove
the mixed remainder estimate or a Ricci--DeTurck existence theorem.

# RHSPathOrderSplit

## Role

This module is the public realized-family entry point for the low-regularity
Ricci--DeTurck path decomposition.  It keeps the Ricci and DeTurck Lie slopes
together until their second-order terms have been combined.

## Current state

- `rhsPathSlope` is the exact scalar slope of the complete chart RHS.
- `hasDerivAt_rhsPath` and `deriv_rhsPath` derive it directly from the
  realized-family Ricci and Lie derivative APIs.
- `rhsTopTerm` is the complete Ricci--DeTurck second-order coefficient applied
  to the fixed-background covariant Hessian of `T - T'`.
- `rhsLowTerm` contains only the Ricci order-zero/order-one arms, the raw Lie
  order-zero/order-one arms, and the connection tail created by reanchoring.
- `rhsSlope_eq_split` proves the exact full principal-part cancellation before
  any norm estimate, and `rhsSum_sub_eq_int` supplies the endpoint FTC bridge.
- The module does not use `ChartMetricPerturbation` and introduces no
  high-regularity hypothesis.

The exact scalar decomposition is complete.  The order-zero correction field
created by changing chart Hessians to the fixed-background covariant Hessian
is now public in `LieCorr0Field.lean`, with no high-order hypothesis.  The
remaining frontier has two coupled parts: expose the exact component readout
that identifies the raw lower scalar arm with the public C0/C1 fields, and
prove the q=0,1 coefficient bounds from a uniform C3 metric-jet envelope.  The
old oversized assembly contains the readout only behind a large private
normal-form chain.

## Failed route

The attempted adapter from `realizedFam` to `IsMetricPerturbationFamily` was
invalid.  `ChartMetricPerturbation` requires each component function to be
globally smooth on the whole model space, while a totalized realized chart
Gram field is only known smooth on the chart target.  The invalid adapter was
removed rather than hidden behind an extra assumption.

Focused verification passed without local `sorry`s.  The mixed H3-to-H1 tame
endpoint remains unstated and therefore 0% complete; its dedicated machinery
is about 88% complete.

## 2026-07-16 downstream closure

The component readout and public C0/C1 fields are now completed in
`LieCorr0Readout`, `LieCorr0Field`, `LieThreeArmCancel`, and
`RHSThreeArmCancel`. `RHSPathIntegral.rhsArm_sub_eq_paths` consumes this module's
FTC bridge and proves the exact tensor-valued integrated three-arm identity.
Thus the exact-decomposition frontier recorded above is closed.

The remaining mathematical frontier is not another path split: it is uniform
low-regularity control of the concrete C0/C1 path coefficients and the final
Sobolev assembly. The mixed theorem is still unstated (0%); its dedicated
machinery is conservatively about 78%, superseding the earlier 88% estimate.

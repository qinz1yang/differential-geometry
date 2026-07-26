# KochLammCarl

## Purpose

This file identifies the exact local `L²` arm of the Koch--Lamm carrier with
the gradient-Carleson energy used by the existing nonlinear product layer.
The Carleson constant is the square of the `NNReal` Koch--Lamm radius; no
pointwise gradient estimate is introduced.

## Mathematical content

- `eLpNorm_two_sq` identifies the square of the `L²` seminorm with the
  lintegral of the squared norm.
- `klL2_inv_sq` proves the exact scale cancellation
  `(R^(-n/2))^(-2) = R^n`.
- `kl1_to_gradCarl` converts a `KLSource1` flux into `GradCarl`.
- `klPath_gradCarl` converts the gradient arm of a `KLPath` into `GradCarl`.

## Verification state

Focused verification passes with no local warning.  This closes the exact
local-energy conversion, but not any heat-potential estimate.  The next
analytic frontier is the late `L^(n+4)` / `L^((n+4)/2)` product and heat
mapping layer.  The endpoint `ricci_flow_forward_unique` remains 0%; this file
is supporting analytic machinery only.

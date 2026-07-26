# RHSFirstDerivativeUniform

## 2026-07-15 family-uniform first RHS jet

This file packages uniform metric equivalence and chart Gram bounds through
order three into a single bound for every first spatial chart derivative of
the Ricci--DeTurck right-hand side on active partition-of-unity supports.

Focused and targeted verification passed.  The proof uses one `Option`-indexed
family to include the fixed DeTurck background, then combines uniform
inverse-Gram and Christoffel bounds through second derivatives with the
pointwise estimates in `RHSFirstDerivativeBound`.  No background order-zero
Gram bound is required.

The first-RHS-jet theorem `chartRHSD_pou_bnd` is now proved (100%).  This closes
the coefficient-level C3-to-C1 input, but not the Sobolev mixed tame estimate
or a solution theorem.  Uniform low-regularity existence remains 0%, with
dedicated E1 machinery about 34--35%; whole-HCG machinery remains about 57%
and all HCG endpoint theorems remain 0%.

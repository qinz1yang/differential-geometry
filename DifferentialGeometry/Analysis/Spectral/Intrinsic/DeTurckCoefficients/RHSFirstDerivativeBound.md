# RHSFirstDerivativeBound

## 2026-07-15 low-regularity coefficient route

This module is the pointwise algebra layer for one spatial derivative of the
Ricci--DeTurck right-hand side.  It now proves the exact first derivatives of
the chart Riemann and Ricci coefficients, the exact second derivative of the
DeTurck vector field, the six-term first derivative of the DeTurck Lie term,
and the combined first-RHS derivative formula.  Each stage has an explicit
finite-sum absolute bound.

Focused verification passed with no warnings and no new axioms or sorries.
The resulting RHS bound depends only on uniform inverse-Gram and Christoffel
bounds through second derivatives together with chart Gram bounds through
order three.  The family-uniform first-RHS-jet theorem is stated separately
and remains unverified, so that endpoint is still 0%; this pointwise layer is
complete and its dedicated family-assembly machinery is approximately 90%.
Uniform low-regularity existence remains 0%, with dedicated E1 machinery about
32--33%; whole-HCG machinery remains about 57% and all HCG endpoint theorems
remain 0%.

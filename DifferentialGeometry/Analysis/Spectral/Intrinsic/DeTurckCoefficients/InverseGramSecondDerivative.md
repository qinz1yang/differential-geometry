# InverseGramSecondDerivative

## 2026-07-15 low-regularity coefficient route

This module is the first new producer on the C3-controlled spatial-derivative
route.  It reuses the exact second inverse-matrix identity
`partialDeriv2_chartInvGramOnE_eq` from `Geometry/Operator/HessianTrace`, bounds
its finite sums by inverse-Gram and first/second Gram bounds, and packages one
POU-family constant from the existing uniform ellipticity input.  No duplicate
inverse-matrix identity remains in this file.

The mathematical role is narrow: it is a prerequisite for a uniform
second-Christoffel-derivative bound and hence for a first spatial derivative
bound on the Ricci--DeTurck RHS.  It does not supply the sharp three-dimensional
`H^3 -> H^1` mixed tame estimate or a low-regularity solver.

Focused verification passed without warnings or new axioms.  This local module
is complete.  The first-RHS-jet theorem is still unstated and therefore 0%; its
dedicated coefficient machinery is approximately 60%.  The uniform
low-regularity existence theorem remains 0%, with dedicated E1 machinery about
31--32%; whole-HCG machinery remains about 57%, while its endpoint theorems
remain 0%.

# ChristoffelSecondDerivative

## 2026-07-15 low-regularity coefficient route

This module is the second C3-controlled producer toward a family-uniform first
spatial derivative bound for the Ricci--DeTurck RHS.  It adds the twice
differentiated metric bracket, the second chart-partial Christoffel formula, a
pointwise quantitative estimate, and a POU-family wrapper consuming Gram bounds
through order three.

The route reuses `partialDeriv_chartChristoffel_eq`, `invGramD_abs_le`, and the
new `invGramD2_abs_le`; no higher-order compactness choice is used.  Focused
verification passed without warnings or new axioms.  The local producer is
complete.

The first-RHS-jet theorem remains unstated and therefore 0%.  Its dedicated
coefficient machinery is approximately 70% after this module.
The uniform low-regularity existence theorem remains 0%, with dedicated E1
machinery about 31--32%; whole-HCG machinery remains about 57%, while its
endpoint theorems remain 0%.

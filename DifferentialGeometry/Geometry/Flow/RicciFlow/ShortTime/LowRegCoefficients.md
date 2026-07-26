# LowRegCoefficients

## 2026-07-14 solver-facing coefficient package

`LowRegCoeff` stores one two-sided inverse-Gram ellipticity envelope, chart
Gram bounds through order three, a positive absolute Ricci--DeTurck RHS bound,
one positive bound for every first spatial chart derivative of the RHS, and a
Lipschitz constant controlling the RHS value by the metric `2`-jet difference.
`IsLowRegCoeff` records that these constants work for all members of a metric
family on every active partition-of-unity chart support.

`exists_low_reg_coeff` starts from exactly the current E1 family inputs:
pointwise `Lambda`-equivalence to a fixed background and uniform
`MetricCovDerivOrderBoundOn` hypotheses through order three.  Fixed-background
bounds are obtained once by compactness, adjoined to the moving family, and
then the intrinsic-to-chart, ellipticity, Ricci, and Lie producers are
assembled into the package.

The added `rhsBound` closes the forcing-size input needed to keep a contraction
map inside its ball; `rhsLip` alone did not imply such a bound.  The new
`rhsD1Bound` closes the family-uniform first-RHS-jet input from exactly the
same C3 hypotheses.  This file still deliberately does not state a
local-existence theorem.  For the Hamilton three-dimensional route, the
smallest analytic frontier is now the Sobolev realization of these component
bounds as a mixed `H^3 -> H^1` tame estimate at maximal-regularity order
`a = 1`.  It is followed by the actual solver and same-interval
regularization.  Until these exist, both low-regularity Ricci--DeTurck
existence and `ricci_flow_unif_existence` remain theorem-level 0%.

Focused verification passed.  The updated axiom probe for
`chartRHSD_pou_bnd` and `exists_low_reg_coeff` is clean: both depend only on
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

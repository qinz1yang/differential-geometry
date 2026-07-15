# LowRegCoefficients

## 2026-07-14 solver-facing coefficient package

`LowRegCoeff` stores one two-sided inverse-Gram ellipticity envelope, chart
Gram bounds through order three, a positive absolute Ricci--DeTurck RHS bound,
and a Lipschitz constant controlling the RHS value by the metric `2`-jet
difference.  It does not bound spatial derivatives of the RHS.
`IsLowRegCoeff` records that these constants work for all members of a metric
family on every active partition-of-unity chart support.

`exists_low_reg_coeff` starts from exactly the current E1 family inputs:
pointwise `Lambda`-equivalence to a fixed background and uniform
`MetricCovDerivOrderBoundOn` hypotheses through order three.  Fixed-background
bounds are obtained once by compactness, adjoined to the moving family, and
then the intrinsic-to-chart, ellipticity, Ricci, and Lie producers are
assembled into the package.

The added `rhsBound` closes the forcing-size input needed to keep a contraction
map inside its ball; `rhsLip` alone did not imply such a bound.  This file still
deliberately does not state a local-existence theorem.  For the Hamilton
three-dimensional route, the smallest analytic frontier is now a quantitative
first-RHS-jet and mixed tame estimate from metric-equivalent C3 data, realizing
the Ricci--DeTurck nonlinearity as `H^3 -> H^1` at maximal-regularity order
`a = 1`.  It is followed by same-interval regularization.  Until these exist,
both low-regularity Ricci--DeTurck existence and `ricci_flow_unif_existence`
remain theorem-level 0%.

Focused and targeted verification passed.  The axiom probe remains clean of
`sorryAx`.

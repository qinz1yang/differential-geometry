# LieSummandLipschitz

## 2026-07-14 family-uniform DeTurck Lie estimate

The file now contains absolute bounds for the DeTurck vector field and its
first coordinate derivative, a reusable algebraic estimate for the chart Lie
summand, and `chartLie_pou_lip`.  The latter gives one family-uniform
`2`-jet Lipschitz constant for the full Lie summand relative to a fixed
background metric, using chart Gram bounds through order two.

Focused and targeted verification passed.  Together with
`chartRicci_pou_lip` this closes the pointwise nonlinear RHS coefficient
estimate.  It does not construct a low-regularity solution or smoothing
interval.

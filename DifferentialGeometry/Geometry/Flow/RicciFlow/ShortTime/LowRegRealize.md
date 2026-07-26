# LowRegRealize

## 2026-07-19

Source implementation contains no `sorry`, `admit`, axiom, or replacement
hypothesis; focused verification is pending.

`lowreg_realize_h2` is the direct lower-order realization bridge: an `H2`
spectral tensor whose realized smooth perturbation has the required
pointwise operator bound produces a smooth metric.  `lowreg_realize` retains
the corresponding `H3` entry point.

The new `H2` form is the relevant one for a maximal-regularity solution,
because the state ball is controlled pointwise in time only in the lower
norm.  This file does not yet supply the concrete tame nonlinearity or the
uniform-family lifetime, so `ricci_flow_unif_existence` remains 0%.

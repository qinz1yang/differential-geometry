# RHSAbsoluteBound

## 2026-07-15 uniform forcing-size producer

`chartRicci_abs_le`, `chartLie_abs_le`, and `chartRHS_abs_le` give explicit
finite-sum absolute component bounds for the Ricci term, the DeTurck Lie term,
and their full RHS combination.  Unlike the earlier difference estimates,
these lemmas control the value at one metric and therefore supply the forcing
size needed for a fixed-point self-map estimate.

Focused and targeted verification passed.  The file introduces no `sorry`.

This is only the order-zero coefficient estimate.  The three-dimensional
`a = 1` maximal-regularity route still needs a quantitative first spatial jet
bound and the integrated mixed tame estimate `H^3 -> H^1`; the existing
all-order compact-chart API chooses constants separately for each metric pair
and is not uniform over the E1 family.

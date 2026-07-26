# RicciLinearizationConnDiffUniformBounds

## Low-regularity producer

`ricci_coeff_rfns_le` is the public no-high-order producer for pointwise fibre
norm bounds of the Ricci order-zero and order-one connection-difference
coefficients.  It assumes a fixed-background metric two-jet envelope and does
not pass through a supercritical Sobolev embedding.

Focused verification passed.  This closes the pointwise Ricci part only; the
L2 derivative windows and the DeTurck Lie C0/C1 coefficients remain separate
frontiers.

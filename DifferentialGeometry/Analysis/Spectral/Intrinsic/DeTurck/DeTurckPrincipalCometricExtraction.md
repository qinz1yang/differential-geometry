# DeTurckPrincipalCometricExtraction

## Purpose

This module identifies the difference between the moving and background
cometric principal parts and expresses its covariant jets through the
inverse-metric difference coefficient.

## 2026-07-15 state

`coeff_grad_rfns_le` removes the spurious undifferentiated term in the first
coefficient derivative because the background double-trace field is parallel.
`deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff` gives the
pointwise finite lower-jet envelope at every order.  The new
`coeff_jet_l2_sq` integrates that statement and controls each coefficient
`L2` jet square by the corresponding finite inverse-coefficient jet window.

Focused verification and the module build pass.  This is an exact projection
lemma, not the missing low-regularity inverse-metric estimate and not a
Ricci--DeTurck existence theorem.

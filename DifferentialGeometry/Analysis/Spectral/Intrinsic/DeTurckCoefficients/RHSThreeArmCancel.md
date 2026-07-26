# RHSThreeArmCancel

## Role

This module is the public, source-level Ricci--DeTurck cancellation boundary.
It combines the Ricci and Lie correction linearizations into exact order-zero,
order-one, and order-two coefficient arms before any Sobolev estimate.

## Verified state

`rhsLow0Coeff`, `rhsLow1Coeff`, their joint path smoothness theorems, and
`rhsLow_eq_arms` / `rhsSlope_eq_arms` are sorry-free. Focused verification and
the named module build pass. The top arm is the complete Ricci+DeTurck
coefficient, so the principal cancellation is expressed without a high-order
Sobolev-ball hypothesis.

The exact cancellation sublane is complete (100%). The mixed `H3 -> H1`
estimate remains unstated and theorem-level 0%; its dedicated machinery is
approximately 78% complete.

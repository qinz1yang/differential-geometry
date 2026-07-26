# LieThreeArmCancel

## Role

This module is the public cancellation layer for the realized DeTurck Lie
slope. It packages the complete center-chart slope as the sum of intrinsic
order-zero, order-one, and order-two coefficient arms.

## Verified state

`lieSlope_eq_arms` is proved without `sorry`, Sobolev-ball hypotheses, or
high-regularity assumptions. Focused verification passes. The proof reuses
`lie0_order0_eq`, `lieOne_cov_eq_raw`, and `lieTop_cov_eq_raw`; after
unfolding the named top tail, all connection correction terms cancel by a
single linear identity.

## Frontier

The Lie-side reanchoring is complete. The next producer identifies the lower
order-zero and order-one coefficient fields in the full Ricci-DeTurck slope,
combining this theorem with the existing Ricci linearization split. That
producer feeds `LowRegPathLower.lower_coeff_h1`. The mixed `H3 -> H1`
endpoint remains unstated and therefore 0%; its dedicated coefficient and
reanchoring machinery is approximately 97% complete.

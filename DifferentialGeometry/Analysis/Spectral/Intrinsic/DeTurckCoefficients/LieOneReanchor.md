# LieOneReanchor

## Role

This module is the public first-order reanchoring layer for the DeTurck Lie
slope. It converts the arm acting on the first background covariant derivative
of the metric difference into the raw center-chart first-derivative expression
plus the exact connection tail.

## Verified state

`lieOne_cov_eq_raw` is proved without `sorry`, Sobolev-ball hypotheses, or
high-regularity assumptions. Focused verification passes. The module stays
below the 3000-line limit; its long algebraic chain is a private extraction of
the settled legacy proof, while the first-jet readout is reused through the
public `lieU3_readout` theorem.

## Frontier

Together with `lie0_order0_eq` and `lieTop_cov_eq_raw`, this theorem supplies
the three exact identities whose connection tails cancel in the full
Ricci-DeTurck slope. The next theorem is that compact three-arm cancellation
identity, followed by the lower-path `H1` estimate. The mixed `H3 -> H1`
endpoint remains unstated and therefore 0%; its dedicated coefficient and
reanchoring machinery is approximately 95% complete.

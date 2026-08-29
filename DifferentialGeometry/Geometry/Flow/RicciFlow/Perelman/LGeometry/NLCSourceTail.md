# NLCSourceTail

## Role

This module isolates the large-source half of the good/bad decomposition used
in the reduced-volume-to-ball estimate for smooth noncollapsing.

## Route

`lRedJac_src_le` multiplies the checked pointwise inequality
`lRedJac_le_gauss` by the positive exact source density and identifies the
result with `lSrcGauss` using `lSrcGauss_eq`.

`lRedJac_tail_le` integrates that comparison on the measurable intersection of
the strict minimizing domain with the complement of a terminal-metric closed
ball, then enlarges the source set to the whole Gaussian tail.

`lRedJac_tail_lim` squeezes the large-source reduced integral against
`lSrcGauss_tail`, so it tends to zero as the terminal-metric radius tends to
infinity.  No tail bound, auxiliary measure normalization, or geometric input
beyond the already required positive-time solution data is assumed.

## Status

Focused verification and the targeted module refresh pass without warnings or
proof placeholders.  `lRedJac_src_le`, `lRedJac_tail_le`, and
`lRedJac_tail_lim` are each **100%** for their stated interfaces.  This closes
the large-source tail branch of the good/bad split.  The theorem
`redVolume_ball_le` remains unstated and unproved (**0%**), with its dedicated
machinery about **15--20%**; `smooth_nlc` remains unstated and unproved
(**0%**).

The next inside-ball/endpoint localization leaf is to bound the integral over
the terminal-metric source ball after splitting according to whether
`lExp S T x Z tau` lies in the controlled target metric ball.  The inside-
source/outside-target part needs the quantitative endpoint-displacement or
reduced-length lower bound supplied by `FlowMetricBall.IsRmControlled`; the
inside-target part can then be transported through `redVolume_lint` and the
L-exponential parametrization formula.

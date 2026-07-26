# LipschitzApprox

## Goal

Provide the quantitative chart-to-intrinsic gradient-error bridge needed to
turn chart-Sobolev approximation of a bounded intrinsically Lipschitz function
into metric-gradient control.

## Current state

`grad_sub_chart_le` chooses one nonnegative constant from the inverse Gram
matrix bounds on the compact supports of the finite canonical partition of
unity.  Uniformly over every active chart, it bounds the squared metric norm of
the gradient of the localized error `ρ_α * (u - v)` by that constant times
the corresponding coordinate partial square sum at every common
differentiability point.

The public Euclidean helper `fderiv_ae_chosen` in `LipschitzW1.lean` identifies
the classical directional derivative of a globally Lipschitz compactly
supported Euclidean function with the canonical chosen weak partial.  It is
the measure-level identification needed after the pointwise comparison here.

This is the pointwise metric-comparison producer.  The remaining frontier is
the measure-level assembly: identify the a.e. classical partials of the
localized Lipschitz-minus-smooth error with the chart weak partials, and sum
their `L²` bounds into `wkpNormChart`.

The pointwise theorem passed focused verification.  A later recheck was
blocked before source elaboration because the required upstream refresh of
`ChartBridge.Gradient` currently fails at its line 199 `MDifferentiableAt.sum`
type mismatch.  This is outside this file's claim.

## 2026-07-17 completed measure assembly

The stale state above is superseded. `local_grad_l2_le` chooses one constant
before all Lipschitz/smooth pairs and produces a measurable scalar majorant on
each active chart. `grad_sub_l2_le` sums those estimates and gives a uniform
intrinsic gradient-error bound by the chart `W¹,²` error.

`exists_smooth_grad` combines that bridge with chart Sobolev density.
`exists_smooth_supp` additionally chooses a smooth outer bump, applies the
quantitative smooth-multiplier theorem, and gives a smooth approximant inside
any prescribed open support margin with simultaneous function `L²` and metric
gradient `L²` error. The constant is chosen before the input function, so no
support-dependent constant is hidden in the consumer.

Focused verification passed for the full file, and the targeted module refresh
subsequently passed after the shared exponential import chain was current.
The exported `exists_smooth_supp` theorem is now consumed by the focused-green
`Perelman.exists_cutoff_energy` proof.

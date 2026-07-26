# HeatKernelBeta

## Status

Source-written; focused Lean verification is waiting for the shared named
build to finish.

## Proved source boundary

`critTime t s = (t-s)^(-1/2) s^(-1/2)` is the time kernel produced by a
first heat derivative acting on a `sqrt(s)|Du(s)|`-controlled divergence
flux.  The file source-proves interval integrability and the strict uniform
bound

`integral_0^t critTime(t,s) ds <= 4` for every `t > 0`.

`critCoeff_int_le` states the fixed-point form directly: after multiplying by
a nonnegative coefficient `K`, the time-integrated bound is `4K`.  `K` is the
only small factor.

The exact integral is `pi`; the elementary split-at-`t/2` bound avoids the
heavier complex Beta-function conversion and is sufficient for the fixed
point.

## Design consequence

There is deliberately no `T^alpha` factor.  Shrinking the horizon cannot make
this critical arm contractive.  Its small constant must be the inverse-metric
coefficient variation, ultimately controlled by the initial `C⁰`
oscillation/small positive-definite ball.  The local Carleson estimate must
carry the same coefficient smallness.

Endpoint accounting is unchanged: `ricci_flow_forward_unique` is 0% until
its exact theorem is proved and checked.

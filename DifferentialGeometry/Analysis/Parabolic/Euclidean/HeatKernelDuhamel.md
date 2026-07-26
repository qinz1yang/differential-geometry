# HeatKernelDuhamel

## Source status

This file integrates the genuine spatial `D^2 H_t` cancellation estimate in
time.  The exact scalar identity is

```text
integral from 0 to t of (t-s)^(-3/4) = 4 * t^(1/4).
```

It also records the first-derivative identity
`integral (t-s)^(-1/2) = 2 * t^(1/2)`, used by divergence-form flux arms.

The Banach-valued interfaces are:

- `heatD2Duh_int`: strong measurability in time plus one spatial
  `1/2`-Holder constant on the closed time interval gives an interval-integrable
  cancelled Duhamel integrand;
- `heatD2Duh_norm`: under the same strong-measurability datum, the genuine
  interval-integrable Duhamel second derivative is bounded by the same Holder
  constant times the explicit small factor `4 * t^(1/4)`.

No time derivative, high Sobolev norm, or metric-dependent horizon is used.
The source contains no `sorry`, `admit`, axiom, or opaque replacement.  Its
focused Lean check passes with no warnings.  Completion of the cancellation
and time-integration abstraction in this file is 100%; completion of either
analytic endpoint theorem is still 0% until the exact theorem is proved.

## Role in the endpoint

This is a dimension-generic Euclidean Schauder brick.  It is not by itself a
proof of `ricci_flow_unif_existence`; the remaining work is finite-atlas
localization, variable-coefficient absorption, the nonlinear chartwise fixed
point, realization, and same-horizon smoothing/pullback.

It is also not the reverse-realization theorem needed for forward uniqueness.
That role is now supplied at the abstract strong heat layer by
`StrongDuhamelBack`; this file supports the low-regularity existence estimates
through its explicit small-time cancellation factor.

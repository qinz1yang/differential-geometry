# KochLammFluxExp

## Purpose

This file supplies the exact real Hölder exponents for the late
`KLSource1 → L∞` heat-potential estimate.

## Proved source content

- `klPReal` is the real form of `klP = n+4`.
- `klPDual = (n+4)/(n+3)` is its Hölder conjugate.
- `klPDual_one` and `klPDual_two` place that dual exponent in `[1,2]`, the
  range consumed by the first-derivative power-mass theorem.
- `klD1Exp` simplifies to `-(n+2)/(n+3)`, hence is strictly greater than
  `-1`.
- `klD1Exp_add`, `klD1Scale_exp`, `klD1Time_int`, and `klD1Time_set`
  evaluate the terminal time integral and expose the exact
  `t^(1/(n+4))` scale after the dual root.
- `klD1Time_intble` proves the corresponding reflected terminal-time power is
  integrable on `(t/2,t]`.

## Verification state

Focused verification passes with no local warning.  The source contains no
`sorry`, `admit`, axiom, or opaque replacement.  This is one analytic layer
of the late flux value arm, not the full heat map, so
`ricci_flow_forward_unique` remains 0%.

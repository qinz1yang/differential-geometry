# KochLammExp

## Status

Source complete. The focused Lean check passes with no local warnings.

## Proved target

This file specializes the late ordinary-source exponents before the genuine
space-time Hölder estimate:

- `klQReal = (n+4)/2` is the source exponent;
- `klQReal_ofReal` identifies it with the existing `ENNReal` exponent
  `klQ V`;
- `klQDual = (n+4)/(n+2)` is its Hölder conjugate;
- `klHeatExp = n(1-klQDual)/2 = -n/(n+2)` is the time power in the exact
  spatial heat-kernel mass;
- `klHeatExp_gt` proves this power is greater than `-1`;
- `klTimePow_intble` proves the reflected power is interval-integrable on
  `(t/2,t)`.

This closes only the exponent/integrability input. The next theorem must use
it with `heatPow_shift` and Fubini to prove the terminal space-time kernel
`L^klQDual` bound, then pair it with the restricted `KLSource0` late arm.

The endpoint `ricci_flow_forward_unique` remains 0%.

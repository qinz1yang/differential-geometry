# TimeH1Ramp

## Purpose

This module realizes the two affine endpoint ramps as reusable `timeH1` curves.
On a positive interval, `rampUp T z` runs from `0` to `z`, while
`rampDown T z` runs from `z` to `0`.

## API

- `rampUp`, `rampDown`: the two `timeH1` curves.
- `rampUp_apply`, `rampDown_apply`: their continuous representatives on
  `[0, T]`.
- `rampUp_zero`, `rampUp_end`, `rampDown_zero`, `rampDown_end`: endpoint
  values for `0 < T`.
- `rampUp_deriv`, `rampDown_deriv`: their almost-everywhere constant weak
  derivatives for `0 < T`.
- `rampUp_smul`, `rampDown_smul`: scalar linearity in the endpoint vector.

The definitions use `timeH1.ofContDiffOn` when `0 ≤ T`; the otherwise branch
is zero because `timeH1 X T` itself is defined for every real `T`.

## Verification

Focused verification passed without warnings. The source contains no `sorry`,
`admit`, or new axioms, and every public name stays within the project's
twenty-character limit.

## Project status

This generic endpoint-ramp API is verified and complete (100%). It is reusable
in the L-geometry node-variation stage but does not itself prove node momentum
matching or the final L-minimizer theorem; those endpoints remain at 0% until
their own Lean theorems are proved.

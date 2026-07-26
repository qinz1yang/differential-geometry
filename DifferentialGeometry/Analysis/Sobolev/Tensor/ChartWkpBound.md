# ChartWkpBound

## Status

Source-written only; no Lean/Lake process was started in this lane because a
different named build owns verification.

## Mathematical content

This file proves the quantitative `W^{2,p}` transport estimate required for
genuine weak tensor sections.

- `transCoeffE` pushes the existing globally smooth, doubly cut off tensor
  transition coefficient into the source Euclidean chart.
- Its smoothness, compact support, and coordinate evaluation are exposed by
  `transCoeffE_smooth`, `transCoeffE_cpt`, and `transCoeffE_apply`.
- `coeffMulJoint` applies the existing quantitative smooth-multiplier theorem
  to control multiplication by that coefficient in `W^{2,p}`.
- `secTransTerm` is the source coefficient product followed by scalar
  cross-chart transport and target POU multiplication.
- `secTermJoint` combines multiplier and cross-chart constants. For every
  source scalar with support in the fixed POU image, it returns target
  `MemWkp 2 p` and a norm bound by a finite real constant times the source
  norm.

This is the dimension-independent, finite-component estimate; it does not use
the dimension-three spectral `H^3 -> H^1` shortcut.

## Honest progress

- Quantitative scalar term transport: 100% source-written, 0% Lean-verified.
- Finite tensor transport and completeness assembly: source-written in
  `ChartWkpCompat.lean` and `ChartWkpComplete.lean`, still 0% verified.
- Exact `ricci_flow_unif_existence`: 0%.


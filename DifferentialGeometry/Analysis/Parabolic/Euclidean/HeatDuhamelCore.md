# HeatDuhamelCore

## Role

This file is the physical-space entry point for the causal smooth-core
`L²` Hessian estimate.  It transfers spatial derivatives from the heat kernel
to a compactly supported smooth source, which supplies the physical-space side
of the spacetime Fourier realization argument.

## Current state

- `slice_compact` packages compact support of each spatial slice.
- `heatD1_ibp` transfers one heat-kernel derivative to the source.
- `heatD2_ibp` transfers one of two heat-kernel derivatives to the source.
- `heatD2_ibp2` transfers both derivatives; slice-shaped versions are exported.
- `heatPot1_eq_pot0` identifies the causal divergence potential with the
  ordinary potential of the spatial derivative for a smooth compactly
  supported space-time source.
- `heatPot0_zero` and `heatPot1_zero` record exact initial values.
- Every exported derivative-transfer theorem now assumes `ContDiff ℝ ∞`, the
  project notation for `C∞`.  The former `ContDiff ℝ ⊤` hypotheses meant real
  analyticity in the current Mathlib API and were stronger than the documented
  and mathematically intended smooth-source assumptions.

## Verification

Focused verification after the `∞` correction is GREEN and warning-free.  The
file contains no `sorry`, `admit`, axiom, or opaque declaration.

The rejected route was to retain the analytic-order `⊤` hypothesis or to add
it at the consumer.  That would make the compactly supported source core
vacuous apart from the zero source and would not prove the required smooth
realization theorem.  Weakening the canonical API to its intended `C∞`
statement is backward-compatible with any analytic caller.

## Next frontier

The immediate consumer is `HeatHessRealize`.  Its next exact goal is the
almost-everywhere identity between the damped causal heat-Hessian integral and
the convolution of the twice differentiated smooth source with the damped
causal heat kernel.  The positive-time branch now consumes `heatD2_slice2`
with the corrected `C∞` hypothesis; the subsequent frontier is the spacetime
`L²` multiplier estimate and removal of the damping parameter.

Endpoint accounting remains honest: both `ricci_flow_unif_existence` and
`ricci_flow_forward_unique` remain 0% until their exact Lean theorems are
proved.  The exact causal `heatD2Past_l2` checkpoint is also not yet proved;
its dedicated machinery is about 45% complete (the derivative transfer,
source Fourier symbol, convolution-Fourier bridge, and damped resolvent are
done, while the physical convolution identity, `L²` bound, damping limit, and
final `toLp` identification remain).

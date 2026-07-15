# MetricCovDerivLinear

## 2026-06-21

This file contains linearity and smooth-slot evaluation helpers for the
metric-covariant tower.

What is verified:

- `metricCovDeriv_succ_eval_smooth_slots_gen` is the boundaryless-free
  successor-slot evaluation formula for `metricCovDeriv`.
- The theorem exposes the same decomposition used by the private pullback proof:
  leading scalar directional derivative minus the finite sum of Levi-Civita
  correction terms.
- The formula is now reusable by open-subtype restriction and other locality
  arguments without importing the pullback-specific HCG bridge.

Verification passed.  No blocker remains in this helper file.

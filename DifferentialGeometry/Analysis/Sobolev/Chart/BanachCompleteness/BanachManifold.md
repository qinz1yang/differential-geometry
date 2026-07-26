# BanachManifold

## 2026-07-19: fixed-support property of the per-chart limit

### Implemented

- Added `chartLimit_ae_zero` without changing any existing declaration and
  without adding a class, instance, or notation.
- The statement says that the chosen Euclidean `W^{k,p}` chart limit is almost
  everywhere zero on the chart target outside the fixed image
  `toEuclidean '' (extChartAt I α '' tsupport ρ_α)`.
- The proof lowers the existing `wkpNorm` convergence to order-zero `eLpNorm`
  convergence, obtains convergence in measure, extracts an almost-everywhere
  convergent subsequence, and uses the public pointwise support theorem
  `chartPushed_support_subset_compact_in_target`. Uniqueness of limits in
  `ℝ` then forces the chosen limit to vanish off the fixed kernel.
- Compactness and measurability of that kernel are proved locally from compact
  `tsupport`, continuity of `extChartAt` on the subordinate chart source, and
  continuity of `toEuclidean`; no new support API is exported.

### Verification state

- Source implementation: 100%.
- Focused Lean verification: pending, intentionally not run while the shared
  verification slot is unavailable.
- The generic uniform Ricci-flow endpoint remains 0%; this is one spatial
  `W^{k,p}` completeness producer, not the parabolic maximal-regularity solver.

### Elaboration risks to check first

- Inference of the measure in `Measure.restrict_mono_set volume Set.diff_subset`
  inside the `h_ae.filter_mono` step.
- Coercion of the canonical partition-of-unity member to `M → ℝ` in the
  compact-kernel calculation.
- Rewriting `(extChartAt I α).source` with `extChartAt_source` under the local
  model-with-corners parameters.
- Recognition by `simpa only [hzero]` that the subsequence is pointwise the
  constant-zero sequence.

No `sorry`, `admit`, axiom, or opaque replacement was introduced.

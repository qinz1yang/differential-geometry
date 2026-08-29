# RedVolumeParam

## Role

This module is the fixed-positive-backward-time joint-parameter bridge from
compact L-cost upper semicontinuity to reduced-volume lower semicontinuity.  It
keeps the moving Riemannian measure honest by decomposing it through the native
finite chart partition of unity and integrating every chart contribution
against the fixed model Haar measure.

## Source route

- `exists_cost_curve` chooses an actual near-minimizing global `C¹` competitor.
- `lCost_param_usc` and `lCost_y_usc` derive the needed cost upper
  semicontinuity from the checked strict-event producers; they do not assume a
  continuity wrapper.
- `redDensity_param_lsc` and `redDensity_y_lsc` pass cost upper
  semicontinuity through the antitone reduced-density exponential.
- `chartDensity_time_cont` controls the moving metric density at fixed model
  coordinates.
- `redVolume_chart_sum` is the exact finite chart partition-of-unity
  decomposition of reduced volume.
- `chartRedTerm_liminf` applies the pointwise product liminf inequality and
  Fatou's lemma to one fixed-model-Haar chart contribution.
- An eventual regular-slab sequence shift promotes every chart Fatou estimate
  to chart-term lower semicontinuity.  Mathlib's native finite-sum lower-
  semicontinuity theorem then assembles the chart terms, avoiding unnecessary
  boundedness hypotheses on ENNReal liminfs.

## Public statement

`redVolume_lsc` states that for fixed `tau > 0`, if the base slab
`[T - tau, T]` is regular, then
`p ↦ redVolume S p.1 p.2 tau` is lower semicontinuous at `(T,x)`.
Its hypotheses are the native solution, connectedness, compactness, and slab
regularity assumptions used by the producer chain.

## Verification

Warning-free focused verification passed, including after adding the explicit
namespace terminator requested by the style linter.  The named artifact was
refreshed before that style-only edit; no exported declaration changed.  The
module contains no `sorry` or `admit`.  During elaboration repair, the generic
ENNReal liminf-add route was
replaced by the native finite-sum lower-semicontinuity theorem, and the moving
chart-density proof was simplified to the local metric-family entry theorem
plus native matrix determinant continuity.  This retained the original weak
regular-slab hypotheses; the stronger globally quantified
`MetricFamilyRegularAt` interface was deliberately not introduced.

## Progress accounting

- `redVolume_lsc`: theorem source and verified theorem 100%.
- Dedicated lower-semicontinuity machinery: source and verified machinery
  100%.
- `redVolume_unif_low`: theorem and its dedicated compact finite-cover /
  uniform-floor machinery 100%, verified in `RedVolumeUniform`.
- Whole Perelman L-geometry program: approximately 45%; P2 remains below 1%,
  and the whole Poincare program remains approximately 3--5%.

## Next target

The next separate L9 producer is the compact-slab reduced-volume-to-ball-volume
upper estimate.  It must consume the checked moving-range, scalar lower-bound,
metric-volume comparison, and dimension-uniform Gaussian-tail APIs; it must not
replace them with a supplied noncollapsing hypothesis.

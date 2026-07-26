# H6IsometryDeriv

## Purpose

This file is the independent [H6] Section 5 producer lane for the existing
`IsometryDerivBounds` honest input.  It does not replace the active B/C normal
branch and does not add a new consumer-side assumption.

## Status

- The framed-coordinate migration is complete. `normalTrans_isom`,
  `normal_fderiv_bij`, and `normal_fderiv_le_two` now state their overlap and
  derivative conclusions directly with `framedExpDiffeo`, `framedChartAt`, and
  `framedTransition`.
- `normal_bounds_on` now takes its two smoothness containments at the intrinsic
  `expRadiusGp` scale and its overlap hypothesis in the framed chart domains.
  Its sequence-family input/output deliberately retains the public
  `normalTransition` compatibility alias: that alias is definitionally
  `framedTransition` and packages the per-object manifold instances that a raw
  sequence lambda cannot infer on its own.
- Focused verification and the later ordered exact module refresh pass with no
  `sorry` or local linter warning.  The refresh was deferred until explicit
  authorization and run in dependency order.
- Gate 1 is complete: `isom_first_bound` turns exact metric isometry and the H6
  `1/2`/`2` quadratic-form comparison into the order-one bound `2`.
- Gate 2 is complete at the reusable pointwise level.  `isom_jet_one`
  differentiates the metric identity, `isom_koszul` performs the cyclic solve,
  and `second_eq_koszul` / `isom_second_eq` recover the exact vector formula.
  `second_norm_le` / `isom_second_bound` give the explicit order-two bound
  `6 * CB + 12 * CC`.
- `normalTrans_isom` proves exact isometry for normal-coordinate transitions;
  `normal_fderiv_bij` and `normal_fderiv_le_two` give their pointwise derivative
  bijectivity and operator bound on an H6-controlled overlap.
- Gate 3 is complete.  The proof-independent Gram inverse and raised-Koszul
  fields, local bilinear/composition estimates, exact second-derivative field
  recurrence, and recursive `isomBudget` close strong induction at every
  positive order.  The fixed-order form uses only metric jets through that
  order, matching the quantifiers of `NormalCoordMetricBoundInput.metricC`.
- Gate 4 is complete.  `isom_deriv_on` is the reusable open-domain pointwise
  theorem, `isom_bounds_on` produces `IsometryDerivBoundsOn`, and
  `normal_bounds_on` specializes it to normal-coordinate transition sequences.
  Order zero is supplied explicitly by a uniform target-domain norm bound;
  positive orders come entirely from H6 metric data.
- Route-mistake count is zero.  No alternative mathematical route was discarded.
- Final localized `IsometryDerivBoundsOn` producer theorem: **100% proved**.
  Dedicated H6 Section 5 machinery: **100% for the localized producer**.
  The canonical framed source repair and its focused verification are also
  **100% complete**.
  The fixed-source B/C consumer path through transition extraction, live-slot
  extraction, and atom/weight packaging is now checked. The finite source-slot
  diagonal and endpoint removal of `ExpInverseDerivBoundInput` remain separate.

## Next target

The H6 proof lane has no remaining mathematical frontier. The checked consumer
chain now ends at `existsAtomWeightH6`. The next integration step belongs to
the separately claimed finite source-slot diagonal: call that package instead
of `existsAtomWeightLim`, and reuse the canonical transition-overlap/maps-to
adapters being added in `StepBTransitionOverlap.lean`. Do not create a parallel
H6 diagonal or reintroduce a synonymous derivative-bound assumption.

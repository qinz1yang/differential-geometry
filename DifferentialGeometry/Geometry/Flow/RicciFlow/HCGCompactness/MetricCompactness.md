# MetricCompactness

Source used: MSM135 Definition 3.5 and Theorem 3.9.

Introduced definitions: `PointedRiemannianCGMaps`, `MetricSourceDomain`, `MetricSourceData`, `MetricSourceCPConvOn`, `MetricCGConvergenceData`, `PointedRiemannianCGConverges`, `MetricCompactnessConclusion`, and `metricCompactness`.

Honest frontier: this file's unconditional `metricCompactness` remains the
single metric-compactness proof `sorry`.  The direct-limit/exhaustion and
smooth metric-convergence assembly is now checked in the conditional endpoint;
the remaining unconditional gap is the native production of its cited
Cheeger--Gromov--Taylor, Bishop--Gromov, localized normal-coordinate, and
connectedness inputs from the theorem's public hypotheses.

2026-05-27 review update: the metric compactness layer now consistently uses the pointed Riemannian names. `MetricSourceData` also dropped its public `smoothPlus` field; source-domain `∞ + 1` is derived locally from the stored smooth manifold instance only at the low-level norm supremum.

2026-05-27 injectivity update: `metricCompactness` now carries `[I.Boundaryless]` because its `BaseInjBound` hypothesis is the HCG wrapper around the normal-coordinate injectivity-radius backend.

Verification: passed with the expected single `sorry` at `metricCompactness`.

2026-06-17 P4 metric-domain backend update: corrected the
`MetricSourceData.compact_preimage` shape so compact restriction now requires
the honest eventual-domain hypothesis `K ⊆ Φ.source k`. Added the matching
`metricSourceCompactSet_isCompact` lemma, canonical open source/target domain
structures, `metricSourceTargetDiff`, `MetricSourceData.ofCanonical`,
`MetricSourceData.ofRestrictPullback`, and the metric/pointed
`ofRestrictPullback` convergence constructors. The metric-only source-domain
packaging now builds from real open-subtype restriction and pullback metrics;
the remaining input is the analytic seminorm convergence for those constructed
metrics, plus the existing global `metricCompactness` compactness `sorry`.
Verification passed with the expected single `metricCompactness` `sorry`.

2026-07-09 comparison-domain differential update: added
`metricSourceTargetDiff_mfderiv`. It identifies the differential of the bundled source-to-target
diffeomorphism with the ambient differential of the stored comparison map. The proof differentiates
the two equal ambient composites and removes the source/target subtype inclusions. Focused
verification and the targeted module build passed; the expected unconditional endpoint `sorry` is
unchanged.

2026-07-10 D6 repointing update: added `PointedRiemannianCGMaps.unrepoint`,
`MetricSourceData.unrepoint`, `MetricCGConvergenceData.unrepoint`, and
`PointedRiemannianCGConverges.unrepoint`.  These transport a checked convergence
package from a sequence whose members differ only by stored basepoints back to
the original sequence, given the pointwise basepoint equalities.  The metric,
source, and target-domain data are preserved by field-wise rewrapping, so no
record equality or `HEq` transport is needed.  Focused verification and the
targeted module refresh passed; the existing unconditional endpoint `sorry` is
unchanged.

2026-07-17 conditional-endpoint update: the selected B/C producer now supplies
all five `StepB1RawInput` fields, Step D consumes that record, and
`C4/MetricCompactnessEndpoint.lean` lifts the resulting nested-subsequence
conclusion back to the original sequence.  The conditional Theorem 3.9 is
focused- and targeted-green (100%).  This file's unconditional theorem remains
0% until the external comparison/packing/normal-coordinate bundle and required
connectedness are produced natively.  The source docstring was updated to keep
that separation explicit; its theorem body and sole `sorry` were not changed.

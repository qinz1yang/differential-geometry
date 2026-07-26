# MetricCompactnessEndpoint

## Role

`MetricCompactnessEndpoint.lean` is the final assembly layer for the conditional
MSM135 Theorem 3.9 endpoint.  The input structure remains in
`MetricCompactnessInputs.lean`; moving the theorem body here avoids an import
cycle while preserving the public name
`MetricCompactnessInputs.metricCompactness` and its statement.

## Checked assembly

The proof uses exactly this chain:

1. completeness and connectedness give the per-stage `ProperMetricOn` data;
2. `MetricCompactBase.exists_b1_raw` chooses a strict subsequence and produces
   the concrete `StepB1RawInput` (all 5/5 fields checked);
3. `compactness_of_b1` runs the checked Step-D consumer on that subsequence;
4. `MetricCompactnessConclusion.ofSeqSubseq` composes the nested subsequence and
   returns a conclusion for the original pointed sequence.

Focused verification and the exact targeted module refresh pass against the
canonical framed B/C chain.  There is no `sorry` or `admit` in this file or in
the concrete `compactness_canon` sidecar constructor it calls.

## Honest accounting

- `MetricCompactBase.exists_b1_raw`: 100%.
- concrete `StepB1RawInput`: 5/5 fields checked.
- selected B/C-to-B1 producer route: 100%.
- nested-subsequence lift and endpoint wiring: 100%.
- `compactness_canon`, `metricCanon`, and the projected
  `MetricCompactnessInputs.metricCompactness`: 100% checked.
- separately named textbook B1 theorem: unstated/unproved, 0%.
- historical full textbook Step-C arbitrary recurrence: separate and incomplete.
- unconditional Theorem 3.9: 0%; native CGT, Bishop--Gromov/uniform-packing,
  [H6], and connectedness producers remain outside this explicit-input theorem.
- Chapter 4 machinery: approximately 95%.
- whole-HCG machinery: approximately 60%.

The endpoint adds no branch-specific radius field and no new mathematical
assumption.  The explicit-volume conditional endpoint is complete; native
Bishop--Gromov/uniform-packing production is the remaining unconditional volume
frontier.

## 2026-07-18 canonical sidecar endpoint

The assembly now exposes `MetricCompactnessInputs.metricCanon`, which runs the
same selected B/C producer and concrete Step-D construction but retains the
`StepDCanonData` provenance through the nested subsequence.  The existing
`metricCompactness` name and statement are preserved as the `.mc` projection;
the abstract `MetricCompactnessConclusion` itself is unchanged.

The canonical framed dependency chain is now exact-current through
`StepDAssembly` and this endpoint.  Consumer/import verification is green; the
remaining obstruction is mathematical/API content in `HasCanonBounds`, not a
stale artifact or framed-coordinate mismatch.

This section recorded the state before the concrete canonical-bounds producer
was proved; it is superseded by the update below.

## 2026-07-19 canonical endpoint closed

`compactness_canon` now proves `HasCanonBounds` from the concrete Step-D chain:
an all-tail estimate is combined with compact finite-head collars, then metric
equivalence and covariant bounds are transported through the canonical
source-target diffeomorphism and the nested subsequence.  The endpoint consumes
that checked sidecar without changing the abstract
`MetricCompactnessConclusion` API.

Focused verification and the exact targeted refresh pass through
`MetricCompactnessEndpoint`.  Honest accounting: `compactness_canon`,
`metricCanon`, and conditional Theorem 3.9 are each 100% checked; the selected
conditional Chapter-4 route is 100%.  The separately named textbook B1 theorem
and unconditional Theorem 3.9 remain 0%; `compactnessSol` and the Hamilton
endpoint also remain theorem-level 0%.  Whole-HCG machinery remains
approximately 60%.

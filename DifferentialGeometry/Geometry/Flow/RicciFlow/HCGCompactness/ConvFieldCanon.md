# ConvFieldCanon

## Role

`ConvFieldCanon.lean` is the readable final producer assembly where the two P4
lanes meet.  It takes the concrete `StepDCanonData` sidecar, completeness, and
the sequence curvature package and keeps the following objects explicit in the
proof:

```text
canon → mc → Phi → bf
              ↓
       per-window equivalence + Shi
              ↓
           srcData
              ↓
 hbound / hcovTail / hlipTail / hlipSrc / hcp
              ↓
       open_upgrade_of_raw
```

The public theorem is `open_upgrade_canon`; the name is eighteen characters
and stays within the repository's twenty-character limit.

## Exact assembly

For each canonical window, one call to
`CurvBoundInput.metricEquiv_open` chooses the Ricci coefficient and finite
equivalence majorant before the sequence index.  The same window data are used
for all later consumers, avoiding independent incompatible choices.

The target-side data are reindexed by `mc.subseq` and restricted from
`Set.univ` to `Phi.target k`.  `CurvBoundInput.movingShi_open` is transported
to each source domain by `srcShi`.  The canonical `canon_rel` and `canon_init`
projections then feed `srcCovLip_of_soln`, producing one `SrcCovLipData` per
window.

The raw packages are transparent projections/adapters:

- `hbound` uses `hbound_of_equiv` with
  `cLow n = (Crel * Bmax n)⁻¹`;
- `hcovTail` uses grow-local `covTail_of_bounds` and `srcData.cov`;
- `hlipTail` uses grow-local `lipTail_of_src` and `srcData.lip`;
- `hlipSrc` restricts the stronger whole-source `srcData.lip` estimate to the
  requested compact set;
- `hcp` is exactly `StepDCanonData.canon_cp`.

No endpoint assumption, bump-derivative assumption, new radius hierarchy, or
claim about arbitrary `MetricCompactnessConclusion` was added.

## Current verification state

`open_upgrade_canon` is focused GREEN with zero `sorry`, `admit`, or `axiom`
in this module.  The definitional equality

```text
tgtRefSrc gRefT hsrc htgt k = srcMetric hsrc htgt k 0
```

is checked by reflexivity once the target-manifold instances are materialized
in the local proof.  The only source repair was to repeat the canonical
topology/chart/manifold/compactness instances inside dependent lambda and proof
bodies; no metric assumption or compatibility wrapper was added.

The theorem and its dedicated consumer assembly are now focused and exact
GREEN (`9720/9720`), with a current module artifact.  This does not prove the
unconditional `compactnessSol` endpoint:
`open_upgrade_canon` consumes a concrete `StepDCanonData`, and its Shi input
still comes through the independent complete-noncompact analytic lane.  The
unconditional endpoint therefore remains 0%; dedicated P4 support machinery
is approximately 98%, while whole-HCG supporting machinery remains roughly
60%.

# Step-D canonical P4 adapters

## Role

`StepDCanonP4.lean` is the bounded provenance-to-P4 bridge.  It applies only to
the concrete `StepDCanonData` sidecar and deliberately makes no claim about an
arbitrary `MetricCompactnessConclusion`.

The three projections expose the exact flow-side shapes needed downstream:

- `canon_cp`: compact-open time-zero convergence for `conv0_of_cp`;
- `canon_rel`: one source-index-independent time-zero metric-equivalence
  constant;
- `canon_init`: the source-index-independent initial covariant envelope used
  by the constants-first source-flow estimates.

## Provenance repair

The original `ref_eq` field was not sufficient for these adapters.  A general
`MetricSourceData` also stores topology, charted-space, manifold, and
sigma-compact instances, while the flow side uses the canonical open-subtype
instances.  Rewriting only the reference metric therefore left a genuine
dependent-instance mismatch.

The minimal repair is the whole-record equality now retained by
`StepDCanonData.domain_eq`:

```text
mc.convergence.metrics.domain k = canonDomain mc.maps k
```

Here `canonDomain` is the existing metric-native restriction/pullback source
data with the restricted limit metric as reference.  Rewriting by this equality
recovers both the canonical instances and the three canonical metrics; the
metric-to-flow comparison maps are a field-for-field copy, so the remaining
source-domain expressions reduce to the established flow-side definitions.

No new geometric hypothesis, radius field, compatibility wrapper, or parallel
convergence hierarchy was introduced.

## Verification and frontier

The adapter source contains no `sorry`, `admit`, or `axiom`.  After the
canonical-bounds producer closed, focused verification passed and the exact
targeted refresh completed successfully.  `canon_cp`, `canon_rel`, and
`canon_init` are therefore 100% checked, as are `compactness_canon` and the
conditional metric-compactness endpoint.  The Step-D provenance lane has no
remaining frontier.

The independent analytic lane remains: arbitrary-dimensional complete
noncompact Shi estimates and the constants-first varying-source producer.
Accordingly unconditional `compactnessSol` stays theorem-level 0%; P4 support
machinery is roughly 97%, and whole-HCG machinery remains roughly 60%.

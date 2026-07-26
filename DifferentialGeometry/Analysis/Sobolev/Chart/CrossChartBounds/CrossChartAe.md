# CrossChartAe

## 2026-07-19: fixed a.e.-support cross-chart producer

### Implemented

- `compactRep` replaces an a.e.-compactly-supported Euclidean function by its
  pointwise closed-set indicator representative.
- `compactRep_support` and `compactRep_ae` record its exact support and
  a.e.-equivalence on the chart target.
- `rawPullback_self` proves the same-chart raw push/pull identity.
- `crossPullback_ae` transports a.e.-equality through a chart pullback and a
  second chart's POU pushforward.  It uses quasi-measure preservation on the
  overlap and pointwise vanishing off the overlap.
- `crossChartAeJoint` combines these facts with `crossChartJointK`.  For every
  `MemWkp k p` input which is a.e. zero off the fixed compact chart kernel, it
  returns both target-chart `MemWkp` membership and a norm bound with a constant
  independent of the input.

### Route audit

1. Reusing the old higher-order theorem verbatim did not suffice: it exported
   a norm bound but no Sobolev membership.
2. Inferring `MemWkp` merely from finiteness of `wkpNorm` is not faithful: the
   norm expression alone does not certify the weak-derivative relations.
3. The selected route exports the membership already proved inside the
   cross-chart argument, then uses a compact indicator representative and the
   existing quasi-measure-preserving transition API.

### Verification and project state

- Source implementation: complete; 270 lines.
- Focused Lean verification: pending because this lane was explicitly
  source-only while another named build owned the shared verification slot.
- No class, instance, notation, axiom, `sorry`, or `admit` was introduced.
- The downstream finite-sum assembly is now implemented source-only in
  `BanachCompleteness/ManifoldLimitWkp.lean`; its focused Lean verification is
  likewise still pending.
- `ricci_flow_unif_existence`: still 0%.  This producer only advances the
  generic spatial `W^{k,p}` completeness route.

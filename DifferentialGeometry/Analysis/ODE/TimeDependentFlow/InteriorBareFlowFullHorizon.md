# InteriorBareFlowFullHorizon

## 2026-07-19 analytic-producer work

`bare_fromZero_full` combines two already separated regimes:

- `bare_fromZero_local` supplies equality on one positive initial window from
  an explicit chart-field Lipschitz datum at time zero;
- `wch_interior_coherence` propagates equality from one positive time to any
  later target, using the field's joint smoothness only on the open positive
  time interval.

Thus two one-sided bare integral curves with a common initial value agree on
the whole common half-open horizon.  No uniform lower bound for successive
interior continuation windows is used.

Verification status: the complete file passes its focused check, including
both `bare_fromZero_full` and `bare_Ico_unique`.  The remaining Ricci-flow
uniqueness work must still construct the regularizing-flow gauges, prove their
one-sided initial orbit equation, identify their common DeTurck velocity, and
undo the gauge.  The exact theorem `ricci_flow_forward_unique` therefore
remains 0%.

`bare_Ico_unique` covers the stronger and shorter endpoint situation in which
the driving field is jointly smooth on the closed slab.  It applies the proved
Seeley time extension and then the existing one-sided autonomous integral-curve
uniqueness theorem on each compact initial segment.  This is the intended
de-gauging tool after a gauged metric has been identified with the canonical
Ricci--DeTurck solution, whose DeTurck field is already jointly smooth through
the initial edge.  The HMF producer must still supply its orbit equation at the
one-sided initial time; this lemma does not assume or construct HMF existence.

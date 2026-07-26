# ChartWkpTransport

## Status

Source-written only. No Lean/Lake process was started in this lane because a
different named build owns verification. Every theorem below therefore still
needs focused elaboration verification.

## Mathematical role

The existing public tensor transition coefficient is already the correct
coefficient for weak tensor fields: its definition depends only on the bundle
trivializations, not on smoothness of the section. The earlier transformation
theorem nevertheless accepts only `SmoothCcTensor`, which cannot consume a
Sobolev limit.

This file repeats only the section-independent fibrewise algebra for the new
genuine raw-section carrier:

- `secTriv_trans` proves the coordinate-change identity for any
  `RSTensorSection`;
- `secCompRaw_trans` expands an arbitrary raw section into the existing finite
  `transitionCoeff` sum;
- `secPull_triv_eq` and `secPull_raw_eq` show that pulling an arbitrary model
  field back through its own chart trivialization recovers that field and its
  canonical scalar projections;
- `secPull_raw_trans` combines the two results, giving the exact pointwise
  target-chart expression needed for weak-Sobolev transport.

No regularity of the model field is used, no weak limit is declared smooth,
and the proof uses only public component/basis operations. No tensor `Hom`
representation, global instance, foundational class, notation, axiom, opaque
producer, `sorry`, or `admit` was introduced.

## Exact next theorem

The next analytic producer should push `secPull_raw_trans` to Euclidean chart
coordinates, multiply by the target POU factor, and invoke scalar cross-chart
Sobolev transport term by term. A useful consumer shape is:

```lean
theorem secPull_wkp_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β α : M) (v : EuclN → TensorRSModel r s ℝ E)
    (hv : ∀ Q, MemWkp k p
      (fun y => tensorChartComponentProjection r s Q.1 Q.2 (v y))
      (chartTargetEuclid β))
    (hv_support : every source component is a.e. supported in the fixed
      Euclidean image of the β-POU kernel) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ P₀,
      MemWkp k p (secChartComp r s (secModelPull r s β v) α P₀.1 P₀.2)
        (chartTargetEuclid α) ∧
      wkpNorm k p
        (secChartComp r s (secModelPull r s β v) α P₀.1 P₀.2)
        (chartTargetEuclid α) ≤
      C * ∑ Q, wkpNorm k p
        (fun y => tensorChartComponentProjection r s Q.1 Q.2 (v y))
        (chartTargetEuclid β)
```

The key remaining detail is support. The chosen component limits in
`ChartWkpLimit.lean` must inherit the a.e. support of the POU-weighted
approximating components, as in scalar `chartLimit_ae_zero`. This prevents an
arbitrary off-target representative from contaminating `secModelPull`.

## Honest progress

- Raw-section tensor transition algebra: 100% source-written, 0% Lean
  verified.
- Weak model-pull target-chart formula: 100% source-written, 0% Lean verified.
- Support inheritance for chosen component limits: 0%; the scalar argument is
  available to port.
- Quantitative tensor cross-chart `W^{k,p}` estimate: 10% machinery, 0% exact
  theorem.
- `wkpTensor_limit`: 30% machinery, 0% exact theorem.
- Exact `ricci_flow_unif_existence`: 0%.

## Superseding implementation update

The support and quantitative theorem requested above are now source-written in
`ChartWkpSupport.lean` and `ChartWkpBound.lean`. Exact finite compatibility is
in `ChartWkpCompat.lean`, including explicit elimination of both target and
source cutoff factors, and the completeness assembly is in
`ChartWkpComplete.lean`. This supersedes the earlier “exact next theorem” and
progress figures. None is counted as proved until focused Lean verification.

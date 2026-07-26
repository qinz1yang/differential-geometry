# Metric completeness under a lower bound

## Status — 2026-07-17

`MetricComplete.complete_of_lower` is checked without `sorry`.

The theorem starts with a pointed manifold `X` whose stored metric is complete,
a second smooth metric `h`, a constant `c > 0`, and the global quadratic-form
bound

```text
c * X.metric.inner x v v ≤ h.inner x v v.
```

It returns `CompleteSpace X.M` for the Riemannian emetric induced by `h`.  The
target metric is packaged as `{ X with metric := h }`, so the proof reuses the
canonical `PointedRiemannianManifold.riemBundle`, `riemInner`, and
`riemBundle_cont` installation rather than constructing a parallel metric API.

The proof combines `edistOf_scale` and `edistOf_mono` to obtain

```text
sqrt(c) * d_X ≤ d_h.
```

An `h`-Cauchy sequence is therefore Cauchy for `X.metric`; completeness of the
reference metric supplies a limit.  Both Riemannian emetrics induce the stored
manifold topology, so the same limit is valid for `h`.

The explicit topology normalization before the final source-metric instance
switch is important for elaboration: it avoids an expensive definitional
equality comparison between two reducible Riemannian emetric structures.

Focused verification passed with no warnings.  This theorem and its dedicated
comparison machinery are 100%.  It is a reusable consumer-side bridge; it does
not by itself prove the all-time lower bound or the unconditional HCG
compactness endpoint.  The latter remains theorem-level 0%, while whole HCG
machinery remains about 60%.

# MetricLapDiffPair

## 2026-07-13 short-time alignment

The duplicated private `toRS0_sub` bridge was normalized in the same way as
`MetricLapDiffCore`: scalar evaluation followed by `smul_sub`.  Focused
verification passes without `sorry`; the pairwise endpoint and its progress
accounting are unchanged.

## Role

This module proves the fixed-reference pair estimate needed for operator-norm
continuity of the genuine moving scalar Laplacian.  For fixed spectral metric
`q` and center metric `k`, the constant is independent of the finite spectral
support and the varying metric `h` is controlled by its `C¹(k)` distance.

The finite-core squared norm is first reduced to the scalar integral of
`(Δ_h u - Δ_k u)²`.  `lapDiff_pair_energy` combines the invariant pointwise
Laplacian-difference estimate with `cross_energy_le q k`.  The final operator
bound is lifted from the dense spectral core through a closed norm inequality;
it does not prove an equality of whole continuous-linear-map objects.

## Public endpoint

`lapDiff_pair_norm q k` supplies a nonnegative constant `C` such that, under
the two fixed-`q` extension hypotheses and the pairwise `k` smallness
hypothesis,

```text
‖lapDiffOp q h - lapDiffOp q k‖
  ≤ sqrt(C) * |metricDerivNormSupOn univ 1 h k k|.
```

## Verification status

The complete file is verified without `sorry`; both the focused check and the
targeted module build passed.  The only dense-lift repair was to normalize the
submodule subtype coercion before rewriting with `lapDiffOp_core`.

## Progress accounting

- `lapDiff_pair_norm`: 100% theorem and 100% dedicated machinery.
- Fixed-`L²` pairwise continuity producer for A2: 100%.
- `lapDiffA20_short`: verified (100% theorem and dedicated A2 machinery).
- Full geometric nonautonomous input package: about 50% machinery; its final
  assembly theorem is 0%.
- Moving conjugate-heat theorem: 0%.
- Perelman no-local-collapsing theorem: 0%; dedicated machinery about 8%.

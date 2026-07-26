# ChartWkp

## Status

This is a source-only implementation.  No Lean/Lake command was run in this
lane because another named build owns verification.  Consequently every item
below is an implemented source claim, not yet an elaboration claim.

The file introduces the dimension-independent tensor chart-Sobolev carrier
needed by a maximal-`L^p` Ricci--DeTurck route:

- `RSTensorSection I M r s` is the genuine dependent section
  `forall x, TensorRSSpace r s I x`; it is not an unconstrained array of chart
  components.
- `secTriv`, `secCompRaw`, `secCompPou`, and `secChartComp` use the existing
  bundle trivialization and public continuous-linear
  `tensorChartComponentProjection`.  No tensor `Hom` representation is
  unfolded.
- `MemWkpTensor g k p S` asks that every POU-weighted chart component is in the
  scalar Euclidean `MemWkp k p` space.
- `wkpTensorSub` and `WkpTensor` package the zero/add/scalar closure.  The
  subtype is an abbreviation, so existing submodule structures are reused and
  no new global foundational instance is installed.
- `wkpTensorNorm` is the `ENNReal` sum over charts and the two finite component
  index types.  `secComp_zero_off` collapses the chart sum to
  `chartAtlasPOU_finset`; `wkpTensorNorm_lt_top` proves finiteness on the
  carrier.
- `TensorAEEq` is componentwise a.e. equality on each chart target.
  `WkpTensorQuot` is the resulting quotient and `wkpTensorQNorm` is the
  well-defined quotient-valued `ENNReal` norm function.

The source contains no `sorry`, `admit`, axiom, opaque producer, notation, or
global normed/complete-space instance.

## Why this carrier is the correct general-dimensional lane

The exact `ricci_flow_unif_existence` statement is dimension-general and has
uniform `C^3` data.  The existing spectral three-arm `H^3 -> H^1` estimate gets
the necessary algebra and small highest-order coefficient in dimension three;
it is not a proof of the general endpoint.  A general-dimensional contraction
must choose `p` relative to `dim M` and work in tensor `W^{k,p}` / maximal-`L^p`
spaces.  This file supplies the first missing carrier without increasing the
regularity assumptions or replacing tensors by unrelated chart arrays.

## Exact remaining completeness theorem

The smallest consumer-shaped analytic theorem still missing after this file
is the following representative form of quotient completeness (the public
name is within the repository limit):

```lean
theorem wkpTensor_limit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp_one)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      (wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1)).toReal < ε) :
    ∃ v : WkpTensor (I := I) (M := M) g r s k p hp_one,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (wkpTensorNorm (I := I) (M := M) g k p
          ((u n).1 - v.1)).toReal < ε
```

Its non-formal core is now narrower. `ChartWkpLimit.lean` uses scalar
completeness for every chart/component sequence, reconstructs a model tensor
from those limits, pulls each model field back through the genuine bundle
trivialization, and sums over the finite atlas POU. Thus it does not treat an
arbitrary component array as the final carrier and does not need a separate
compatibility axiom merely to define the candidate. What remains is the
quantitative tensor transition estimate showing that each target-chart
component of a pulled-back local model field is in `W^{k,p}` and is bounded by
the finite source-component norms. This is also the estimate needed to pass
componentwise convergence through the finite POU sum and obtain convergence in
`wkpTensorNorm`.

After `wkpTensor_limit`, one can locally install the seminormed structure,
obtain theorem-valued `CompleteSpace WkpTensorQuot`, and build the tensor
maximal-`L^p` forcing and Duhamel operators.  Adding such global instances in
this file would cross the explicit foundational-instance boundary, so it was
not done.

## Honest progress

- Genuine tensor `W^{k,p}` carrier, finite norm, and a.e. quotient: 90%
  source-complete; 0% Lean-verified in this lane.
- Tensor quotient completeness: 25% machinery; chartwise scalar limits and a
  genuine POU-assembled candidate are source-written in `ChartWkpLimit.lean`.
  The exact endpoint `wkpTensor_limit` remains 0% until tensor cross-chart
  `W^{k,p}` transport and total-norm convergence are proved and verified.
- Quotient-safe Ricci--DeTurck nonlinearity and maximal-`L^p` solver: 0%.
- Exact `ricci_flow_unif_existence`: 0% until the full producer and uniform
  same-horizon realization/smoothing are proved and verified.

## Superseding implementation update

The representative theorem sketched above is now source-written for the
needed `k = 2` lane in `ChartWkpComplete.lean`, with the Cauchy control and
conclusion kept in the native `ENNReal` chart norm. Its prerequisites are
split into `ChartWkpSupport.lean`, `ChartWkpBound.lean`, and
`ChartWkpCompat.lean`. The same file also states `wkpTensorQ_limit`, expressing
convergence through `wkpTensorQNorm` without adding global quotient algebra or
metric instances.

This update supersedes the earlier completeness progress figures. The exact
theorems remain 0% Lean-verified until the named verification lane checks the
new source. A theorem-valued `CompleteSpace WkpTensorQuot` is still a separate
foundational construction because the present quotient has no algebra or
metric structure.

`ChartWkpQuot.lean` subsequently adds zero/add/neg/smul/sub as explicit
ordinary quotient functions and proves their norm laws and zero separation.
It still introduces no standard algebraic or metric instance.

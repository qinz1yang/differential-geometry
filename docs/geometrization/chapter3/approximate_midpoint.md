# Complete approximate-midpoint criterion: MC22

The new leaf
`DifferentialGeometry/Topology/MetricSpace/ApproximateMidpoint.lean`
proves the completeness-only MC22 criterion, including an actual curve and
its quantitative Lipschitz and length bounds. Properness and local
compactness are not assumptions.

## Exact public statements

Let X be a complete ordinary metric space. Assume that for every a,b in X
and every ε>0 there is z with

```
d(a,z) ≤ d(a,b)/2 + ε,    d(b,z) ≤ d(a,b)/2 + ε.
```

For any a,b and τ>0:

- `Metric.exists_lipschitz_curve_of_approximate_midpoints` produces an
  actual function `f : Icc (0 : ℝ) 1 → X`, with f(0)=a and f(1)=b, that
  is Lipschitz with constant `d(a,b)+τ/2`.
- `Metric.exists_curve_eVariationOn_lt_of_approximate_midpoints` produces
  an actual `f : unitInterval → X`, with continuity, the same endpoints,
  the same Lipschitz bound, and
  `eVariationOn f univ < ENNReal.ofReal (d(a,b)+τ)`.

`unitInterval` is Mathlib's real interval [0,1]; these are the same
underlying interval conventions. `eVariationOn` is Mathlib's extended
metric variation, the supremum of finite ordered partition sums, and is
the curve length used here. No surrogate length functional is introduced.
The strict upper bound is finite, so the constructed curve is rectifiable.

The theorem holds for a=b as well. There is no division by d(a,b), no
positive-diameter assumption, no independently assumed connectedness,
and no pre-existing path existence premise. Completeness and approximate
midpoints are the geometric hypotheses. The conclusion supplies the
near-minimizing curves themselves, not merely a reformulation of their
existence as a new property or class. It does not claim that the distance
is realized by a minimizing segment in an arbitrary complete space.

## Coherent dyadic construction

Fix D=d(a,b), C=D+τ/2 and `r_n=2^-n`. At dyadic refinement step n use
midpoint error

```
h_n = (τ/8) r_n² = τ 2^(-2n-3).
```

Even-indexed values are copied exactly from the previous level; odd
values are chosen approximate midpoints between the neighboring old
values. The first and last values are a,b at every level. The induction
proves the adjacent-distance bound

```
δ_n = C r_n − (τ/2) r_n²,
δ_0 = D,
δ_(n+1) = δ_n/2 + h_n,
δ_n ≤ C r_n.
```

This is algebraically the blueprint's bound
`2^n * maxAdjacentDistance ≤ D + (τ/2)(1-2^-n)`.
The bound is proved for each edge directly; no unnecessary finite-maximum
object is introduced.

Define the level-n step approximation to t by the value at
`floor(t*2^n)`. The polygon inequality and the floor estimates give

```
d(g_n(s),g_n(t)) ≤ C*d(s,t) + C*2^-n.
```

Coherent refinement is essential here. The identity
`floor(t*2^(n+1))/2 = floor(t*2^n)` implies that a step value either stays
at its old point or moves to its adjacent inserted midpoint. Thus

```
d(g_n(t),g_(n+1)(t)) ≤ C*2^-n.
```

For each t this gives a Cauchy sequence by Mathlib's geometric-series
criterion. Completeness provides its limit F(t). Passing the two-point
bound to the limit makes F C-Lipschitz; exact endpoint retention gives
F(0)=a and F(1)=b. This is the blueprint's coherent dense-domain extension
implemented through the canonical dyadic step sequences. A separate type
of dyadic rationals, quotient of representations, or proper-space
compactness argument is unnecessary.

For the length bound, the proof extends F arbitrarily outside [0,1],
uses the actual Lipschitz-on-interval estimate from `CurveVariation.lean`,
and restricts back through the monotone subtype inclusion. This proves
that the same curve has variation at most C, and hence strictly less
than D+τ. No continuity of the finite step approximations is asserted or
used; only the limit curve is proved continuous.

## Blueprint and source correspondence

The exact contract and written proof were read in revision207
`master207A.tex`, MC22 `thm:metric-approximate-midpoints`, lines1534-1580,
alongside the midpoint conventions and MC21/MC23. The errors, finite
distances, completeness-only scope, endpoint retention, Lipschitz
constant and strict length inequality agree with that statement.

The existing detailed source check in `reference_checks_revision68.md`
was reused: BBI Proposition1.5.9, printed11-12/PDF26-27; Definitions and
lemmas2.4.7-2.4.10, printed41/PDF56; Theorem2.4.16 and proof,
printed42-43/PDF57-58. The archived book's SHA256 is
`4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.
The retained author errata remove the local-compactness requirement in
this discussion. The source gives the exact-midpoint construction and
leaves the approximate case as an exercise; the blueprint and this code
provide the approximate-case proof, rather than importing that exercise
as an axiom. No new exhaustive source/errata audit is claimed.

`DenseExtension.lean` was inspected for the existing extension boundary.
This proof implements its particular coherent-grid extension directly by
Cauchy sequences and does not assume an extension theorem containing the
desired curve. The new midpoint operators and refinement helpers remain
private to their mathematical proof.

## Executed checks and downstream use

The final leaf build passed on Lean `v4.35.0-rc3`, Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, reporting 1,702 jobs.
Both public theorem types were inspected. Their axiom closures contain
only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx`, custom mathematical axiom or unsafe declaration. No whole-PC
or whole-root build is claimed by this receipt.

The second theorem's curve/variation output has the precise form consumed
by `CurveMidpoint.lean` after discarding its additional Lipschitz field.
The separate proper-space theorem in `GeodesicMidpoint.lean` produces
distance-realizing segments. The present theorem supplies the stronger
completeness-only near-minimizing-curve conclusion needed in MC14's
length-closure branch.

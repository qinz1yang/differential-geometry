# SbrGradientSpeed.lean

Verified 2026-09-08 in the dev checkout. The actual submaximal generalized gradient is nonzero and its maximizing unit direction yields the eventual inverse-gradient metric-speed bound for the constructed curve.

Empty focused output: 14.9s. Lint-clean named build: 18.5s.
Fresh external public axiom audit: 13.1s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrGradientSpeed-result1.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Source-ready and frozen for the parent's verification queue, 2026-09-08.
This implements the bounded SbrGradientSpeed brief appended to
`SOUL_PLAN.md`. The parent controls verification; this worker remains
source-only. No Lean, Lake, REPL, check, build, artifact refresh, axiom
audit, root import, shared-plan/status edit, or commit was performed.

Claim retained: `9e5f149d-f8aa-4876-a372-7a6b27af1d43`.
Frozen source SHA256:
`D229D30D791C42F0FE7B9B2C390699AFF692C5B03BF9D7B1ED496A34AE0805B9`.
There is one public theorem and one private real-arithmetic helper, with
no proof placeholders or axiom declarations. Compiler verification and
the public dependency audit remain pending. `SbrEulerSpeed.lean` is
unchanged at its frozen hash
`A29238758F90B02E2E2707EEEE1A160D8820D520B2922249466B8CDBD84D46B3`.

## Actual endpoint and provenance

`exists_nearest_superlevel_limit_with_gradient_speed` constructs its eta
from `exists_nearest_superlevel_limit_with_local_speed`. This is the
actual generalized-gradient specialization of the speed estimate in
root `master05a.tex`, proof of `prop:sbr-finite-flow-existence`, around
lines 7827-7866 and equation `eq:sbr-limit-speed-bound`.

The standing hypotheses retain the actual Euler geometry and function:
the complete Riemannian manifold, explicit smooth metric g and
`IsMetricNorm g`, `LipschitzWith L F`, concavity along every native complete
intrinsic geodesic, compact `C = {z | 0 <= F z}`, an attained global maximum
m, `0 <= a < T < m`, and x with `F(x)=a`. The tangent-bundle Hausdorff
hypothesis of the frozen `SbrGradient` API is retained explicitly.

The output eta keeps the common `diam(C)/(m-T)` Lipschitz bound,
`eta(a)=x`, membership in C on `[a,T]`, and `F(eta(t))=t` there. For every
s in `[a,T)`, writing the actual vector

```text
G = intrinsicGeneralizedGradient g hEnorm hF hconc (eta s),
```

it additionally proves `G != 0`, strict positivity of its actual metric
length `sqrt(g.inner (eta s) G G)`, and for every `epsilon > 0`:

```text
eventually h in nhdsWithin 0 (Ioi 0),
  dist (eta(s+h)) (eta(s)) / h
    <= (sqrt(g.inner (eta s) G G)) inverse + epsilon.
```

The eventual neighborhood is chosen small enough that `s+h<T`, so the
statement concerns the actual interval curve, independently of its global
extension. It does not assume a curve, gradient field, speed bound,
nonvanishing gradient, or trajectory-existence result as replacement data.

## Proof route

The supplied maximum point q has `F(q)=m>s=F(eta(s))`.
`intrinsicGeneralizedGradient_ne_zero_of_lt` and
`intrinsicGeneralizedGradient_norm_pos_le_of_lt` therefore prove the
required nonvanishing and positive length.

`intrinsicGeneralizedGradient_unit_maximizer` supplies the actual normalized
direction `U = length(G) inverse • G`, whose metric length is one and whose
actual intrinsic right derivative equals `length(G)`. The metric
nonnegativity identity and `Real.sq_sqrt` convert the unit-length statement
to the `g.inner U U = 1` input of the Euler speed producer. These operations
use only the frozen public gradient API and explicit g.inner; this leaf
does not install a different tangent norm or any global instance.

For `r=length(G)>0`, the private arithmetic helper chooses
`a0=(r inverse + epsilon/2) inverse`. Then `0<a0<r` and
`a0 inverse < r inverse + epsilon`. The actual Euler local estimate gives
`dist(eta(s+h),eta(s)) <= h/a0` on a sufficiently small forward interval.
Intersecting that interval with `h<T-s` and dividing by the actual positive
h gives the public eventual quotient estimate.

## Verification and remaining obligation

All current evidence is source inspection only. The parent owns the
queued checks and refreshes for the Euler and gradient chains, then this
leaf's focused check and public axiom audit. Local absence of placeholders
does not establish checked or axiom-clean status.

An independent read-only source review checked the exact frozen gradient
signatures, square-root normalization, reciprocal rate, forward-neighborhood
cutoff, and quotient conversion. It found no concrete issue. This is source
review rather than compiler evidence.

The resulting eventual speed bound is the geometric input to the separately
assigned actual right-velocity identification. It must still be combined
with the exponential secant limits and the unique supporting/calibrated
gradient characterization to construct and identify a right derivative.
No curve derivative, normalized-gradient equation, uniqueness, contraction,
or full Sharafutdinov flow is asserted here.

# SbrFiniteFlow.lean

Verified 2026-09-08 in the dev checkout. Finite normalized ascent exists from actual Euler polygons: exact levels, initial point, compact containment, common Lipschitz bound and the actual normalized-gradient right manifold derivative are all produced, with no flow premise.

Empty focused output: 14.9s. Lint-clean named build: 17.2s.
Fresh external public axiom audit: 12.8s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrFiniteFlow-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Source-ready and frozen for the parent's verification queue, 2026-09-08.
This implements the bounded SbrFiniteFlow brief appended to
`SOUL_PLAN.md`. Chapter23 owns the compiler window; this worker remains
source-only. No Lean, Lake, REPL, check, build, artifact refresh, axiom
audit, root import, shared-plan/status edit, or commit was performed.

Claim retained: `f102297b-da7d-4679-a6a5-15f74e6ce9a6`.
Frozen source SHA256:
`5CFF39F71AF3E7496D9DE04CEBD7B26E904AC452506812A6143374799B31FB23`.
There is one public producer and one private affine-time derivative
helper, with no proof placeholders or axiom declarations. Compiler
verification and the public dependency audit remain pending.
`SbrGradientSpeed.lean` is unchanged at its frozen hash
`D229D30D791C42F0FE7B9B2C390699AFF692C5B03BF9D7B1ED496A34AE0805B9`.

## Actual finite-interval endpoint

`exists_finite_normalized_ascent_curve` assembles the existence part of
root `master05a.tex`, `prop:sbr-finite-flow-existence`. Its scope is an
actual finite normalized ascent curve on `[a,T]`; uniqueness, coherence
between different finite intervals, and extension to the maximum level
are separate subsequent obligations.

Inputs are the actual complete smooth Riemannian manifold, smooth metric
g with explicit `IsMetricNorm g`, `LipschitzWith L F`, concavity along all
native complete intrinsic geodesics, compactness of the actual set
`C = {z | 0 <= F z}`, an attained global maximum m, `0 <= a < T < m`, and
an actual point x with `F(x)=a`. The tangent-bundle Hausdorff hypothesis
required by the frozen gradient/metric-velocity APIs remains explicit.

The theorem produces one actual `eta : Real -> M` with:

- common Lipschitz bound `diam(C)/(m-T)`;
- `eta(a)=x`;
- `MapsTo eta (Icc a T) C`;
- `F(eta(t))=t` for every `t` in `[a,T]`;
- for every s in `[a,T)`, the actual vector
  `G=intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)` is nonzero,
  and eta has native right manifold derivative on `Ici s` at s equal to
  `ContinuousLinearMap.toSpanSingleton Real ((g.inner (eta s) G G) inverse • G)`.

The derivative is constructed, not an input. The global curve remains the
same Lipschitz extension supplied by the finite Euler-limit producer;
only its interval values and right germs at subterminal times carry the
stated ascent meaning. Global Lipschitz continuity immediately provides
the `ContinuousOn` input needed by the later comparison consumers.

## Assembly and time translation

`exists_nearest_superlevel_limit_with_gradient_speed` supplies the actual
eta, its nonzero gradient, exact levels, and sharp eventual metric speed.
For each fixed `s<T`, restrict positive h to `h<T-s`. The exact interval
levels give the required calibration

```text
F(eta(s+h)) = F(eta(s)) + h.
```

Distance symmetry converts the same eta's speed inequality to the
orientation used by
`hasMFDerivWithinAt_normalized_intrinsicGeneralizedGradient` in
`SbrMetricVelocity`. Applying that actual geometric producer to
`h -> eta(s+h)` gives its right manifold derivative on `Ici 0` at zero.
The normalization is the actual metric squared length of the actual
generalized gradient; no replacement field, support inequality, limiting
vector, chart inverse, derivative or trajectory is assumed.

The private translation helper uses the native derivative of `t -> t-s`
from `(hasFDerivAt_id s).sub_const s`. It maps `Ici s` to `Ici 0`.
Restating the outer derivative at `s-s` makes its center match this
translation. `HasMFDerivWithinAt.comp` and
`ContinuousLinearMap.comp_id` then transfer the derivative back to eta
on `Ici s` at s. The function equality is the actual affine cancellation
`s+(t-s)=t`; no coordinate derivative or tangent transport is assumed.

The derivative format is compatible with `SbrGradientContraction`:
the existing native equality
`ContinuousLinearMap.smulRight_one_eq_toSpanSingleton` identifies its
`(1 : Real ->L[Real] Real).smulRight V` with the returned
`ContinuousLinearMap.toSpanSingleton Real V`. No duplicate derivative
representation or new flow hierarchy is introduced.

## Verification and remaining work

This is source-written finite existence, not a verified endpoint.
The parent owns the remaining gradient/Euler/metric-velocity dependency
checks and refreshes, this file's focused check, and its public axiom
audit. Local placeholder absence supplies no compiler or axiom evidence.

An independent read-only review checked the current metric-velocity
signature, shifted calibration and speed, center equality, interval
mapping, composition, and public conclusion. It found no concrete issue;
this is source review rather than successful Lean elaboration.

The source search confirmed the exact native affine derivative, manifold
chain-rule, congruence, and derivative-map compatibility APIs. Global
coherence, uniqueness/comparison assembly, maximal-level continuation,
and the complete Sharafutdinov retraction remain outside this bounded
leaf.

## Resumed verification and warm-session trial, 2026-09-08

The affine helper fixes the inner time map explicitly in the chain rule,
uses explicit base-point rewrites, then `convert!` for the canonically
identical tangent models. No derivative or existence hypothesis was added.
The helper omits all unused geometric section assumptions. Initial cold
focused diagnostics took24.8s; imports loaded in13.109s; corrected whole
body checked in1.581s. A request-only `True.intro` replacement of the actual
right derivative was rejected in1.598s, followed by the corrected body from
the same import-only environment. Evidence is `warm-SbrFiniteFlow-r1` in
E:/lean-tools/soul-audits-20260907. Prefix/config/artifact stamps were guarded;
the own REPL and elaboration lock closed before the independent saved-file
check, named refresh and fresh public audit. No timing generalization is made.
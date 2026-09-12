# SbrEulerSpeed.lean

Verified 2026-09-08 in the dev checkout. Actual nearest mesh edges and uniform convergence give the sharp local bound dist(eta(s+h),eta(s)) <= h/a0 for every positive directional rate a0.

Empty focused output: 15.8s. Lint-clean named build: 18.5s.
Fresh external public axiom audit: 13.1s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrEulerSpeed-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Source-ready and frozen for the parent's verification queue, 2026-09-08.
This implements the SbrEulerSpeed brief appended to `SOUL_PLAN.md`.
The parent controls verification; this worker remains source-only. No
Lean, Lake, REPL, check, build, artifact refresh, axiom audit, root import,
shared-plan/status edit, or commit was performed for this leaf.

Claim retained: `26b5f7e8-4d9d-4ccc-920b-262fc20e2371`.
Frozen source SHA256:
`A29238758F90B02E2E2707EEEE1A160D8820D520B2922249466B8CDBD84D46B3`.
The source has one public producer and two private metric helpers, with
no proof placeholders or axiom declarations. Compiler verification and
the public dependency audit are pending. `SbrEulerLimit.lean` is unchanged
at its frozen hash
`5769B98D4462627CE81F20C5FCDF5214FCBBB361E5A9778D73DFD257B7B9CC46`.

## Actual public endpoint

`exists_nearest_superlevel_limit_with_local_speed` constructs an actual
limit from `exists_nearest_superlevel_euler_limit` and proves the local
speed estimate used in root `master05a.tex`, proof of
`prop:sbr-finite-flow-existence`, around lines 7827-7866. This is the
positive-rate estimate preceding `eq:sbr-limit-speed-bound`; it does not
yet identify the speed with the inverse norm of an actual generalized
gradient or construct the limiting right velocity.

The standing inputs are unchanged from the Euler-limit producer:

- the actual complete smooth Riemannian manifold, smooth metric g, and
  explicit `IsMetricNorm g`;
- actual `LipschitzWith L F` and concavity of F along every native complete
  intrinsic geodesic;
- compactness of `C = {z | 0 <= F z}` and an actual attained global maximum m;
- `0 <= a < T < m`, and an actual x with `F(x)=a`.

The output is one actual `eta : Real -> M` satisfying the common
`diam(C)/(m-T)` Lipschitz bound, `eta(a)=x`, compact containment on `[a,T]`,
and exact levels `F(eta(t))=t`. For this same eta it proves:

```text
for every s in [a,T), every v in TangentSpace I (eta s)
with g.inner (eta s) v v = 1, and every rate a0 satisfying
  0 < a0 < intrinsicRightDerivative g hEnorm F (eta s) v,
there exists delta > 0 such that
  0 < h < delta and s+h <= T
imply
  dist (eta(s+h)) (eta(s)) <= h/a0.
```

Neither eta nor a nearest-polygon family is an input to this public
producer. The same eta works for all indicated points, unit directions,
and positive rates. Its inherited global extension outside `[a,T]` has
no asserted flow meaning.

## Proof and retained geometric content

The proof extracts the actual node family, minimizing-vector family,
polygon family, strict subsequence, and mesh convergence from
`SbrEulerLimit`. It applies the metric helper to the actual subsequence
with `N(n)=phi(n)+1`. The helper retains the exact node levels, native
nearest-superlevel `IsMinOn` property, exact node interpolation, common
polygon Lipschitz bound, and convergence. A bare Lipschitz curve with
calibrated levels would not suffice for the helper.

For the actual unit vector v and rate a0,
`exists_local_superlevel_step_of_positive_direction` constructs an open
starting neighborhood U and uniformly short candidate steps with level
gain at least tau and distance at most `tau/a0`. This hypothesis of the
private metric helper is thus discharged by the native geometric producer,
not assumed at the public endpoint.

A small ball about `eta(s)` is contained in U. The common polygon
Lipschitz constant, convergence at s, and shrinking mesh put every nearby
mesh node in this ball. For every relevant edge, its exact initial level
and the candidate's level gain make that candidate lie in the actual
next superlevel. The actual node's nearest-point minimality then gives
the edge bound `mesh/a0`.

Native `Nat.floor` estimates choose the last mesh node at or before each
endpoint. `dist_le_Ico_sum_of_dist_le` sums the actual edge bounds. The
original polygon Lipschitz estimate bounds each partial endpoint error by
`K*mesh`. Flooring both endpoints allows one extra mesh in the span, so
the exact prelimit estimate used here is

```text
dist (polygon(n,s+h)) (polygon(n,s))
  <= h/a0 + (2*K + 1/a0)*mesh(n).
```

The extra `mesh/a0` is a harmless finite-mesh overshoot. It avoids a second
ceil/floor case split while producing exactly the requested sharp bound
after passage to the limit. The book's tighter `2*K*mesh` prelimit error
is not claimed. This source route preserves the actual nearest nodes and
their constructed broken geodesics; it reuses their already-proved global
Lipschitz bound instead of repeating a local gluing proof.

Pointwise distance convergence at s and s+h, mesh convergence, and native
closed-order limit comparison remove the entire error. No derivative of
eta, smoothness of F, or continuity of a generalized gradient is used.

## Verification boundary and remaining work

All evidence remains source inspection only. The parent owns the queued
checks and refreshes for `SbrEulerPolygons`, `SbrEulerLimit`, `SbrDirectional`,
and `SbrLocalStep`, then this leaf's check and public axiom audit. No
checked or axiom-clean status is inferred from local placeholder absence.

An independent read-only source review found two mechanical API issues:
the finite triangle-sum helper's implicit index binder and the explicit
center argument of `Metric.ball_mem_nhds`. Both are repaired in the
frozen source. No further mathematical gap was identified in the node
neighborhood argument, nearest-edge transfer, finite sum, or existence
assembly. This is source review, not compiler evidence.

The remaining velocity argument must combine these actual short-increment
bounds with the generalized-gradient characterization and exponential
secant limits. Existence/uniqueness of an actual right derivative, its
normalized-gradient identity, trajectory uniqueness, contraction, and the
final Sharafutdinov flow are not asserted here.

# SbrEulerPolygons.lean

Verified 2026-09-08 in the dev checkout. Actual nearest-superlevel Euler polygons, uniform metric Lipschitz control and mesh-proportional level error are produced; no limiting flow is claimed yet.

Empty focused output: 15.6s. Lint-clean named build: 18.8s.
Fresh external public axiom audit: 12.9s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrEulerPolygons-result3.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Source-ready and frozen for the parent's verification queue, 2026-09-08.
This is the bounded SbrEulerPolygons source brief at the end of
`SOUL_PLAN.md`. Chapter23 owns verification. This worker has performed no
Lean, Lake, REPL, check, build, artifact refresh, axiom audit, root import,
shared-plan/status edit, or commit for this leaf.

Claim retained: `220d9743-45cd-43c6-a8ea-8a14d1ca2ffd`.
Frozen source SHA256:
`C9E6C0F15C3BA72132C294A0C9DBB318549E2C235A6B1AD88AB778357544A24F`.
The source has one public producer and four private analytic/geometric
helpers, with no proof placeholders or axiom declarations. Compiler
verification and the public dependency audit remain pending.

## Actual construction and public result

`exists_nearest_superlevel_euler_polygon` constructs the uniform-mesh
version of the Euler polygons in root `master05a.tex`, the proof of
`prop:sbr-finite-flow-existence`, lines 7785-7823. Its scope is the actual
polygon construction, equation `eq:sbr-polygon-node-level`, the common
Lipschitz estimate `eq:sbr-polygon-equicontinuity`, and the prelimit level
error. It does not prove the full finite-flow-existence proposition.

The inputs are the native complete Riemannian-manifold setup from
`SbrNearestStep`, a smooth metric `g` with explicit `IsMetricNorm g`, the
actual function `F : M -> Real`, and:

- `LipschitzWith L F`, with `L : NNReal`;
- concavity of `F` along every actual `intrinsicGeodesic g hEnorm p v`;
- compactness of the actual set `C = {z | 0 <= F z}`;
- an attained global maximum `exists q, F(q)=m and forall z, F(z)<=m`;
- `0 <= a < T < m`, an actual point `x` with `F(x)=a`, and `N > 0`.

Write `mesh=(T-a)/N`, `time(i)=a+i*mesh`, and
`K=diam(C)/(m-T)`. The public Lean statement represents the nonnegative
constant by `Real.toNNReal`; the proof establishes its real coercion is
exactly this quotient. It produces actual objects

```text
node : Nat -> M
v : forall i, TangentSpace I (node i)
curve : Real -> M
```

with all of the following:

- `node(0)=x` and `F(node(i))=time(i)` for every `i<=N`;
- every such node belongs to the actual compact set `C`;
- for `i<N`, the next node is a native `IsMinOn (dist (node i))`
  point of `{z | time(i+1)<=F(z)}`, and its step distance is at most
  `K*mesh`;
- each `v(i)` is an actual minimizing-exponential vector:
  `intrinsicGeodesic g hEnorm (node i) (v i) 1 = node(i+1)` and its
  metric speed `sqrt(g.inner (node i) (v i) (v i))` equals that distance;
- `LipschitzWith K curve`, `curve(a)=x`, and exact interpolation
  `curve(time(i))=node(i)`;
- on every closed mesh interval `[time(i),time(i+1)]`, the curve is
  exactly the native geodesic with affine parameter
  `intrinsicGeodesic g hEnorm (node i) (v i) ((t-time(i))/mesh)`;
- the curve maps `[a,T]` into `C`, and for every `t` in this interval,
  `t <= F(curve(t)) <= t + L*K*mesh`.

The natural-number node extension beyond `N` and the curve extension
outside `[a,T]` are construction conveniences. Their values are not used
as polygon data. All node and piece conclusions retain their actual
`i<=N` or `i<N` bounds. The global curve is constant to the left of `a`
and follows the last complete geodesic after `T`; compact containment is
asserted only on `[a,T]`.

## Proof route and native dependencies

The node family is produced by `Nat.rec`, starting at `x`. Each valid
successor is selected from the actual existential conclusion of
`exists_nearest_superlevel_step`. Guards make this a total recursion;
induction proves the exact node levels, which in turn discharges every
successor's guard. No node sequence or nearest-point selector is assumed.

`minExp_of_ne_top` produces every joining vector. Its native Riemannian
extended distance is identified with the actual metric distance using
`IsRiemannianManifold.out`. The speed bound for the affine segment uses
`sqrt_gInner_smul_self`, `intrGeo_smul_apply`, and
`intrinsicGeodesic_riemannianEDist_le`; it introduces no replacement
metric norm or tangent-space structure.

A private finite-gluing lemma joins globally K-Lipschitz real-parameter
curves which agree at the cut. The cross-cut case is the triangle
inequality through their shared point. Induction over the actual mesh
preserves endpoint values, every earlier piece formula, and the level
estimate. This avoids assuming a polygon or hiding the gluing in a new
geometric hierarchy.

Geodesic concavity supplies the lower bound by interpolation between the
two exact node levels. The actual F Lipschitz estimate and the segment
distance bound give `F(segment(t)) <= time(i)+L*K*mesh`, hence the stated
uniform upper bound. In particular, containment in C is derived from
`0<=a<=t<=F(curve(t))`.

## Handoff boundary

`SbrNearestStep` is source-written in the parent's verification queue;
the parent must check and refresh it before checking this new import.
This leaf has received source inspection, including an independent
read-only review of the recursion guards, native speed rescaling, gluing
endpoints, and level interpolation. That review found no concrete issue;
it is not compiler evidence. No checked or axiom-clean status is claimed.

A later compactness producer can take `N` tending to infinity, use the
common Lipschitz bound and compact containment to extract an actual
uniform limit, and deduce the exact limit level from the error estimate.
That requires an Arzela-Ascoli/subsequence argument which is not included
here. A limiting right velocity, identification with the normalized
generalized gradient, uniqueness, contraction, and the final flow remain
separate obligations. Compact convergence alone supplies none of these
velocity or gradient conclusions.

## Resumed verification and warm-session trial, 2026-09-08

The source repair renames the reserved parser word `prefix`, unfolds the local
node selector explicitly, and uses the same geodesic's distance bound under
affine reparametrization. No hypothesis or output was weakened. Initial cold
focused check failed in16.6s. The import-only REPL environment loaded in13.159s;
the corrected full saved body checked in2.71s. A request-only substitution of
`True.intro` for compact containment was rejected in2.434s, then the unchanged
saved body passed from the same pre-target environment. Evidence is the fresh
`warm-SbrEulerPolygons-r1` directory outside the checkout. The runner guards
prefix/config/native artifact stamps and holds the wrapper's elaboration lock.
An attempted independent verification was correctly blocked by the live-worker
guard before starting any compiler (result2); the owned REPL was then closed
and its lock released before the independent result3 acceptance sequence.
These timings are for this target only; no chapter-wide speedup is inferred.
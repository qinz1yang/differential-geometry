# SbrEulerLimit.lean

Verified 2026-09-08 in the dev checkout. Actual Arzela-Ascoli subsequence and compact Euler limit retain all nearest-node witnesses and prove exact levels, initial value and uniform Lipschitz control.

Empty focused output: 13.8s. Lint-clean named build: 16.2s.
Fresh external public axiom audit: 12.2s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrEulerLimit-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Source-ready and frozen for the parent's verification queue, 2026-09-08.
This implements the bounded SbrEulerLimit brief appended to
`SOUL_PLAN.md`. The parent owns the exclusive verification window; this
worker remains source-only. No Lean, Lake, REPL, check, build, artifact
refresh, axiom audit, root import, shared-plan/status edit, or commit was
performed for this leaf.

Claim retained: `68571edf-b1c1-463a-a22a-763980d16d30`.
Frozen source SHA256:
`5769B98D4462627CE81F20C5FCDF5214FCBBB361E5A9778D73DFD257B7B9CC46`.
The source contains one public theorem and no proof placeholders or axiom
declarations. Its own compiler check and public dependency audit are
pending. `SbrEulerPolygons.lean` remains unchanged at its frozen hash
`C9E6C0F15C3BA72132C294A0C9DBB318549E2C235A6B1AD88AB778357544A24F`.

## Public statement and actual witnesses

`exists_nearest_superlevel_euler_limit` proves the compact-limit part of
root `master05a.tex`, proof of `prop:sbr-finite-flow-existence`, around
lines 7785-7823, including the exact identity `eq:sbr-limit-level`. It
does not establish the full normalized-flow proposition.

Its geometric and function inputs are exactly those of
`exists_nearest_superlevel_euler_polygon`:

- the actual complete smooth Riemannian manifold, smooth metric `g`, and
  explicit `IsMetricNorm g`;
- `LipschitzWith L F`, with `L : NNReal`, and concavity of F along every
  native complete `intrinsicGeodesic g hEnorm p v`;
- compactness of `C = {z | 0 <= F z}`;
- an actual attained global maximum m;
- `0 <= a < T < m` and an actual point x with `F(x)=a`.

There is no polygon, convergence, limit, derivative, or gradient premise.
For every k, the proof calls the polygon producer with `N=k+1`. Writing

```text
mesh(k) = (T-a)/(k+1)
time(k,i) = a + i*mesh(k)
K = diam(C)/(m-T), represented by Real.toNNReal in LipschitzWith
```

the result retains actual output data

```text
node : Nat -> Nat -> M
v : forall k i, TangentSpace I (node k i)
polygon : Nat -> Real -> M
phi : Nat -> Nat
eta : Real -> M
```

For every k, it retains every conclusion of the original polygon producer:
the initial node, exact node levels, membership in C, each next node's
native `IsMinOn` nearest-superlevel property and step bound, the actual
minimizing exponential vectors and their metric speeds, the common global
Lipschitz bound, initial curve value, exact node interpolation, and the
exact affine native geodesic formula on each closed mesh interval. It also
retains compact containment and the full prelimit inequality
`t <= F(polygon(k,t)) <= t + L*K*mesh(k)` on `[a,T]`.

For these same chosen witnesses, the result then proves:

- `StrictMono phi`;
- the actual subsequence mesh `mesh(phi(n))` tends to zero;
- native `TendstoUniformlyOn (fun n => polygon (phi n)) eta atTop (Icc a T)`;
- `LipschitzWith K eta` and `eta(a)=x`;
- `MapsTo eta (Icc a T) C`;
- for every `t` in `[a,T]`, `F(eta(t))=t`.

The whole family is output, with the explicit strict subsequence index;
later proofs can access `node (phi n) i` and `v (phi n) i`. No node
information is discarded by passing only a bare limit curve downstream.

## Native compactness and limit argument

Each polygon is restricted to the compact subtype `Icc a T` and packaged
as a native continuous map. The common Lipschitz bound gives uniform
equicontinuity through `LipschitzWith.uniformEquicontinuous`. The existing
`DifferentialGeometry.Analysis.arzela_subseq_cpt` in
`Analysis/Calculus/ArzelaAscoli.lean:228` supplies a strict subsequence and
uniformly convergent continuous-map limit. This reuses the project's
actual compact Arzela-Ascoli producer; no replacement compactness
principle or assumed convergent family is introduced.

Pointwise distance convergence passes the common Lipschitz bound to the
limit. The interval limit is extended to `Real` by the native
`Set.projIcc a T haT.le`, which is 1-Lipschitz. This yields a global
K-Lipschitz extension constant before a and after T. Only the interval
values carry geometric level and trajectory meaning. Projection is the
identity on the interval subtype, giving the stated native uniform-on
convergence of the original polygons.

The shared initial values identify `eta(a)` by uniqueness of limits.
Closedness of the actual compact set C passes containment to eta. The
native inverse-natural-number limit proves the meshes, and hence the
level errors along the strict subsequence, tend to zero. Continuity of F
passes the polygon values to `F(eta(t))`; the two one-sided bounds then
give the exact level identity by order-closed limit comparison.

## Verification and remaining obligation

All current evidence is source inspection only. The parent must first
check/refresh the queued nearest-step and polygon dependencies, then
check this leaf and audit its public theorem. No compiler or axiom-clean
status is inferred from the lack of local placeholders.

An independent read-only review checked the native compactness API,
projection conversion, preservation of the witness family, subsequence
mesh limit, pairwise-distance limit, and exact-level squeeze. It found no
concrete issue; this is source review rather than compiler evidence.

This proves a compact limit candidate with exact levels. Identifying an
actual right velocity requires the separate local-step, secant, and
generalized-gradient argument. No limiting derivative, normalized
gradient equation, uniqueness, contraction, or level-map flow is claimed
from uniform convergence alone. The retained nearest nodes, minimizing
vectors, affine formulas, and mesh convergence are the inputs to that
remaining argument.

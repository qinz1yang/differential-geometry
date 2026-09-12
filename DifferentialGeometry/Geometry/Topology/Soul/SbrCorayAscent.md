# SbrCorayAscent.lean

Verified 2026-09-08 in the dev checkout. A unit direction attaining value one is the actual generalized gradient; reversed calibrated corays satisfy the actual normalized ascent equation before their prescribed terminal point.

Empty focused output: 19.7s. Lint-clean named build: 22.4s.
Fresh external public axiom audit: 17.1s; all 2 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrCorayAscent-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Status: source-ready, not compiler-verified. This bounded leaf follows the
`SbrCorayAscent` brief at the end of `../SOUL_PLAN.md`. Earlier delivered
leaves are frozen. Chapter 23 owns the compiler window; the parent owns
focused verification, artifact refresh, audit, imports and integration.

Parent continuation 2026-09-08: the two local metric instances now use
the current `let` syntax required by the compiler's style checks, following
the already verified SbrGradient repair. No mathematical statement or
instance scope changed. The historical source blob below is superseded;
compiler verification is still pending.

Claim: `fb7f7b02-69a3-4229-b313-f1f5a7e71fb0`, obtained from the external
`E:/testdifferential-geometry/scripts/lake-locked.ps1` wrapper from the dev
checkout. Retain it for the parent's verification handoff.

## Public results

1. `intrinsicGeneralizedGradient_eq_of_unit_value`: for the actual
   intrinsic generalized gradient of a one-Lipschitz, geodesically concave
   function, a tangent vector `U` with `g.inner p U U = 1` and actual
   intrinsic right directional derivative equal to one satisfies
   `intrinsicGeneralizedGradient ... p = U`.
2. `exists_busemann_reversed_coray_ascent`: given an actual isometric ray
   `c`, a point `p` with `busemann c p < C`, and actual Lipschitz and
   geodesic-concavity proofs for `F(q) = C - busemann c q`, construct a unit
   `u` in the actual tangent fiber at `p`. Set `T = C - busemann c p`,
   `gamma = intrinsicGeodesic g hEnorm p u`, and
   `delta(s) = gamma(T-s)`. The conclusion supplies global smoothness of
   `delta`, `b(delta(0)) = C`, `delta(T) = p`, `F(delta(s)) = s` on
   `[0,T]`, and distance preservation on that interval. For `s` in
   `[0,T)`, the actual gradient at `delta(s)` equals the actual curve
   velocity, has metric squared norm one, and its normalized velocity
   is the curve's actual `HasMFDerivWithinAt` on `Ici s` at `s`, represented
   by `ContinuousLinearMap.toSpanSingleton`.

## Proof mechanism and provenance

The unit-value identification captures the native gradient support and
metric-length bound before locally installing the actual metric's inner
product on the same tangent fiber and topology. It then applies the
verified algebraic `superadditive_gradient_eq_of_unit_value` from
`SbrGradientVelocity`, with slope bound one. The local metric transport
is the same `toNormedAddCommGroupOfTopology` / `ofCoreOfTopology` route
used by `SbrGradient`. There is no new global metric-norm instance or
replacement tangent representation.

The geometric curve comes from the frozen
`SbrCorayDirection.exists_busemann_reversed_coray`. Its actual unit
velocity and directional value one give the gradient identity through
the first result. Squared norm one makes its normalized gradient equal
to that velocity. The native linear-map identity
`ContinuousLinearMap.smulRight_one_eq_toSpanSingleton` converts the
already produced manifold right derivative to the chosen public
representation. The construction matches the reversed-coray argument in
`master05a.tex`, Chapter 8, around lines 8225 onward.

No directional derivative of `F` at the terminal time `s = T` is claimed.
The terminal point is supplied by the smooth intrinsic curve itself;
no backwards nonsmooth flow, trajectory, contraction, or gradient
identity is assumed as an input.

## Exact remaining inputs and verification

The endpoint keeps the actual manifold/metric completeness assumptions
of the coray and intrinsic-gradient APIs. The complement's one-Lipschitz
bound and concavity along every complete intrinsic geodesic remain
explicit proofs tied to `F = C - busemann c`; the nonnegative-curvature
caller supplies those. Comparison with the chosen ascent curve and
surjectivity of a level map remain downstream work.

Imports `SbrCorayDirection`, `SbrGradient`, and `SbrGradientVelocity` use
their current native source signatures. The last has a completed
verification triple; the parent tracks the first two in its frozen
verification queue. This leaf has not run Lean, Lake, REPL, a focused
check, a build, or an axiom audit. No compiler errors are yet known;
source-only review is not evidence of elaboration or artifact freshness.

Static review: two public theorems, no private declarations, all three
import paths present, and zero forbidden-token or trailing-whitespace
matches. Frozen source blob:
`84cdfb2efec9031a6b06660409010c03c1b770b8`.

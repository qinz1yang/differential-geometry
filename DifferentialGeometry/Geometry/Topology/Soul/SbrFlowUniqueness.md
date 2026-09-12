# SbrFlowUniqueness.lean

Verified 2026-09-08 in the dev checkout. The actual constructed generalized gradient supplies contraction and fixed-point comparison; equal initial points and calibrated levels imply uniqueness on closed intervals and overlap agreement.

Empty focused output: 15.1s. Lint-clean named build: 17.5s.
Fresh external public axiom audit: 14.3s; all 4 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrFlowUniqueness-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

## Scope, claim, and verification state

Assigned to `soul_distance_field` by the bounded Ch8 source brief in
`SOUL_PLAN.md`, 2026-09-08. Claim
`e3a859d8-7f9a-4b77-8884-2519a7cfa3ae` was acquired through
`E:/testdifferential-geometry/scripts/lake-locked.ps1` from the dev checkout.
The claim is retained for the parent's verification and integration.

Source-ready only: four public declarations, no helper definition or private
theorem. Chapter23 owns the compiler window. This worker ran no Lean, Lake,
REPL, check, build, refresh, or axiom audit, and made no root registration,
shared status/plan edit, earlier-leaf edit, or commit. No compiler feedback
exists for this leaf yet. Earlier delivered source remains frozen.

Static freeze: source Git blob `455652d9771d9b9de858964bc15b6a51aa31fcae`;
both source imports exist; no forbidden tokens or trailing whitespace;
source parentheses balance. These checks do not establish Lean verification.

Book scope: the actual-gradient instances of
`lem:sbr-two-flow-contraction` and `lem:sbr-flow-to-fixed-point`, then
`cor:sbr-flow-uniqueness` at `master05a.tex:7667-7677`. The finite-interval
overlap conclusion supplies the agreement step at the beginning of the
proof of `thm:sbr-maximal-flow` near line 7908. The curve-existence and
maximal-time constructions remain separate.

## Native common inputs

Every public declaration uses the actual
`intrinsicGeneralizedGradient g hEnorm hF hconc`. Its inputs are the given
smooth compatible metric, `hF : LipschitzWith L F`, and concavity of `F`
along every actual complete intrinsic geodesic. The complete geometric
context is retained from `SbrGradient`, including finite positive model
dimension, the boundaryless model, sigma-compactness, continuous Riemannian
bundle, and the actual tangent-bundle Hausdorff hypothesis. No compact set,
curvature, attained maximum, or nonzero-gradient premise is needed for
these comparisons.

Curve right derivatives are exposed exactly as in `SbrMetricVelocity` and
the pending finite-flow producer. For a curve `xi`, the input at each
`t ∈ Ico a b` is

```lean
let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
  (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G))
```

This is the actual tangent vector and linear derivative map. The derivative
is required only before the terminal time, while continuity is supplied on
the whole closed interval. There is no assumed supporting tangent field,
angle inequality, smoothness of the generalized gradient, or trajectory
existence package in any public statement.

## Public declarations

All four are in `DifferentialGeometry.Geometry.Topology`, with common
explicit arguments `g hEnorm hF hconc` preceding their curve data.

- `antitoneOn_dist_normalized_intrinsicGeneralizedGradient`: two continuous
  curves with the displayed actual right derivatives and
  `F (xi t) = F (zeta t)` for `t ∈ Ico a b` have
  `AntitoneOn (fun t => dist (xi t) (zeta t)) (Icc a b)`.
- `antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient`: for one
  such curve and a fixed `q` with `F (xi t) ≤ F q` before the terminal
  time, `AntitoneOn (fun t => dist (xi t) q) (Icc a b)`.
- `eqOn_normalized_intrinsicGeneralizedGradient_curves`: the same two-curve
  assumptions and `xi a = zeta a` imply `EqOn xi zeta (Icc a b)`. Equal
  function values suffice; the stronger actual calibration `F(xi t)=t`
  and `F(zeta t)=t` is not redundantly required here.
- `eqOn_normalized_intrinsicGeneralizedGradient_overlap`: one supplied
  curve on `Icc a b₁`, another on `Icc a b₂`, their actual right
  derivatives on the respective half-open intervals, separate exact level
  calibrations `F(xi t)=t` and `F(zeta t)=t`, and a common initial point
  imply `EqOn xi zeta (Icc a (min b₁ b₂))`.

The last result explicitly supplies finite-interval compatibility without
assuming an existing compatible curve family. It is obtained by restricting
the supplied continuity, right derivatives, and level equations to the
actual intersection interval, then applying the uniqueness result.

## Support instantiation and derivative representation

The support premise in each existing comparison consumer is discharged by
`(intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1`. No supporting
vector is assumed or selected again in this leaf. The actual directional
and gradient constructions remain the ones in `SbrDirectional` and
`SbrGradient`.

Native Mathlib already proves the exact representation bridge

```lean
ContinuousLinearMap.smulRight_one_eq_toSpanSingleton
```

in `Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`. It identifies
`(1 : ℝ →L[ℝ] ℝ).smulRight v` with `toSpanSingleton ℝ v` and is proved by
`rfl`. The comparison proofs use this equality in the reverse direction
through `HasMFDerivWithinAt.congr_mfderiv`. Thus the public derivative
premises match the velocity producer, and their conversion to the existing
comparison API is proved internally without adding a representation input
or duplicating a continuous-linear-map definition.

The uniqueness proof evaluates the actual antitone distance at a time
`t ∈ Icc a b` and compares it with its zero initial value. Metric
nonnegativity then forces distance zero and hence equality. This includes
the terminal point; no derivative there is assumed. Degenerate and empty
intervals need no extra argument or hypothesis.

The local tangent-space normed instances mirror the existing actual-gradient
and metric-velocity leaves. No global instance or public metric changes.

## Verification and remaining scope

Read `SbrGradient.md`, `SbrMetricVelocity.md`, `SbrGradientContraction.md`,
their actual declarations, the native continuous-linear-map representation
identity, and the relevant book proof before implementation. Static review
found no mathematical gap in this bounded instantiation/uniqueness route;
elaboration and lint feedback remain pending.

Parent order: verify and refresh the actual gradient chain and
`SbrGradientContraction`, then this leaf, followed by its named refresh and
fresh audit of all four public declarations. This leaf need not import the
Euler-limit or metric-velocity existence producer: it shares their exact
derivative output type and consumes explicit curve data.

The actual finite trajectories, their continuity, right derivatives, and
level calibration still come from the separate geometric existence chain.
Given those data, no support or endpoint-angle input remains in the
uniqueness statements. This source does not construct the maximal curve,
prove its endpoint limit, define a flow/level map, or claim Sharafutdinov
surjectivity or coherence.

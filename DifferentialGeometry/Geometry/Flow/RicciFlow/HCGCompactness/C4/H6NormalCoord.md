# H6NormalCoord

## Purpose

This module is the native producer boundary between radial Jacobi estimates
and the Chapter-4 `NormalCoordMetricBoundInput` API. It must not introduce a
replacement geometric assumption.

## Status

Implementation resumed on 2026-07-18. The public `normalCoordMetric` now is the
canonical orthonormally framed pullback metric. `H6NormalCoord.lean` records its
exact endpoint-Jacobi formula and converts two-sided framed Jacobi estimates to
`NormalCoordMetricEquivOn`; the obsolete raw-coordinate aliases were removed.

`Geometry/Exponential/NormalFrame.lean` now constructs, at every center `x`, a
chosen continuous linear equivalence `normalFrame : E ≃L T_xM` and proves

`g_x(normalFrame v, normalFrame w) = <v,w>`.

`Geometry/Exponential/FramedNormalCoordinates.lean` defines the genuine
normal chart `z |-> exp_x(normalFrame z)`, its inverse, its differential, and
the exact equivalence between model balls and `g_x` tangent balls. The public
`normalCoordMetric` is the pullback metric of that chart, equals `innerSL Real`
at the center, and is the endpoint Gram form of radial Jacobi fields launched
through the same frame. Its framed Jacobi API consumes the intrinsic
`expRadiusGp` rather than the raw `expMapC2Radius`.

The first shared migration brick is now checked: `injRadius` measures
injectivity of the actual global framed exponential map. The two raw
`expMapDiffeo` source helpers needed by the Gauss radius layer retain their
legacy explicit instance signature in an isolated section, avoiding the
`NormedSpace` instance diamond. `ExpBallDiffeo` has been rewritten against the
same framed map and its focused check passes. `StepBInputs.normalTransition`
now delegates to the same generic `framedTransition`; the full Step-B input
file also passes a focused check after keeping its raw chart-inverse proof
pointwise rather than calling the newly framed ExpBall theorem.

The local zero-order producer is now checked. `exists_equiv_ball` uses
smoothness of the framed pullback metric and
`normalMetric_zero = innerSL Real` to choose, for each center, a positive radius
inside `expRadiusGp` on which the metric satisfies the exact H6 half/two
Euclidean comparison. This proof does not use Rm04 and makes no sequence-uniform
claim.

`exists_equiv_radii` packages those per-center choices for an entire pointed
sequence and is focused- and target-green. Its radius still depends on both `k` and `x`;
this is useful pointwise data, but it does not change the quantifier-order gap
for `NormalRadiusProfile`.

The quantitative zero-order producer is now focused- and target-green. `FramedRm04Bound`
states the radial Rm04 bound on the explicit
`framedJacobiRadius = expRadiusGp / 26`; `framed_rm04_of_seq` supplies it from
`SeqBoundedGeometry.C 0`. `framed_rm04_bounds` proves arbitrary-vector endpoint
bounds, including the required positive rescaling of each launch direction.
Finally, `exists_rm04_radii` chooses one sequence-independent `r0 > 0`, makes
the scalar Gronwall error at most one quarter, and proves
`NormalCoordMetricEquivOn` on
`ball 0 (min (framedJacobiRadius Y x) r0)` for every sequence member and every
center. There is no new geometric assumption or endpoint wrapper in this
chain.

## Corrected feasibility diagnosis

The old raw-coordinate feasibility diagnosis is obsolete. The current
`normalCoordMetric Y x` uses `normalFrame`, and at the origin
`normalMetric_zero` gives

`normalCoordMetric Y x 0 = innerSL Real`.

Consequently local coercivity follows from continuity. What does not follow
from this pointwise argument is the quantifier order required by
`NormalRadiusProfile`: one fixed positive ratio must work for every sequence
member and every center after multiplication by the CGT decay profile.

The Jacobi/Rm04 and scalar-budget portions of the zero-order producer are no
longer frontiers. The remaining quantifier-order gate is the pointwise clamp
`framedJacobiRadius Y x = expRadiusGp Y.metric x / 26`. The current
`expRadiusGp` contains `expMapC2Radius`, which is a qualitatively chosen local
inverse radius. CGT injectivity cannot lower-bound that arbitrary choice.

There is a second independent quantifier issue in the current record boundary.
`NormalCoordMetricBoundInput.radius` is downward closed: any valid record can
be restricted to an arbitrarily smaller positive radius. Consequently a
positive `NormalRadiusProfile.ratio` cannot be produced for an arbitrary
supplied `hb`; H6 must choose the controlled radius together with the metric
bound record (or return a combined bounds/profile package). The profile is not
a post-processing theorem about the current unconstrained record.

`InjectivityRadius.exp_dom_of_inj_rad` now closes the first canonical-branch
subproblem: every vector in a framed model ball strictly below `injRadius`
belongs to the natural `expDomain`. This uses injectivity against the origin
and the totalized exponential's center value outside its domain. It does not
put the ball in the selected `framedExpDiffeo.source`.

The finite-time smooth-flow gate is now closed at source level. The exact-green
generic theorem `ODE.flow_slice_smooth` propagates smooth dependence along a
compact reference trajectory. `Exponential.lift_isIntegral` identifies the
complete intrinsic velocity lift with the globally smooth basepoint-free
spray, `velocityLift_one` proves its time-one slice is globally smooth, and
`intrinsicExp_smooth` projects this to the complete intrinsic exponential; the
whole continuation/identification module is focused- and exact-green.
The H6 branch no longer needs to upgrade the old long finite chart-chain
continuity proof. `intrinsic_jacobi` and `intrinsic_jacobi_one` now give the
global intrinsic Jacobi equation and the exact time-one differential identity.
The remaining native gate is architectural: the ordinary framed exponential
used by `injRadius` and `expRadiusGp` is chart-fixed, while CGT and the new
Jacobi API control the intrinsic exponential. A canonical migration or a
single justified geometric-branch design is required before Rm04 and
injectivity can construct the radius-controlled partial diffeomorphism. Do not
replace it by an endpoint wrapper or synonym assumption on
`NormalRadiusProfile`.

## Honest progress

- Per-center orthonormal normalizer and exact radial norm correspondence: 100%
  proved and checked.
- Framed chart, inverse chart, differential, pullback metric, and framed Jacobi
  bridge: 100% proved and checked.
- Per-center zero-order `NormalCoordMetricEquivOn` producer theorem: 100%
  proved and focused-checked.
- Sequence-wide pointwise radius-choice theorem: 100% proved and
  focused-checked; it deliberately makes no uniform lower-bound claim.
- Sequence-uniform clamped zero-order metric producer: 100% proved and
  target-checked. It gives one curvature radius `r0`, but still intersects it
  with the pointwise `framedJacobiRadius`.
- Sequence-uniform relative-radius/profile theorem: 0%; its dedicated
  zero-order Jacobi/Rm04 machinery is about 99%. Natural-domain containment,
  global spray smoothness, intrinsic-lift identification, and smooth time-one
  dependence plus the intrinsic Jacobi endpoint differential are proved. The
  Route-A-plus-Route-C architecture is now fixed, and its first intrinsic framed
  migration brick is focused-green. The remaining zero-order gap is the single
  intrinsic local branch, canonical name/radius migration, and final H6 choice
  of bounds together with its profile; the profile cannot target an arbitrary
  shrinkable bounds record.
- Native all-order `NormalCoordMetricBoundInput` producer theorem: 0%; its
  dedicated machinery is about 35%, because the high-order curvature-to-metric
  jet induction has not been formalized.
- Unconditional MSM135 Theorem 3.9: 0%. Conditional Theorem 3.9 remains 100%;
  whole HCG compactness machinery remains about 60%.

## Next target

The canonical architecture in `H6_RADIUS_CONSULT.md` is resolved as Route A
plus Route C. Geometry Stages 1--3 are focused- and exact-green in
`Geometry/Exponential/IntrinsicFramedCoordinates.lean`: the total intrinsic
framed map, its migration-only local partial diffeomorphism, and its total-map
pullback metric are implemented, including local agreement with the legacy
objects. The next target is the HCG completeness boundary. The intrinsic map
requires `[CompleteSpace M]`, while the current `normalCoordMetric Y x` and
`NormalCoordMetricBoundInput` do not carry `MetricComplete Y`; this dependency
must be threaded or packaged honestly before switching the existing public
metric name. After that, flip the canonical framed names and make injectivity
and `expRadiusGp` intrinsic. H6 must finally choose its metric-bound record and
relative profile together. Higher coordinate derivatives remain a separate
curvature-jet induction.

## Migration audit

The minimal canonical migration is not a new parallel API:

1. `Geometry/Comparison/InjectivityRadius.lean` must measure injectivity of
   `z |-> exp_x(normalFrame z)` on model balls, equivalently `exp_x` on
   intrinsic `g_x` tangent balls.
2. `Geometry/Comparison/ExpBallDiffeo.lean` must restrict that same framed
   exponential map, not the raw model identification.
3. `C4/StepBInputs.lean` should retain its public HCG names but redefine
   `normalCoordMetric` through `framedExpDiffeo` and `normalTransition` through
   the checked generic `framedTransition`.
4. Downstream B/C files should then need proof-shape repairs rather than new
   hypotheses. The existing raw formulas remain useful only as implementation
   lemmas relating framed coordinates to the underlying tangent-fiber map.

The generic frame, chart, transition, radial-ball, differential, and pullback
identities are now available, so none of those layers should be rebuilt during
the migration.

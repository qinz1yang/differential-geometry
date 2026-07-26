# GPT Pro consultation: canonical H6 radius architecture

Public repository: `https://github.com/liao9yuan/differential-geometry`.
Use the remote `short-time-existence` branch (currently
`7cbd2b4c5e679db34f815090712069ee9bdd22d4`) as the inspectable reference.
The checked local aligned worktree is `codex/short-time-existence-align` at
`4039d5eec17c891898b3463120840e2c161c1834`, with additional uncommitted
declarations quoted below. Those local signatures and verification results are
newer than the remote branch and are authoritative for this consultation.

## Decision and execution status

The consultation verdict is accepted: use Route A for the canonical geometry
and Route C at the H6 producer boundary. There must be one total intrinsic
framed exponential, one induced pullback metric, and one intrinsic geometric
radius API; the H6-specific partial diffeomorphism is only a witness used while
constructing the chosen bounds/profile package.

The Lean import DAG requires one adjustment to the proposed order. The current
`FramedNormalCoordinates.lean` cannot import the intrinsic stack without a cycle
through Hopf-Rinow, Gauss, injectivity, and framed coordinates. Stage 1 therefore
lives temporarily in
`Geometry/Exponential/IntrinsicFramedCoordinates.lean`, above both stacks.
It is focused-green and exact-green and proves the intrinsic framed map is smooth,
fixes the origin, has the normal-frame derivative there, and agrees with the
legacy map on a positive ball. The fixed-model-norm bridge is explicit as
`intrFrameCLM`. It also provides the migration-only intrinsic local partial
diffeomorphism and the pullback metric of the total intrinsic map, with agreement
to the legacy metric on the migration source.

Current status: geometry Stages 1--3 complete; the canonical migration is about
35% complete. The next target is the HCG consumer boundary, where the consultation
pseudocode omitted a live formal dependency: `expMapIntrinsic` requires
`[CompleteSpace M]`, but the current public `normalCoordMetric Y x` and
`NormalCoordMetricBoundInput` carry no `MetricComplete Y`. Completeness must be
threaded or packaged explicitly before the existing HCG name can be switched.
The `NormalRadiusProfile` producer theorem remains 0%; no consumer radius-floor
assumption or second chart hierarchy has been introduced.

## Goal

Choose the smallest mathematically honest architecture that lets Hamilton H6
produce the sequence-relative normal-coordinate radius used by Step B/C. Do
not add a consumer assumption equivalent to the desired radius floor, and do
not create a second polished normal-coordinate hierarchy beside the canonical
one.

## Newly verified state

The intrinsic geodesic route is no longer an analytic frontier.

1. `Geometry/Geodesic/CrossVFReduction.lean` proves global smoothness of the
   basepoint-free geodesic spray.
2. `Analysis/ODE/TimeDependentFlow/SmoothDependence/CompactTrajectory.lean`
   proves finite-time smooth dependence along every compact reference orbit.
3. `Geometry/Exponential/IntrinsicVelocity.lean` proves:

   ```lean
   intrinsicExp_smooth
   intrinsicFiber_smooth
   intrinsicVar_smooth
   ```

   for the complete intrinsic exponential and fixed-base affine velocity
   variations. This module is focused- and exact-green.
4. `Geometry/Exponential/JacobiVariation.lean` proves:

   ```lean
   intrinsic_jacobi
   intrinsic_jacobi_one
   ```

   The first is the global Jacobi equation for
   `s,t |-> intrinsicGeodesic p (x + s*w) t`; the second identifies its
   time-one variation field with the vector-slot manifold derivative of
   `expMapIntrinsic`. Both declarations are focused- and exact-green; the
   coordinated refresh passed (`3799/3799`).
5. `C4/H6NormalCoord.lean` has exact-green sequence-uniform Rm04/Jacobi
   estimates and zero-order half/two metric equivalence on

   ```lean
   ball 0 (min r0 (expRadiusGp metric x / 26)).
   ```
6. `Comparison/InjectivityRadius.lean` proves that injectivity of the current
   framed ordinary exponential on a model ball forces that ball into the
   current chart-fixed `expDomain`.
7. `Comparison/ExpBallDiffeo.lean` already exposes

   ```lean
   IsLocalDiffeomorphOn.exists_diffeo_of_injOn
   ```

   so partial-diffeomorphism gluing is not missing.

No theorem above introduces a new assumption, `sorry`, `admit`, or axiom.

## Current canonical definitions

`FramedNormalCoordinates.lean` still defines

```lean
def framedExpMap (g) (p) : E -> M :=
  fun z => expMap g p (normalFrame g p z)

def framedExpDiffeo (g) (p) :=
  -- conjugates the qualitative chart-fixed expMapDiffeo by normalFrame
```

Here `expMap g p v := maximalGeodesic g p v 1` is the chart-fixed
totalized exponential. Its own documentation states that it becomes junk once
the geodesic leaves `(chartAt H p).source`. By contrast,
`expMapIntrinsic g hEnorm p v` follows the complete geodesic across charts.

`GaussLemmaPullback.lean` defines `expRadiusGp` from the qualitatively selected
`expMapC2Radius` and coercivity constants. It is therefore a radius for the
current chart-fixed selected partial diffeomorphism, not a geometric
injectivity radius.

`Comparison/InjectivityRadius.lean` currently defines

```lean
def injRadiusSet (g) (p) : Set ENNReal :=
  {r | Set.InjOn (framedExpMap g p) (Metric.eball 0 r)}

def injRadius (g) (p) : ENNReal := sSup (injRadiusSet g p)
```

Thus this `injRadius` is also tied to the chart-fixed ordinary exponential.

The Step-B record is

```lean
structure NormalCoordMetricBoundInput (X) where
  metricC : Nat -> Real
  metricC_nonneg : forall p, 0 <= metricC p
  radius : forall k, (X.obj k).M -> Real
  radius_pos : forall k x, 0 < radius k x
  metric_equiv : forall k x,
    NormalCoordMetricEquivOn (X.obj k) x (Metric.ball 0 (radius k x))
  metric_deriv : forall k p x,
    NormalCoordMetricDerivBound (X.obj k) x
      (Metric.ball 0 (radius k x)) p (metricC p)
```

and the compatibility record is

```lean
structure NormalRadiusProfile (hd : InjRadiusDecayInput X)
    (hb : NormalCoordMetricBoundInput X) where
  ratio : Real
  ratio_pos : 0 < ratio
  le_radius : forall k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) <= hb.radius k x
  le_exp_radius : forall k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) <=
      expRadiusGp (X.obj k).metric x
```

## Two feasibility failures

### 1. `NormalRadiusProfile` cannot be produced from an arbitrary `hb`

The data in `NormalCoordMetricBoundInput` is downward closed in `radius`: from
any valid record one may replace `radius k x` by an arbitrarily smaller
positive value and restrict both estimates. Therefore no theorem of the form

```lean
forall hd hb, NormalRadiusProfile hd hb
```

can be true. Even on one fixed flat metric, choose `hb.radius k x = 1/(k+1)`
while `hd.mu` is constant. The required positive global `ratio` cannot exist.

The H6 producer must choose the radius together with the metric-bound record,
or the record must carry an honest source-radius floor as part of its H6 data.
It cannot be recovered afterward from the current fields.

### 2. Geometric injectivity cannot lower-bound the current `expRadiusGp`

`expRadiusGp` contains an arbitrary qualitative IFT/chart choice. A sequence of
flat manifolds can use center charts whose source neighborhoods shrink with
the sequence while the intrinsic geometry and geometric injectivity radius
stay unchanged. CGT injectivity controls `expMapIntrinsic`; it cannot uniformly
lower-bound a chart-dependent selected radius.

The same issue affects the current `injRadius`, because its map is
`framedExpMap = expMap o normalFrame`, not the complete intrinsic exponential.
The new global Jacobi/differential theorems do not repair this representation
mismatch.

## Architecture decision requested

Please choose and justify the smallest route among these, or give a better one.

### Route A: migrate the canonical framed API to the intrinsic exponential

Parameterize the canonical framed exponential/partial diffeomorphism by the
metric-enorm compatibility proof already used by the intrinsic API:

```lean
hEnorm : forall x (v : TangentSpace I x),
  eNorm v = ENNReal.ofReal (Real.sqrt (g.inner x v v))
```

Then redefine or replace, in dependency order:

```lean
framedExpMap
framedExpDiffeo
framedChartAt
normalCoordMetric
injRadius
expRadiusGp
```

using `expMapIntrinsic`. Preserve the existing public names if possible and
migrate the current framed B/C consumers once, rather than maintaining two
normal-coordinate hierarchies.

Questions for Route A:

1. What is the narrowest canonical file for the intrinsic framed map and its
   local partial diffeomorphism?
2. Should `hEnorm` be an explicit argument throughout, or can an existing
   metric/bundle package provide it without introducing a new foundational
   typeclass?
3. Can positivity of the intrinsic injectivity radius be proved most cheaply
   by transferring the existing local ordinary branch through the already
   proved small-radius equality, or should one apply the manifold IFT directly
   to `intrinsicFiber_smooth` and the identity derivative at zero?
4. Give the smallest migration order that keeps the current B/C selected
   branch usable after each step.

### Route B: keep local ordinary charts, add one geometric branch beneath H6

Keep the current local `framedExpDiffeo` for existing consumers, but construct
one intrinsic injective partial diffeomorphism on a CGT-controlled ball from:

```text
intrinsicFiber_smooth
  + intrinsic_jacobi_one
  + Rm04 derivative estimates
  + intrinsic injectivity
  + exists_diffeo_of_injOn.
```

Then make the H6 metric bounds and all downstream radius-sensitive consumers
use that branch. Explain how this avoids becoming a second polished
normal-coordinate hierarchy and how the existing `normalCoordMetric` is
transported to it without any qualitative agreement radius.

### Route C: combined H6 output first

Change the producer boundary so H6 returns a chosen metric-bound record and its
profile together, for example:

```lean
structure H6NormalData (X) (hd : InjRadiusDecayInput X) where
  bounds : NormalCoordMetricBoundInput X
  profile : NormalRadiusProfile hd bounds
```

This fixes the shrinkable-radius quantifier problem but not by itself the
chart-fixed `expRadiusGp` problem. State what canonical exponential migration
must accompany it.

## Requested answer

1. Verdict and selected architecture.
2. Exact first public theorem or definition to implement, with a Lean-like
   signature and natural file.
3. Proof/migration dependency chain.
4. Which current public definitions must change and which can remain stable.
5. How to package the H6 radius so it is chosen with the all-order metric
   estimates rather than demanded from arbitrary shrinkable input data.
6. How the intrinsic Rm04/Jacobi endpoint proves local-diffeomorphism and
   metric-equivalence bounds on the chosen geometric ball.
7. Whether the high-order curvature-to-coordinate-metric induction is an
   independent remaining theorem after the radius architecture is corrected.
8. Difficulty classification: routine migration, missing reusable API,
   substantial design choice, or genuine mathematical obstruction.

## Constraints

- Work on the `short-time-existence` branch.
- Preserve the current quantitative selected diagonal branch and its transport
  theorems.
- Do not add a synonymous radius-floor assumption downstream.
- Do not claim `NormalRadiusProfile` is proved merely because intrinsic
  smoothness and Jacobi identities are proved.
- Do not derive a positive ratio from an arbitrary shrinkable `hb.radius`.
- Do not claim CGT controls the current chart-dependent `expRadiusGp` without
  changing or quantitatively identifying that API.
- Do not introduce a new foundational class without explaining why existing
  metric/bundle data cannot carry `hEnorm` explicitly.
- Keep the high-order H6 curvature-jet induction visible as a separate
  producer if it is still required.

# GeodesicPreservingSoulData: literal total-convexity audit

## Scope and status

2026-09-08, `soul_distance_field`, assigned by the active source brief in
`SOUL_PLAN.md:1140`. This is a definition/proof audit only. No Lean file was
created or changed; all five delivered positive energy leaves remain frozen.
No compiler, REPL, Lake operation, artifact refresh, registration, plan/status
edit, or commit was performed. The source inspected was the dev checkout at
HEAD `7eaf53428cee0f889df28307c6726b426e062061`.

The requested Markdown-only claim was attempted through
`E:/testdifferential-geometry/scripts/lake-locked.ps1` from the dev checkout.
The wrapper rejects this with `No Lean files to claim.` (line 410), so no
claim token exists for this note. Its ownership is the explicit bounded
source brief above; no dummy Lean leaf was created to obtain a lock.

The pinned branch source is
`a450067f6a6f7e2bd973b97e01f7e550e3a3b579`,
`Poincare/Geometry/Soul/Definitions.lean`, blob
`9f702e5f994b71ea7e7f3bcf5c1fe24b19730011`.

**Outcome:** the old branch predicate is stronger than native total convexity
and is sensitive to irrelevant values of coordinate charts outside their
sources. Continuity of the actual curve cannot be recovered in general from
the displayed equation predicate. A concrete mathematical construction is
given below; it is not a Lean-verified counterexample artifact. Consequently,
the literal old data package has not been instantiated by the general soul
endpoint. The smallest repair is an explicit public-semantic decision to add
the missing `ContinuousOn` premise to the branch predicate (or to make that
field use the native predicate). No definition has been changed here.

## Exact definition comparison

Native `DifferentialGeometry.Geometry.Topology.IsTotallyConvex`, in
`Topology/SoulConvexCore.lean:325`, is:

```lean
∀ {gamma : ℝ → M} {a b : ℝ}, a ≤ b →
  Geodesic.IsGeodesicOn g gamma (Icc a b) →
  ContinuousOn gamma (Icc a b) →
  gamma a ∈ S → gamma b ∈ S → MapsTo gamma (Icc a b) S
```

Pinned `Poincare.Geometry.IsTotallyConvex`, `Definitions.lean:39`, is:

```lean
∀ (gamma : ℝ → M) (a b : ℝ), a ≤ b →
  IsGeodesicOn g gamma (Icc a b) →
  gamma a ∈ S → gamma b ∈ S → MapsTo gamma (Icc a b) S
```

Here the unqualified branch `IsGeodesicOn` is the imported native
`DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn`, not a
different branch definition. Both versions quantify over nonminimizing
segments and permit degenerate intervals. Explicit versus implicit binders
are inessential; the missing continuity hypothesis is substantive.

The branch's `GeodesicPreservingSoulData.totallyConvex` field is precisely
this stronger branch predicate on `Set.range iota` (`Definitions.lean:77`).
The branch predicate immediately implies the native predicate by ignoring
the latter's continuity argument. The converse needs additional information
and is false uniformly over the allowed charted-manifold structures below.

## What the equation actually supplies

`Geodesic/Equation.lean:170` defines

```lean
chartLocalCurve gamma t s = extChartAt I (gamma t) (gamma s)
```

`HasGeodesicEquationAt`, at line 177, supplies vectors `v` and `a`, a
`HasDerivAt` witness for this coordinate-valued function at `t`, local
differentiability of that same function, a derivative-of-derivative witness,
and the displayed Christoffel equation. `IsGeodesicOn` at line 302 is just
the assertion of that predicate at every parameter in the set.

Thus the first derivative witness gives continuity of
`s ↦ extChartAt I (gamma t) (gamma s)`. To recover the actual curve using
the inverse chart one still needs

```lean
∀ᶠ s in 𝓝[Icc a b] t, gamma s ∈ (extChartAt I (gamma t)).source
```

This is not a field of the equation predicate. Mathlib's
`Logic/Equiv/PartialEquiv.lean:116` makes the chart a total function with
left inverse required only on `source`; the file explicitly treats its
outside-source values as irrelevant data. `Topology/PartialHomeomorph/Defs.lean:53`
adds continuity only on source/target; `OpenPartialHomeomorph/Defs.lean:53`
adds openness. `ChartedSpace.lean:139` imposes source membership for the
center and atlas membership, not global injectivity or a condition on chart
values outside source. `IsManifold/ExtChartAt.lean:454` preserves these total
function values by composing the chosen chart with the model map.

The derivative's coordinate continuity ensures nearby coordinate values
belong to the chart target when the model is boundaryless. That does not
imply that the original points belong to chart source: `map_target` speaks
about the inverse image chosen by the inverse function, not every point
whose forward coordinate happens to be in the target.

## Concrete construction showing the obstruction

Take the usual Euclidean plane `E = ℝ²`, `M = E`, with its usual topology,
Euclidean distance, and model `I = 𝓘(ℝ,E)`. For each `c ∈ E` specify a chosen
chart `e_c` as follows:

```text
source(e_c) = B(c,1),       target(e_c) = B(0,1),
e_c(x) = x-c if ||x-c|| < 1, and 0 otherwise,
e_c^{-1}(y) = c+y for every y.
```

These are actual open partial homeomorphisms in the definition just read:
on source/target the maps are inverse translations; both sets are open;
both restrictions are continuous. The value `0` outside source violates
none of the partial-equivalence fields. Use the family `{e_c}` as atlas and
`chartAt c = e_c`; the center belongs to its source. On every overlap the
transition is `y ↦ y+c-d`, so all transitions are smooth. This gives the
usual smooth, boundaryless manifold structure with a legitimate different
choice of total chart functions. The differential of every transition is
the identity. Consequently the usual Euclidean inner product defines the
same smooth flat Riemannian metric in these tangent coordinates; its metric
is complete and compatible with the usual distance. This example has
dimension two, is connected, noncompact, and has nonnegative curvature.

Put `p = (0,0)` and `q = (3,0)`. Define the actual function on all of `ℝ` by

```text
gamma(s) = p if s=0 or s=1, and q otherwise.
```

For either `c ∈ {p,q}`, both `e_c(p)` and `e_c(q)` are zero: at the center
this is the translation value, and the other point is outside the unit
ball. Therefore, for every `t` and every `s`,

```text
chartLocalCurve gamma t s = e_{gamma(t)}(gamma(s)) = 0.
```

All three derivative clauses in `HasGeodesicEquationAt g gamma t` are now
witnessed by derivatives of the constant zero function, with `v=a=0`.
The Christoffel clause also vanishes, using the actual bilinearity identity
`chartChristoffelContraction_zero_left` (`Geodesic/Equation.lean:79`).
Hence this function satisfies the literal native equation at every real
time, and therefore `IsGeodesicOn` on `[0,1]`. Nevertheless it is not
continuous on `[0,1]`: the times `1/(n+2)` tend to zero, their images are
always `q`, and `gamma(0)=p≠q`. This is a construction of the curve and
permitted atlas, not an appeal to a hypothetical discontinuous geodesic.

It also separates the two total-convexity predicates. The set `{p}` is
natively totally convex for this flat metric. Indeed, for a continuous
equation-satisfying segment, continuity places the curve in its centered
chart locally. There the coordinate map is a translation and the flat
geodesic equation is the ordinary equation `gamma''=0`. On the connected
open parameter interval its velocity is constant, so the curve is affine;
endpoint continuity extends that identity to the closed interval. Equal
endpoints force the constant curve. A degenerate interval is immediate.
The branch predicate fails for `{p}` because the explicitly constructed
curve has both endpoints in `{p}` but `gamma(1/2)=q`.

This mathematical construction has not been transcribed into a new Lean
atlas/metric instance or compiler-checked; that would be a separate task.
It explains why a universal continuity/total-convexity bridge would be an
incorrect target, even after retaining completeness and connectedness.

## Available bridges and smallest decision

The existing source APIs consistently preserve the needed regularity:

- `Geodesic/Smoothness.lean:51`, `IsGeodesicAt.continuousAt`, applies to the
  different native integral-curve germ predicate. It cannot be applied to
  `HasGeodesicEquationAt` or to equation-only `IsGeodesicOn`.
- `Geodesic/CrossVFReduction.lean:509` and `:647` require `ContinuousAt gamma t`
  when transporting the equation from its moving centered chart to a fixed
  chart. They do not produce that continuity.
- `Geodesic/ChartRegularity.lean:63` and `:109` bootstrap to smoothness only
  after `ContinuousOn` has been supplied on an open set.
- `Exponential/IntrinsicExpContinuity.lean:126` assumes `Continuous gamma`
  for its equation-to-integral-curve lift. Its proof uses that premise to
  obtain eventual chart-source membership at line 145.
- The checked `Soul/GeodesicGerms.lean:203` states the exact equivalence:
  `IsGeodesicAt` iff equation **and continuity** on an open neighborhood.
  Its smooth representative theorem therefore does not remove this input.

If one explicitly supplies eventual chart-source membership at each
parameter within the interval, the first coordinate derivative witness
does yield `ContinuousWithinAt gamma (Icc a b) t`: compose its coordinate
continuity with the inverse chart and use the chart's source-restricted
left inverse on that eventual set. Equivalently, actual `IsGeodesicAt`
witnesses at every parameter give continuity immediately. Neither extra
input is present in the old universally quantified branch predicate.

The smallest public-semantic decision is to insert
`ContinuousOn gamma (Icc a b) →` immediately after its `IsGeodesicOn`
premise, retaining all other binders. In the common native context this
corrected predicate is exactly native total convexity, and the bridge is
just application to `hab`, `hgeo`, `hcont`, `ha`, `hb`; no new geometric
assumption or proof machinery is needed. Using native total convexity
directly for the data field has the same effect. The old declaration must
not be silently redefined or claimed equivalent to the corrected one.

The pinned `PointSoul.lean` pointness consumer explicitly uses only
compactness, connectedness, isometric immersion, and native geodesic
preservation; it does not read `totallyConvex`. The parent's direct actual
point-soul/diffeomorphism route can therefore proceed separately. What
remains blocked here is the claim of instantiating the **literal old**
`GeodesicPreservingSoulData` package under unchanged public semantics.

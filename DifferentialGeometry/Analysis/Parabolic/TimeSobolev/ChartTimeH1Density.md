# ChartTimeH1Density

## Scope

This file is the geometric half of endpoint-preserving time-`H¹` density in
finite manifold charts.  It does not construct the strong vector-valued
approximants.  Instead, it turns a supplied coordinate curve into a global
manifold curve while preserving the coordinate formula on its segment.

## Checked API

- `flatExtend` extends a coordinate curve by its endpoint values.
- `flatExtend_cont` and `flatExtend_contDiff` prove continuity and `C¹`
  regularity.  The smooth result assumes the coordinate curve is locally
  constant at both endpoints.
- `flatExtend_mapsTo` shows that chart-target membership on the closed segment
  is enough after flat extension.
- `chartFlatLift` lifts the flat coordinate curve through the inverse extended
  chart.
- `chartLift_continuous` gives the weaker globally continuous lift without
  endpoint flatness.
- `chartLift_contMDiff` gives a global `C¹` lift when both coordinate endpoints
  are locally constant.
- `chartLift_coord` recovers the supplied coordinates on the segment, while
  `chartLift_left` and `chartLift_right` expose the constant endpoint germs used
  for gluing.
- `flatJoin` and `flatJoin_contMDiff` perform the finite iterated gluing for any
  nondecreasing node sequence and any family of globally `C¹` manifold
  curves with equal adjacent germs.
- `flatJoin_eq` identifies the resulting curve with each inserted piece away
  from its left subdivision node, the almost-everywhere form needed for action
  integrals.

Focused verification passed without warnings or placeholders.

## Finite gluing route

Adjacent flat chart lifts with the same manifold endpoint are eventually equal
at their common node by `chartLift_right` and `chartLift_left`.  The generic
`flatJoin_contMDiff` theorem iterates Mathlib's `ContMDiff.piecewise_Iic` over
the finite subdivision.  Its induction carries the latest-piece germ, so
repeated nodes in a merely monotone subdivision need no deletion or reindexing.
The same pairwise construction is already used for endpoint-flat manifold
paths in `Geometry/Comparison/CGTPaths.lean`.

There is also a genuinely weaker interface: without locally constant endpoint
germs, the chart lifts are globally continuous and `C¹` on each open segment.
Finite derivative jumps occur only at subdivision nodes and therefore should
not affect the action integral.  This piecewise-`C¹` class may be enough for a
relaxed minimization argument, followed by corner momentum matching and a
Tonelli regularity upgrade.  The endpoint-flat interface is nevertheless
available and avoids changing the current global-`C¹` competitor class.

## Audit of the three routes

1. **Uniform interior buffer plus inverse chart:** viable.  Uniform convergence
   to a compact coordinate image eventually preserves the open chart target;
   `flatExtend_mapsTo` and `chartLift_contMDiff` complete the geometric lift.
   Producing the endpoint-flat strong coordinate approximation belongs to the
   vector time-`H¹` density layer.
2. **Overlap transition and direct gluing:** endpoint agreement alone does not
   match first derivatives across a chart transition.  The existing
   `chartH1_overlap` is an almost-everywhere weak chain rule, not a node-jet
   matching theorem.  Local constancy at nodes removes this obstruction and
   makes `ContMDiff.piecewise_Iic` apply directly.
3. **Mathlib smooth approximation with `EqOn` near nodes:** the available
   manifold-domain theorem has a normed-space target and controls only pointwise
   distance.  Its `EqOn` conclusion requires the original map to be smooth on a
   neighborhood of the closed set.  A general time-`H¹` curve has no such node
   neighborhood, and the theorem gives no strong derivative convergence.

## Progress boundary

The chart lifting and geometric endpoint-gluing mechanism, including the finite
iterated fold, are complete.  The remaining analytic producer is endpoint-flat strong density for each
vector-valued `timeH1` segment, including uniform convergence and strong
derivative convergence.  `lAction_c1_dense` remains unstated and unproved
(0%); the finite-chart geometric lift/glue sub-brick is 100%, while its vector
density/action-convergence machinery remains separate.  The dedicated
minimizer/direct-method machinery remains about 72--78%, dedicated L-geometry
machinery about 73--77%, P2 below 1%, and the whole Poincaré program about
3--5%.

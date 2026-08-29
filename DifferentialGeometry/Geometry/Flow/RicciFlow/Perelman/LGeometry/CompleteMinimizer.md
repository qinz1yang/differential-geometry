# CompleteMinimizer

## Role

This file is the compactness adapter between complete bounded-curvature
localization and the existing finite-chart direct method.  It must not assume a
globally compact manifold.

## Current state

- `lRegSpeed_int_c1` produces the moving-metric kinetic integrability needed by
  the localization theorem for every regular `C¹` curve.
- `lRegRef_int_c1` produces the fixed terminal-metric energy integrability used
  by the complete-flow localization theorem.
- `lRmChartH1_fin` replaces the compact-manifold scalar minimum in the
  finite-chart direct method by the scalar lower bound produced directly from
  the slab curvature hypothesis.
- `lRmAction_subseq` places an entire fixed-endpoint, bounded-action sequence in
  one explicit compact terminal-metric ball, returns that common target, and
  applies the native compact-range Arzelà–Ascoli theorem.
- `lRmAction_chart_lsc` threads that compact target through the finite-chart weak
  limit and the compact-target lower-semicontinuity theorem.
- `exists_lRegMin_rm` assembles the minimizing sequence, complete-flow compact
  subsequence, finite-chart liminf inequality, global `C¹` density recovery,
  closed-interval `C¹` regularity, and the interior regularized L-geodesic
  equation on a nondegenerate interval.
- `exists_lMin_rm` is the endpoint-honest raw-time capstone. It extends the
  attained curve across both square-root-time endpoints and returns
  `IsLRegCurveOn`, equality with the maximal regularized curve, membership in
  `lExpPosDom`, the prescribed endpoint, raw `lCost` attainment, and the global
  fixed-endpoint competitor inequality.
- `exists_lMinVec_rm` converts that complete-flow minimizer into the canonical
  `lMinDomain` interface consumed by the cut and local-cost layers. Its source
  proof mirrors the compact adapter but uses `exists_lMin_rm`.
- Focused verification of the compact-target subsequence, chart-liminf,
  strengthened regular minimizer, and raw endpoint theorem passes without
  warnings or placeholders.

The older direct method had two ambient-compact dependencies. The new
compact-subset comparison `dist_lt_riedist_cpt` removes the Arzelà dependency.
The lower layer now has supplied-compact-target scalar lower-bound and
dominated-convergence producers; the finite-chart liminf and density modules
consume them without an ambient `CompactSpace M` instance. The local
finite-chart `C¹`, node-matching, `C²`, acceleration, and whole-interior
regularity producers were then generalized at declaration scope; each focused
recheck passed without warnings. No proof body, theorem statement, competitor
category, or replacement compactness assumption was added along that chain.

## Frontier and progress

The endpoint-honest `exists_lMin_rm` theorem is stated, proved, and focused
warning-free green: 100%. Its dedicated complete bounded-curvature direct-method
and regularity machinery is also complete for this theorem. It returns an
`IsLRegCurveOn` minimizer, agreement with `lRegCurve`, membership in
`lExpPosDom`, endpoint realization by `lExp`, raw `lCost` attainment, and the
global fixed-endpoint `C¹` comparison inequality, all without
`CompactSpace M`.

The follow-on `exists_lMinVec_rm` adapter is warning-free green and its targeted
module artifact is refreshed: 100%. It adds no minimizer or compactness
assumption: `lMinDomain` membership is derived from the attained raw cost and
maximal-curve agreement already returned by `exists_lMin_rm`.

This closes the first complete noncompact L-minimizer endpoint, but not all of
L8: extensions to broader competitor classes and any additional global
geometric consequences remain separate. L8 as a whole is roughly 30–35%, and
the whole L-geometry program remains substantially below 50%.

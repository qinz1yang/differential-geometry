# ActionAttain

## Result

`lRegCostC1` is the infimum of the regularized L-action over global `C¹`
curves with two prescribed endpoint values. `exists_lRegMinC1` proves that,
when this competitor class is nonempty on a compact manifold, the infimum is
attained by a continuous relaxed curve.

`lRegCostC1_le` is the public lower-bound accessor for this infimum: under the
same compact direct-method time-slab hypotheses, it bounds `lRegCostC1` by the
action of any supplied global fixed-endpoint `C¹` competitor. It reuses the
attained minimizer and avoids unfolding `sInf` in cut-domain consumers.

`lRegCostC1_le_bdd` is the noncompact infimum accessor.  It assumes exactly
that the fixed-endpoint global `C¹` action values are bounded below, then
bounds their infimum by every member.  It needs no compactness, separation,
boundarylessness, flow-equation, time-slab, or regular-time hypothesis.

The theorem proves the exact action equality and the inequality against every
global `C¹` fixed-endpoint competitor. It also retains a finite chart
subdivision, local `timeH1` representatives of the relaxed curve, and a global
`C¹` recovery sequence converging uniformly and in regularized action. These
are the witnesses needed by the later Tonelli regularity step.

The proof uses the existing minimizing-sequence theorem for `sInf`,
`lAction_chart_lsc`, and `lAction_c1_dense`. A local native tangent-map and
continuous-Riemannian-bundle argument shows that global `C¹` competitors have
the reference-energy integrability required by compactness. No manifold-H1
path object, closure assumption, admissibility wrapper, or new foundational
class is introduced.

## Boundary

The relaxed minimizer produced in this file is only continuous with finite-
chart H1 realizations. This theorem itself does not claim that it is `C¹`, an
L-geodesic, or an `IsLRegCurveOn` curve. Those regularity upgrades and the
compact `exists_lMinimizer` endpoint are now complete downstream; the remaining
use here is the finite realization and the cost lower-bound API.

## Verification and progress

Focused verification passed without warnings or placeholders after adding the
noncompact accessor, and the exported module was refreshed for downstream
consumers.  The existing public endpoint axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

- `exists_lRegMinC1`: 100%.
- `lRegCostC1_le`: 100%.
- `lRegCostC1_le_bdd`: 100% proved and focused green.
- Compact regular `exists_lMinimizer`: 100% downstream.
- The minimizing-prefix/cut-domain machinery remains incomplete; its next
  exact producer is an arbitrary two-piece finite chart-H1 join.
- `redVolume_anti`: 0%.
- P2 remains below 1%, and the whole Poincare program remains about 3--5%.

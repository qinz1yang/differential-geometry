# MetricDiffSmallC0

## 2026-07-19 source-only endpoint producer

This file supplies the closed-edge zeroth-order bridge shared by the
Ricci--DeTurck uniqueness adapter and the future harmonic-map heat-flow weak
solver.

Proved source facts:

- `jointSmall_compact`: a jointly continuous scalar family which vanishes on
  one compact slice is uniformly small in the compact variable near that
  parameter;
- `gOpBound_unitQuad`: a uniform quadratic bound on the fixed metric's unit
  tangent bundle promotes, by polarization and normalization, to the exact
  bilinear `gFibreOpBound` with no constant loss;
- `metricDiff_smallC0`: joint `C^0` chart-Gram control on `[a,b)`, together
  with `g(a)=q`, selects one `T>0` common to all points and tangent vectors such
  that the realized fixed-background metric difference has any prescribed
  positive `gFibreOpBound` on `[a,a+T]`.

The argument uses only endpoint continuity and compactness of the fixed
metric's unit tangent bundle.  It does not assume interior Sobolev continuity,
does not choose a base-point-dependent window, and introduces no wrapper
hypothesis.

Verification state: source assembled only.  A focused Lean check is deferred
until the shared named build finishes.  Endpoint theorem completion remains
0%; this is producer machinery, not the harmonic-map gauge construction or
the public Ricci-flow uniqueness theorem.

Honest accounting: the source body for this isolated producer is **100%**;
Lean-verified producer completion is **0%** until its focused check passes;
`ricci_flow_forward_unique` remains **0%**.  There is no known mathematical
obstruction in this bridge.  The remaining risks are elaboration-level:
dependent bundle-evaluation simplification in `hEval`, the conversion between
the bilinear CLM and `Tensor02At` in `gOpBound_unitQuad`, and the final subtype
normalization in `hunit`.  A static audit caught and repaired one proof-shape
error: membership in the small metric ball must be proved directly before the
ball-subset map is applied.

# Strong density for the regularized L-action

## Current result

`lAction_chart_lim` is the finite-chart analytic assembly theorem.  On a
fixed monotone subdivision it combines:

- uniform convergence of the manifold curves;
- uniform convergence of every chart-coordinate representative;
- strong convergence of every chart weak derivative;
- compact containment in each chart target.

The conclusion is convergence of the complete regularized L-action.  The
kinetic term uses `chartKin_tendsto`; the scalar-curvature term uses
`lScalar_tendsto_cpt` on the compact manifold image of each supplied compact
coordinate buffer; `lRegAction_chart` identifies the finite coordinate sum
with the raw manifold action. This removes the former ambient `CompactSpace`
requirement from the chart, strong-`timeH1`, and global `C¹` density theorems.

`lAction_h1_lim` is the natural strong-topology interface: callers provide
strong convergence of each local `timeH1` representative, and the theorem
internally derives both uniform convergence of the continuous representatives
and strong convergence of their weak derivatives before applying
`lAction_chart_lim`.

## Geometric density stage

`ActionDensityGeom.lean` now verifies the finite geometric construction
`exists_c1_of_flat`.  It handles nondecreasing subdivisions, repeated nodes,
and the empty subdivision, and returns global C1 curves, fixed endpoints,
closed-piece chart representatives, chart-source containment, and uniform
convergence.

This file also has checked private producers which derive compact chart
buffers from the compact coordinate image, turn uniform convergence into
eventual buffer containment, and turn strong `timeH1` convergence into
uniform convergence of continuous representatives.  Endpoint-flat strong
`timeH1` density is supplied by `TimeH1Density.lean`; zero-length pieces use a
constant sequence locally rather than imposing strict subdivision
monotonicity.

`lAction_c1_dense` is now the completed geometric capstone.  It selects one
common tail for all finitely many chart pieces, lifts and glues the endpoint-
flat coordinate approximants, and returns global C1 curves with fixed
endpoints, exact local chart `timeH1` representatives, strong local H1
convergence, uniform manifold convergence, and convergence of the complete
regularized L-action.  Compact chart buffers are constructed internally and
are not exposed as consumer assumptions.

## Verification

The upstream endpoint-flat density, strong quadratic, fixed-chart kinetic
convergence, and finite geometric assembly modules are verified. Focused
verification of the compact-range generalization now passes without warnings
or placeholders. Its chart-image membership proof explicitly normalizes the
shifted time and converts `chartAt` source membership to `extChartAt` source
membership.

## Project position

`lAction_c1_dense` and its dedicated density machinery are 100% complete.
This resolves the fixed-endpoint C1-closure/action-recovery gate for the
direct method, but it is not yet `exists_lMinimizer`: the relaxed minimizer
still needs the separate Tonelli/Euler--Lagrange regularity upgrade and final
infimum assembly.  `exists_lMinimizer` and `redVolume_anti` therefore remain
0%.  Dedicated direct-method machinery is roughly 84--89%, dedicated
L-geometry roughly 78--82%, P2 remains below 1%, and the whole Poincare
program remains roughly 3--5%.

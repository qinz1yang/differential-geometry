# FineChartCover

## Producers

`exists_fine_pou` constructs, for a compact set `K` inside the source of one
fixed chart and any prescribed positive coordinate scale `r`, a radius
`epsilon > 0`, a finite set of freeze centers in `K`, and a smooth partition
of unity on `K` subordinate to the corresponding radius-`epsilon` coordinate
balls.  It also proves `2 * epsilon <= r` and that every closed concentric
radius-`2 * epsilon` ball lies inside the chart target.

`exists_fine_cutoffs` applies `exists_pou_cutoff` to add the outer half of the
localization.  Each outer cutoff equals one near its inner POU carrier and has
topological support in the radius-`2 * epsilon` chart ball.

`exists_fine_tricut` adds a third, nested cutoff.  The new outermost cutoff is
one on a neighborhood of the support of the middle cutoff, and both supports
remain in the same radius-`2 * epsilon` ball.  Thus a globally smooth
transition-coefficient extension may use the outermost collar without
altering an output already localized by the middle cutoff.

`FineChartData` bundles the resulting radius, finite center set, fine POU,
and both cutoffs as one ordinary data value (not a class or instance).
`existsFineChart` constructs this value, and `FineChartData.rho_sum` exposes
the ordinary finite-sum identity needed by the tensor retraction.

The construction uses a closed-thickening collar of the compact coordinate
image inside the open chart target, followed by a finite subcover.  Hence all
straight coordinate segments in an outer ball remain in the chart target,
and the prescribed scale can be chosen first from the desired coefficient
absorption threshold.

## Ricci--DeTurck use

For each active canonical chart, take `K` to be the compact topological support
of its canonical POU function.  The refined POU is multiplied by that original
function; no division by a possibly vanishing POU weight is used.  Uniform raw
Gram-jet bounds on the finite outer compact balls are to be produced directly
from the endpoint `MetricCovDerivOrderBoundOn` hypotheses.

## Verification

Focused Lean verification passes without warnings. The strict-cutoff
producers carry the existing `NormalSpace M` condition required by Mathlib's
smooth Urysohn theorem; no new class or instance is introduced. This file
contains no `sorry`, `admit`, axiom, opaque declaration, replacement
hypothesis, or new foundational class/instance/notation.

Endpoint completion remains 0%; this is finite localization machinery only.

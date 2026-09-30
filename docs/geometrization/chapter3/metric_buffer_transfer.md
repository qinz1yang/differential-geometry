# ALG06/AC13: metric transfer and realized-buffer comparison

Eleven public theorems in five leaves prove metric transfer and the four-point
assembly for an explicitly supplied realization of the controlled metric.
This milestone does NOT construct the intrinsic length distance on an open
ball and does NOT claim full ALG06 or AC13. All realization hypotheses below
remain visible and must be proved for that actual metric before binding it.

A topological embedding f:Y->X into a complete metric space, with
LipschitzWith1 f, transfers completeness to closedBall_Y(p,L) whenever
closedBall_X(f(p),L) lies in range(f). The proof maps arbitrary Cauchy filters,
places their ambient limits in the image by the margin, and uses the embedding
topology to recover Y-convergence and the closed radius bound. No global
isometry, uniform inverse, properness or completeness of Y is assumed.
If range(f)=B_X(o,256R) and f(p) lies in B_X(o,4R), the exact closed200R
ball in Y is complete. This is the completeness step of ALG06.

Four-point comparison transfers in both directions on any region with exact
pairwise distance agreement. Local comparison transfers through an open
embedding when sufficiently small balls have that agreement. Canonical germ
angles are preserved by eventual two-parameter cross-distance agreement,
and by agreement on a positive initial rectangle. Neither theorem reselects
the supplied germs or requires equality at parameter zero.

A region theorem derives four-point comparison from actual chosen segments,
local comparison at its centers and endpoint-hinge comparison with the
explicit arm-sum bound. Its three angles use the SAME three chosen germs,
including repeated outer vertices. In a locally compact length space with
local comparison, a complete closed L-ball and81R<=L give comparison on
B(o,R): endpoint closed80R-balls are complete, ALG05 gives radius4R, and
actual joins come from the accepted complete-buffer theorem. The number81
is a derived sufficient assembly bound, not a quoted source constant.

Finally, suppose Y is locally compact, has the explicit actual-curve length
property and local four-point comparison, and f is the preceding embedding
onto B_X(o,256R). ALG05 gives endpoint comparison at every p mapped into
B_X(o,4R), for arm sums<10R. If f also preserves all pairwise distances
among points mapped into that4R-ball, the assembly proves ambient four-point
comparison on B_X(o,R). It uses the actual equality
f(B_Y(p,R))=B_X(o,R) for f(p)=o, proved from the stated hypotheses.
No conclusion about the still-unconstructed intrinsic metric is inferred.
The remaining ALG06 radial point-on-side and monotonicity assembly are also
not asserted by this milestone.

Sources checked: frozen blueprint207A AC02 full2141-2190, AC13 full2713-2755,
ALG06 full7536-7580 and ALG05 full7486-7534; accepted ALG01/04/05 proof
bodies reused. Mathlib Cauchy.lean154-160,418-448, Maps/Basic.lean116-122,
242-243, and Neighborhoods.lean350-359 supply the actual filter/embedding
proof APIs. Version/hash and retained AKP errata evidence are recorded
separately. A subsequent search of BBI Chapter2 located intrinsic-distance
material; those search excerpts are NOT proof evidence for this milestone.

Blueprint207 and earlier mathematical leaves are unchanged. Intrinsic-distance
construction and its exact identifications, full ALG06 radial transfer,
endpoint-free global recognition, uniform covering and PC migration remain.

# Uniform covering from local curvature and finite dimension

Three public theorems in two leaves close the fixed-curvature covering
producer: a complete length space, local curvature-1 comparison on the
controlled256R region, and its finite AMBIENT dimension bound n>=1 now
produce an internal epsilon-net of the closed R-ball with exactly
(1+ceil(4*(pairedChartDistortion n)^2*sqrt(n)*sinh(2R)/epsilon))^n points.
No chart, local compactness, properness or packing bound is assumed.
There are consumers for both local AMBIENT comparison and local comparison
in the ACTUAL constructed intrinsic metric, with explicit metric/topology
parents. The bound uses the SAME explicit L_n as AC28/29.

The proof first splits singleton and nontrivial sources. A singleton has the
literal one-point net {o}, including the strict epsilon coverage condition.
For a nontrivial source, AC07 produces local compactness of the256R-ball and
an actual nearby centered chart of rank1<=m<=n with distortion L_n. AC04
then produces the net using rank m. The new numerical theorem shows that
its exact ceiling bound is at most the fixed-n bound, since sqrt, the natural
ceiling, and natural powers are monotone at bases at least1. This avoids an
extra coordinate-padding map while retaining precisely the blueprint's
final cardinality. Chart radius and source-dependent chart rank disappear
from that final bound.

The near-chart producer uses only a local comparison neighborhood at the
basepoint; local compactness uses all controlled points. The two constructions
are now joined to the actual radial and greedy-net producers. No global
comparison or countable intrinsic dimension bound is introduced. Completeness
is the original ambient assumption, not completeness of an open ball.

Checked sources: blueprint207A AC04 full2232-2269, note2271-2277 (variable
rank and singleton), AC07 full2357-2377, AC08 full2401-2418, AC29 full3508-3535,
and ALG07 full7582-7617. The actual accepted local-structure and exact-net
proofs were reread. The proof uses monotonicity of the stated bound in rank
instead of the blueprint's optional isometric padding; it does not claim a
new padded chart. Existing BBI/BGP and intrinsic source/errata qualifications
are retained in the linked records.

This is the COMPLETE local curvature-1/dimension-to-covering producer with
the written256R margin. Growing-region tails, curvature parameters c_i->0,
and the final SAME-limit extraction/comparison/dimension assembly remain.
In particular, general curvature weakening from0<=kappa<=1 to1 is not yet
proved by CurvatureWeakening.lean (that leaf proves zero-to-kappa weakening).
No such premise is silently discharged here. The separate sharp8R/KL route,
global one-dimensional classification and PC migration bindings remain.
Blueprint207 and earlier mathematical leaves are unchanged.

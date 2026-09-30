# AC04: exact chart-based internal nets

Three public theorems in two leaves assemble AC04 with its EXACT constant
N(n,L,R,epsilon)=(1+ceil(4 L^2 sqrt(n) sinh(2R)/epsilon))^n.
The ceiling is the natural-number ceiling. The resulting finite net is
internal to the original closed R-ball and covers it with strict distance
less than epsilon, slightly stronger than non-strict epsilon coverage.
Here n>=1, L>=1, R>0 and epsilon>0. The chart is the actual map on an open
ball B(q,delta0), centered at zero, with the stated upper/lower ambient-distance
bounds; its radius delta0>0 is arbitrary and does NOT appear in N.

The metric core accepts an actual radial contraction into B(q,delta),
0<delta<delta0, with lower factor delta/sinh(2R). Composing with the chart
bounds its norm by L*delta and its pairwise distance below by
K=delta/(L*sinh(2R)) times source distance. The accepted finite-box packing
proof bounds every finite epsilon-separated subset by
(1+4*(L*delta)*sqrt(n)/(K*epsilon))^n. Exact field arithmetic cancels delta,
and the natural ceiling yields precisely N. The accepted bounded-greedy
proof then constructs an INTERNAL net of that cardinality. No compactness
of the target chart image, map continuity, volume bound or hidden finite
packing assumption is substituted.

The geometric consumer chooses delta=min(R,delta0)/2 and constructs the
actual contraction using the preceding AC03 path theorem. It needs ambient
completeness, actual length curves, local compactness of a larger open M-ball
with2R<M, and four-point comparison on B(o,2R). The source-facing256R
consumer derives that comparison from local AMBIENT curvature-1 neighborhoods
and uses the actual intrinsic construction and ALG06. Thus the chart and
original local curvature inputs now produce the uniform net bound. There
is no uniform lower bound on chart radii and no global source properness
assumption. The separate sharp8R/KL input remains distinct.

Sources checked: blueprint207A AC04 full2232-2269 and implementation note
2271-2277, AC03 full2193-2230; accepted EuclideanPacking and FiniteBoxPacking
full proofs, and FiniteNets' bounded-greedy proof lines45-76. The exact
natural-ceiling order fact in pinned Mathlib Algebra/Order/Floor/Semiring.lean
164-185 was read. BBI10.6.2 and its curvature-normalization qualification are
reused from the preceding source record; no general-curvature coefficient
is imported. These are explicit proof-derived net interfaces, not a claim
of a new cited volume-comparison theorem.

The nearby chart producer AC07/AC29 and full original-input growing-region
compactness remain separate. Smooth chart specialization remains behind the
PC migration boundary. Singleton/n=0 treatment elsewhere is unchanged; this
AC04 theorem explicitly assumes n>0. Blueprint207 and earlier mathematical
leaves are unchanged.

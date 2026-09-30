# Global exact product models on the same pointed limit

Three public theorems in two leaves compose the five actual global factor
models with a supplied exact L2 product splitting. The general metric theorem
assumes completeness of the source, actual minimizing segments, nonnegative
four-point comparison, factor Hausdorff dimension at most one, the splitting
and a requested basepoint. It internally inherits completeness, segments and
comparison on the factor and applies global model existence there.

The resulting ONTO isometry has target E, E x_2 R, E x_2 [0,infinity),
E x_2 [0,L], or E x_2 AddCircle L, with L>0. The singleton factor is actually
removed using Mathlib's Lp product identity. EVERY source point retains its
original E coordinate. The transverse line/circle basepoint is zero; ray and
segment heights remain explicit, including interior basepoints.

The first pointed-convergence consumer assumes source polynomial covering
of exponent n, k<=n, n-k<=1, actual target geodesics/comparison and an exact
Euclidean k-splitting of THAT target. AC45 derives the factor bound internally.
The original growing-region consumer assumes complete source spaces, actual
short curves, nonnegative kappa_i tending to zero, radii tending to infinity,
local comparison and dimension<=n on those growing balls, n>=1 and n-k<=1.
It produces covering, k<=n, target segments and comparison internally. Properness
of the given limit is explicit and supplied by the accepted ALG07 extraction.
No second limit, subsequence or target is selected. Factor compactness,
noncompactness, endpoints, rays, charts and a model type are NOT assumptions.

Source checked: blueprint207A AC47 full4445-4501, AC48 full4503-4530 and
qualifications4532-4550. Actual accepted factor geometry, dimension, global
model and growing-covering proofs were read. Mathlib ProdLp.lean1148-1161
was read for the actual singleton-product isometry, at pinned revision
c55e6e786f49471c72fbddbec5415808896aec1e. Existing geometric/errata evidence
is reused unchanged. The source's maximal-splitting restriction is retained:
an exact one-splitting alone DOES NOT exclude the plane alternative.

This proves all product alternatives in the supplied-factor-dimension and
source-covering/growing-geometry scopes. A standalone original-global
Hausdorff-dimension<=2 corollary and specified-line assembly are still separate.
Model-class exclusivity, parameter uniqueness and maximal-splitting exclusion
are also separate formal statements. No smooth structure, line production,
approximate-splitting compatibility or completed Chapters3-4 is asserted.
Earlier leaves, blueprint207 and migration interfaces remain unchanged.

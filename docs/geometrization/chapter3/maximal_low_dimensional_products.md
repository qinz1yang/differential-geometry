# Maximal splitting excludes the extra Euclidean direction

Four public theorems and one definition in two leaves make AC48's maximality
qualification explicit. finSuccProdIsometry identifies EuclideanSpace R(Fin(k+1))
with the ACTUAL L2 product EuclideanSpace R(Fin k) x_2 R as a linear isometric
equivalence. It is built from Mathlib's finite-coordinate reindexing, sum/product
Lp isometry and genuine one-dimensional orthonormal basis, not the maximum-
metric Cartesian product or an arbitrary pullback metric.

An onto isometry X -> R^k x_2 R therefore gives an onto isometry X -> R^(k+1)
sending ANY chosen p to zero by actual translation. A second theorem produces
an actual pointed (k+1)-splitting, including a metric factor, basepoint, global
onto map and exact basepoint equation. Its singleton factor is the actual
subspace {x:X | x=p}, so it lives in the source universe and uses the inherited
metric. No nonemptiness choice or universe restriction is hidden.

The generic maximal-splitting consumer assumes complete geodesic nonnegative
geometry, dimH(X)<=n, n>=1, n-k<=1, a supplied exact Euclidean k-splitting,
a requested basepoint and absence of ANY pointed (k+1)-splitting with a metric
factor in the same universe as X. It returns the four remaining product
alternatives: R^k, R^k x_2 ray, R^k x_2 positive segment, or R^k x_2 positive
circle. Every old Euclidean coordinate and transverse basepoint convention is
retained. The real one-splitting consumer states the explicit AC48 version
for dimension<=2 and absence of pointed two-splittings, yielding line,
half-plane, strip or cylinder. The plane alternative is eliminated ONLY by
the supplied maximality hypothesis; its existence from an arbitrary one-
splitting is not denied.

Source checked: blueprint207A AC42/43 pointed onto conventions and AC48
full4503-4540, especially maximality4532-4535; unchanged original-global
product/dimension proof bodies. Mathlib Analysis/Normed/Lp/PiLp.lean861-886
and987-1011 (finite reindexing and genuine sum/product isometry), Analysis/
InnerProductSpace/PiL2.lean367-386 and638-662 (homeomorphism/isometry distinction
and singleton basis), and Analysis/Normed/Lp/ProdLp.lean1101-1118,1148-1161,
1195-1200 (actual product congruence and singleton removal) were read at the
pinned c55e6e786f49471c72fbddbec5415808896aec1e revision. The prior translation
source check is reused unchanged.

No maximality is derived from a mere splitting, strainer or approximation.
Approximate compatibility and Chapters3-4 remain unfinished. Earlier leaves,
frozen blueprint207 and migration interfaces are unchanged.

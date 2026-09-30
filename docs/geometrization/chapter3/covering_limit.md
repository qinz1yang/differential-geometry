# Polynomial covering rates on the same pointed limit

`CoveringLimit.lean` proves the quantitative transfer part of AC40 using the
actual `PointedGHConverges` and the AC38 `PointedBallApprox` constructor.

`PointedGHConverges.exists_internal_finset_net` fixes R>0 and delta>0.
If sufficiently late source closed (R+1)-balls have internal delta/4-nets
of cardinality at most a fixed real K, the existing limit's closed R-ball
has an internal strict delta-net with cardinality at most K. It chooses
epsilon=min(1/8,delta/16) and one index satisfying BOTH the approximation
and source-net requirements. The source index may depend on R and delta.
No common tail over all meshes is inferred. Cardinalities are compared as
real numbers without rounding the supplied bound.

`exists_internal_finset_net_of_polynomial_covering` assumes, on the source
closed (R+1)-balls, eventual eta-nets bounded by C*eta^(-d) for every
0<eta<=1, where C does not depend on eta or the source index. It gives
target delta-nets bounded by (C*4^d)*delta^(-d), for 0<delta<=1. The exponent
is a real number; the algebraic transfer does not require d>=0. The later
Hausdorff theorem explicitly assumes that nonnegativity.

`exists_internal_finset_net_of_ceil_covering` retains the sharper constant
from the blueprint. For integer n>=0 and B>=0, an eventual source bound
(1+ceil(B/(delta/4)))^n becomes the target bound

    (2+4*B)^n * delta^(-n).

This is proved directly using the ceiling inequality before converting to
a power-law rate. Substituting
B=4*L^2*sqrt(n)*sinh(2*(R+1)) yields the blueprint's
C_R=(2+16*L^2*sqrt(n)*sinh(2*(R+1)))^n. Converting the source bound to a
coarser polynomial estimate first would give a larger constant; that route
is not used for this specialization. n=0 and B=0 are included.

These are metric implications of actual covering estimates. There is no
curvature assumption, no dimension assumption on the target, and no claim
that curvature supplies the source covering estimates. Source properness,
source completeness, length structure, and continuity of approximations
are not required. Target completeness is inherited from the existing
project convergence predicate, not an extra covering argument.

Sources: blueprint207A AC38--AC40, lines4075--4210; the entire statement and
proof were read. Reused unchanged source/errata checks in
GEOMETRIZATION_BLUEPRINT/reference_checks_revision70.md: BBI1.7.7--1.7.8,
printed19--20/PDF34--35;1.7.17--1.7.19, printed22--23/PDF37--38; the packing
comparison BBI10.9.2, printed390--391/PDF405--406. The displayed constants
are the project's own AC04/AC40 calculation, not a silently imported
general-curvature formula. BBI SHA256:
4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971.
Retained July6,2024 erratum SHA256:
68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e.
No new remote errata retrieval or full-book audit is claimed.

The new module builds on Lean4.35.0-rc3 at the existing Mathlib pin. Exact
source hashes and declaration/axiom coverage appear in the shared manifest
receipt. The existing Chapter3 mathematical leaves remain unchanged.

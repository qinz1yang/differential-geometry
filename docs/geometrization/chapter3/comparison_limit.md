# Lower comparison on the same pointed limit

`ComparisonLimit.lean` implements the metric limit passage in AC37 and
combines it with the already proved AC38--AC40 dimension theorem. It does
not assume or assert the geometric producers of the source inequalities.

## Exact source and target contract

Let (X_i,p_i) be pointed metric spaces, with the actual project convergence
`PointedGHConverges p q` to the given metric space (Y,q). Let kappa_i>=0
converge to zero. The curvature convention is **minus kappa_i**; model
lengths in the hyperbolic cosine law are multiplied by sqrt(kappa_i).

The comparison input is:

    for every R>0, eventually in i,
      fourPointComparison kappa_i (ball(p_i,R)).

This is a literal inequality using three explicitly defined model angles
at a center and three outer points in the ambient metric. Each outer point
must differ from the center; outer points may coincide. The inequality
says the cyclic sum of the three angles is at most 2*pi. It is not an
opaque curvature certificate or an assumed conclusion about Y. For
positive kappa the numerical angle has a checked hyperbolic cosine law on
the domain of triangle side lengths; at kappa=0 it is the existing
Euclidean comparison angle.

The proved `fourPointComparison_of_distinct` adapter recovers this convention
from the blueprint's four-distinct-point inequality when kappa>=0. With a
repeated outer point, one comparison angle is zero and the remaining two
are at most pi. No additional geometric source assumption is hidden here.

The eventual threshold may depend on R. No common threshold for all radii,
no continuity of approximation maps, no global properness or completeness
of the sources, and no dimension assumption on Y is imposed by this
comparison theorem. Target completeness is inherited from the existing
project convergence predicate, although the finite-configuration argument
itself needs no target compactness or geodesic existence.

`PointedGHConverges.fourPointComparison_zero_of_eventual_comparison`
proves the literal curvature-zero inequality everywhere on that same Y.
`PointedGHConverges.quadratic_side_comparison_of_eventual_comparison`
then proves, for all a,b,z,v in Y and 0<=t<=1 with

    dist(a,z) = t*dist(a,b),
    dist(z,b) = (1-t)*dist(a,b),

the inequality

    (1-t)*dist(v,a)^2 + t*dist(v,b)^2
      - t*(1-t)*dist(a,b)^2 <= dist(v,z)^2.

These distance hypotheses apply to every point on every proportionally
parametrized minimizing segment. Coincident endpoints, t=0 or 1, and
v equal to an endpoint or z are included. The theorem does not assume
uniqueness of minimizing segments.

The sibling `fourPointComparison_zero_of_growing_balls` accepts eventual
ambient four-point comparison on ball(p_i,rho_i), with rho_i tending to
infinity. Restriction of the actual source inequalities supplies the
fixed-R input. Here rho_i is an **available comparison radius**; it must
not be confused with a radius on which only local curvature is known.

## Why the limit passage is valid

Fix a quadruple in Y. One bounded target configuration is lifted using the
existing actual pointed approximation maps. The source index sequence is
strictly increasing and is selected after the shrinking errors and the
eventual source-comparison conditions. Every pair distance converges to
its original target value. Positive central target distances make the
three central source distances positive eventually; outer labels need
not separate. Joint model-angle continuity then passes the three source
inequalities to the zero-curvature inequality.

Only the indices used to prove this inequality depend on the quadruple.
The target Y, its metric, basepoint and original pointed convergence are
unchanged. This is not a new extraction of a geometric limit for each
configuration.

## Combined extraction endpoint

`exists_geodesic_pointedGHConverges_of_covering_and_comparison` assumes:

1. A fixed real exponent d>=0 and, for every R>0, a constant C_R>0,
   independent of mesh eta and source index, such that for every
   0<eta<=1, eventually the source closed R-ball has an internal eta-net
   of cardinality at most C_R*eta^(-d).
2. Actual continuous source curves on the unit interval with partition
   variation less than dist(a,b)+epsilon for every epsilon>0.
3. Nonnegative kappa_i tending to zero and the explicit eventual
   fixed-ball comparison condition above.

Its conclusion constructs one Y, one metric, one q and one strictly
increasing subsequence phi. That same space is complete and proper,
is the pointed limit along phi, has Hausdorff dimension at most d,
satisfies global curvature-zero four-point comparison, has exact
minimizing metric segments, and satisfies the quadratic side inequality
for every admissible a,b,z,v,t. Completeness is included in the actual
`PointedGHConverges` conclusion. The dimension is Mathlib's `dimH`.

The source estimates are transported along the exact phi supplied by the
previous dimension/geodesic extraction theorem. There is no new abstract
limit, substitute metric, or postulated comparison property in its proof.

## Current blueprint route and remaining producers

The relevant bodies are blueprint207A AC34--AC37 at lines3788--4055,
AC38--AC41 at lines4075--4225, and ALG06--ALG07 at lines7542--7615.
The recorded source comparisons in revisions69,70,138 and140 were read
and reused for their unchanged claims. In particular, the current
geometric route is ALG06/ALG07 with the written 256R margin. Historical
AC36's sharper 16R statement remains separately source-qualified.

For this implementation, the finite target configuration lies in a
radius-M ball, its lifts lie in the radius-(M+2) source ball, and source
comparison is used on the radius-(M+3) ball. A future ALG06 producer can
supply that input from the radius-256(M+3) local-curvature region. The
growing-radius hypothesis allows this after fixing the configuration;
no uniform local comparison-neighborhood radius is needed.

Geometric production of the source covering and ambient comparison
estimates is still open in this branch. No completed AC36, ALG06/07,
AC41 under its original local-curvature hypotheses, or full MC18 theorem
is claimed. The new endpoint is proved under its explicit source inputs.

The inherited canonical Euclidean module is read and compiled unchanged:
`Geometry/Comparison/Toponogov/ComparisonAngle.lean`, SHA256
`0a98112af2a930008d5aab552a44c123f3075a3455a74723ff2012c879b8bf0a`.
The archived blueprint207A hash is
`277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`.
Its exact source conventions and the new model proof are documented in
`comparison_angles.md`; the finite lifting and direct triangle arguments
are in `finite_configuration.md` and `four_point.md`.

## Verification

The original three-declaration comparison-limit module compiled on the
pinned Lean4.35.0-rc3 / Mathlib c55e6e786f49471c72fbddbec5415808896aec1e
(2698 Lake jobs). The final common receipt records the final source hashes,
all registered module builds, and axiom closures, including the growing-ball
adapter. Independent review is in `comparison_limit_review.md`. No full
migrated PC root build or new blueprint revision is claimed.

The final common gate passed for all 40 registered development modules
(2728 Lake jobs) and all 426 owned declarations. It rejected admissions and
new axioms and checked every source hash, existing-leaf preservation, exact
environment pins and registered imports. All axiom closures contain only
`propext`, `Classical.choice`, and `Quot.sound`.

A separate Lean consumer check instantiated the full combined extraction
theorem on the constant one-point source family with d=0, C_R=1 and
kappa_i=0. Actual singleton nets and constant curves supplied its inputs;
the constructed output retained properness, convergence, dimension zero
and global comparison. The model-angle module also passed explicit
angle-zero and angle-pi limiting applications. These are scoped consumer
checks in addition to the proofs, not a full migrated-root test.

The required original blueprint static audit was rerun; it stopped at a
historical absolute archive path that predates the workspace relocation.
The exact failure is retained in `evidence/blueprint_static_comparison.log`.
No historical source record or audit assertion was bypassed or rewritten.
This document-audit limitation is separate from the executed Lean checks.

# Dimension of the same constructed pointed limit

The development in `DimensionLimit.lean` is the metric/measure part of AC40.
It consumes actual finite covering estimates and the compiled Chapter3
extraction theorem, without defining a provisional curvature predicate.

## Exact source hypothesis

For a fixed real exponent d>=0 and pointed metric spaces (X_i,p_i), assume:

    for every R>0 there exists a finite real C>0 such that
      for every 0<eta<=1, eventually in i,
        the closed R-ball about p_i has a finite internal eta-net F,
        with (card F : real) <= C * eta^(-d).

The covering distances are witnessed and non-strict. The constant C may
depend on R but not on eta or i. The eventual starting index may depend on
both R and eta. The sources need not be complete, proper, compact, or length
spaces for the dimension theorem. Distances are the supplied finite real
ambient metrics; no intrinsic ball metric is substituted.

## Existing pointed limit

For any actual `PointedGHConverges p q` with that source hypothesis,
`PointedGHConverges.hausdorffMeasure_univ_zero_of_polynomial_covering`
proves H^s(Y)=0 for every s>d. This statement uses the standard Borel
measurable structure, but requires no measurability hypothesis on individual
covering sets. `PointedGHConverges.dimH_le_of_polynomial_covering` proves
`dimH (univ : Set Y) <= ENNReal.ofReal d` without measurable-space binders.

The proof takes a source estimate at R+1, transfers delta/4-nets to the same
target closed R-ball, and obtains constant C*4^d. AC39 applies to the actual
ambient subset. The union of closed balls with radii 1,2,3,... is the whole
finite-distance space, so countable-union vanishing/dimension gives the
global conclusion. Constants need not be uniform across those balls.
No target dimension, curvature, or properness assumption is inserted.
Target completeness is already part of the project convergence predicate.

## Actual extraction endpoint

`exists_pointedGHConverges_dimH_le_of_eventual_polynomial_nets` takes only
the source hypothesis above and produces one strictly increasing subsequence
and one complete proper pointed limit with dimension at most d.

Its proof first supplies MC13's exact eventual finite-net hypothesis. For
an arbitrary requested eta>0 it uses mesh min(eta,1), takes the natural
ceiling of the finite real cardinality bound, and keeps the centers inside
the specified source ball. The compiled MC13 theorem constructs the limit.
The original polynomial estimates remain eventual along its strictly
increasing subsequence. The already proved dimension theorem is then
applied to this very same limit, metric, basepoint, and subsequence.

`exists_geodesic_pointedGHConverges_dimH_le_of_eventual_polynomial_nets`
additionally assumes actual near-short continuous curves in every source,
using Mathlib partition variation. The same constructed limit also has an
exact continuous metric segment between every pair of points. This is an
application of the completed Chapter3 midpoint-transfer and geodesic
realization theorems. No separate limit is chosen for the geodesic claim.
Coincident endpoints, d=0 and nonintegral d>=0 are included.

The covering-rate theorem is not the geometric producer of those covering
rates. Chapter4's curvature-to-covering inputs and lower-comparison
stability remain separate; thus MC18 is not declared fully proved here.
The direct ceiling-bound estimate retaining AC40's sharper displayed
constant is documented in `covering_limit.md`.

## Direct ceiling-family consumer

The further public theorems
`PointedGHConverges.hausdorffMeasure_univ_zero_of_ceil_covering` and
`PointedGHConverges.dimH_le_of_ceil_covering` accept the source bound in
its original integer form:

    card F <= (1 + Nat.ceil (B(R)/eta))^n,

with n a natural number and B(R)>=0 for R>0. For every radius and mesh,
such nets need only exist eventually. No continuity or monotonicity of B,
and no common starting index over all meshes, is assumed. The limit-ball
proof uses exactly C_R=(2+4*B(R+1))^n before the countable exhaustion.
Hence these are actual compiled consumers of the sharp ceiling transfer,
including n=0 and B=0. They conclude H^s(Y)=0 for s>n and dimH(Y)<=n.
The substitution B(R)=4*L^2*sqrt(n)*sinh(2R) gives the printed AC40 constant;
producing the corresponding source nets geometrically remains separate.

## Sources and verification

Read the full AC38--AC41 statements and proofs in blueprint207A,
lines4075--4225, and the existing complete source comparison
`GEOMETRIZATION_BLUEPRINT/reference_checks_revision70.md`. The source
locators and fixed BBI/erratum hashes are recorded in `covering_limit.md`
and `polynomial_covering.md`. This composition preserves those contracts;
it does not silently infer comparison or dimension from qualitative GH
compactness. Independent source and mathematical review is in
`dimension_review.md`.

The module compiled on Lean4.35.0-rc3 (2656 Lake jobs). The common manifest
gate records the exact source hashes and all declaration axiom closures.
The final combined gate passed for all 36 branch modules and 380 owned
declarations. Separate Lean consumer checks instantiated the extraction
theorem on the constant one-point family with d=0, C=1, and instantiated the
ceiling-family dimension theorem with n=0, B=0. Both checks elaborated with
actual singleton nets, including the extraction theorem's proper-limit output.
No full migrated PC root build or new blueprint revision is claimed.

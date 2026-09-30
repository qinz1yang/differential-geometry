# Comparison radii and enlargement for the same germs

Ten public theorems and one definition in four leaves provide the comparison-
radius and germ interfaces needed for ALG04. The finite capped radius is the
ACTUAL supremum of nonnegative good endpoint radii bounded above by M. Its
bounds, strict-below comparison property, positive local lower bounds and
upper bound from a failing hinge are proved directly. No attainment of the
supremum is assumed.

This is a finite encoding of the truncated-radius argument: the development
uses the supremum of admissible radii in[0,M] directly. An unbounded extended-
real radius C and an equality to min(C,M) have not been introduced or assumed.
The proved properties are the ones needed for the almost-minimum argument.
For a local four-point neighborhood and M>0, one pair of positive constants
controls all capped radii in a neighborhood. A failing actual hinge with
first endpoint p bounds the capped radius there by its actual arm sum.

The segment adapter turns each supplied positive-parameter minimizing germ
into an actual isometry on the CLOSED interval. It sets the zero parameter
to the specified center and agrees with the original curve at EVERY positive
parameter through its full length. It also permits length zero in the metric
adapter. The hinge adapter uses these same two germs and proves exact equality
of the canonical angle, without imposing a condition on irrelevant original
values at zero or outside the positive interval.

The endpoint enlargement theorem now proves the FULL endpoint comparison
property at radius ell from comparison at p and all q in B(p,ell) below
2ell/3. Join availability is required for those q and centers of arm sum
below ell; local four-point neighborhoods are required in B(p,ell). It
applies ALG02 to the SAME original germs through the proved adapter. This
turns the chosen-segment theorem into the universal endpoint property used
by the comparison-radius definition. Completeness is not used at this stage.

Fresh source reading: frozen blueprint207A ALG04/05 bodies7447-7534 and
context through7605; pinned AKP vol1 ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245
 defs-CBB.tex1131-1218, including comparison radius and the geodesic-case
almost-minimum argument. The general ultrapower route is outside this
implementation. Mathlib Order/ConditionallyCompleteLattice/Basic.lean356-374
was checked for the nonattainment-safe supremum witness. The retained
July12,2026 author errata text and pinned erratum.tex were reread, with the
archive/source/published numbering distinctions from revision140 retained;
no relevant correction to this adopted route was found. Exact hashes and
locators are in the source record.

Blueprint207 and prior mathematical leaves remain unchanged. ALG04's final
almost-minimum contradiction and global comparison consequences still need
assembly. Intrinsic/buffer adaptation, endpoint-free recognition and uniform
curvature-to-covering production remain open. The PC migration boundary is
unchanged.

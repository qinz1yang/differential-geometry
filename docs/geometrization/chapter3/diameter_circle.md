# Onto isometry with the actual quotient circle of circumference2D

Seven public theorems and one definition in three leaves construct the
actual metric-circle isometry from the diameter-arc geometry. The target
is Mathlib's normed additive quotient AddCircle(2D), with its existing
quotient metric, not a new metric defined by pullback from X.

Two general quotient-distance theorems first prove that for L>0 and
0<=a<=L, the norm of the class[a] is min(a,L-a), and that representatives
whose difference has absolute value<=L/2 have exactly their usual real
distance. Endpoint and half-period cases are included. These use the
actual pinned quotient-norm formula and period identity.

The coordinate assigns +distance from the first diameter endpoint to
points in the full first segment range, and -distance to exterior points,
then takes its class modulo2D. Under actual minimizing segments, an open
first segment interior, global pairwise distance bound D>0 and four-point
comparison at any kappa>=0, this coordinate is an isometry. The proof
checks both on-arc, both exterior and mixed cases. The mixed case is exactly
the shorter of the two endpoint routes, matching the quotient norm.

An actual opposite arc with the same endpoints and exterior open interior
maps to its negative parameter at EVERY parameter, including0 andD. AtD,
+ D and - D are identified by the genuine period2D relation. The two arcs
supply representatives in[-D,D] for every quotient class, so the coordinate
is surjective. A true isometry equivalence X~=AddCircle(2D) follows, with
both full parametrizations retained. Finally, a single exterior point to
the first diameter segment suffices: the accepted opposite-arc theorem
constructs the second arc internally, and the new theorem returns the onto
circle isometry aligned with the given first segment.

Source check: blueprint207A AC47 full4445-4501 specifies the real quotient
circle, the shorter-arc metric and zero-normalized circle basepoint. The
accepted diameter/opposite-arc proof records remain. Mathlib at c55e6e786f49:
Analysis/Normed/Group/AddCircle.lean40-43,66-137 was read for the actual
normed quotient, norm formula and half-period equality; Topology/Instances/
AddCircle/Defs.lean205-229,301-306,461-476 for subtraction, period and actual
representatives. Their proofs were checked, not merely theorem names.
The identification is explicit and does not invoke a classification theorem
or silently transport a metric. Existing geometric source/errata records
are unchanged.

A compact-space wrapper must still choose the diameter segment, distinguish
its surjective interval branch and normalize an arbitrary basepoint; the
nontrivial/singleton cases must then be joined with noncompact recognition.
Full AC47/AC48 is not yet claimed. Earlier leaves and blueprint207 stay fixed.

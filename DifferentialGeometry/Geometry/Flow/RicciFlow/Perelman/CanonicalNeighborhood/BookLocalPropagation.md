# BookLocalPropagation

Claim 6a1d50d2-e512-4d31-8eae-ccbf4bf60c64. Source-only during Chapter23's
compiler/artifact/root window; initially UNVERIFIED.

The normalized sequence already supplies actual carrier [-2*depth,0],
regular interior, good witnesses above scalar threshold2 on [-depth,0],
and the rescaled pinching function. Apply ClosedWindowScalarPropagation
with Q=1 directly to these actual normalized flows. The doubled carrier
provides the needed left neighborhoods, including time0, and depth tending
to infinity supplies depth>=2c eventually. Reuse the native pinching lower
bound and curvature-operator norm conversion with coefficient4*sqrt3.

The constants come from WindowedGoodPointBounds, before the source sequence.
The original negative scalar error and explicit Phi-dependent tensor bound
are preserved. The book's uniform vanishing error clause follows separately
from the existing exists_pinching_error_lt and the actual scale sequence.
Only the final book endpoint consumes Chapter23's named model curvature
obligation; no Chapter25 argument is replaced by an upstream placeholder.
Integration target: replace the body of the original
Chapter25Extension.local_propagation with book_local_propagation after the
new artifacts pass. Its type is preserved exactly; the normalized sequence
itself discharges regular-interior and left-neighborhood conditions. Keep the
more general arbitrary-carrier good_point_derivatives slot distinct.

Acceptance fixture prepared, not yet run:
E:/lean-tools/chapter25-book-20260910/BookLocalPropagationAxioms.lean.
It prints all seven new publics and all eleven original Extension endpoints,
then traces the exact admission frontier of both local-propagation endpoints
and the explicit-model-bound producer. The intended frontier is empty for
the latter and only chapter23_modelCurvatureBoundNearBase for the endpoints.

Accepted 2026-09-11: saved check1 EMPTY (24.8s), named build1 (32.9s); all five publics freshly audited. Four are standard-only; book_local_propagation has exactly the named Chapter23 model-curvature ancestor. The original Extension body now uses this proof with an unchanged statement. The final audit fixture also includes CanonicalRadialReserve, so its scope is eight new publics plus eleven original Extension endpoints. Receipt: E:/lean-tools/chapter25-book-20260910/book-local-propagation-completion.json.

Landed in c2c9b9dc1040a88ca041fbad0fa0028a1e04fd08; this batch's ordinary file claim was released after landing. Current compiler ownership is in WORKING_STATUS.md.

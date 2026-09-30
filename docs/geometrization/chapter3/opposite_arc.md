# An actual opposite diameter arc and coverage of the whole space

Four public theorems in three leaves continue the compact AC47 route.
Two isometric segments[0,D]->X with the same two endpoints are considered,
the first having open interior. If ANY point on the second lies outside
the entire first range, EVERY interior point of the second lies outside.
The second segment's open parameter interval is preconnected; if its image
met the first interior, the accepted no-exit theorem would force it through
a shared endpoint at an interior parameter, contradicting its isometry.
No geodesic uniqueness, curvature or completeness is assumed for this step.

A separate metric theorem constructs an arclength isometric segment from x
to y passing through z whenever d(x,z)+d(z,y)=d(x,y). Both original minimizing
segments are concatenated and reparametrized on the actual endpoint distance.
Zero-length arms and coincident endpoints are retained; z's exact parameter
is d(x,z), and both endpoint identities are proved.

Under global four-point comparison at any kappa>=0, actual minimizing
segments, an open diameter-segment interior and a global distance bound D,
every point outside a diameter segment lies on a constructed SECOND
isometric[0,D] arc with the same endpoints. The preceding diameter sum gives
the necessary distance additivity for concatenation. Its open interior is
disjoint from the full first range, and the two full ranges cover ALL of X.
For coverage, an exterior y has endpoint coordinate strictly between0 andD;
the point with that coordinate on the second arc is exterior too, and the
accepted exterior distance equality makes its distance to y zero.
The standalone coverage theorem only needs equality of the initial endpoints;
it does not assume an unused terminal-endpoint alignment. The constructed
opposite arc does retain both endpoint identities.

Source bodies checked: blueprint207A AC47 full4445-4501 and ALR03 full7134-7161,
with the preceding diameter-segment source checks. Accepted SegmentConcatenation,
SegmentExteriorDistance and DiameterSegment proofs were inspected in full for
exact endpoints, parameter restrictions and curvature hypotheses. Mathlib's
actual open-interval preconnectedness and subtype transport were checked.
This is the explicit diameter/opposite-arc decomposition recorded at the
preceding milestone, not a claim to implement the blueprint's maximal chart
continuation proof verbatim. Existing source/model errata checks are retained.

These are actual arcs and full-space coverage. The onto isometry with the
standard quotient circle of circumference2D remains to be constructed;
compact classification and full AC47/AC48 are not yet claimed. Earlier
leaves, blueprint207 and migration-dependent interfaces remain unchanged.

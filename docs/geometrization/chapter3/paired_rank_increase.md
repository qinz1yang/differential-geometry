# AC26: actual paired rank increase

Six public theorems in five leaves prove the quantitative rank-increase
construction. A finite-difference estimate for balanced endpoints converts
near equality of the actual first-anchor coordinates into an angle-difference
bound. Four-point comparison and AC24's two complement bounds control all
four cross angles. The exact project error is
E=2*delta+3*(beta/100)/2+4*pi*sqrt(K*s)+pi*sqrt(epsilon+K*s)/2 < beta/10,
with epsilon=(beta/(100*pi))^2 and K*s<=epsilon.

`PairedComparisonPacket.exists_extension_of_near_coordinates` takes an actual
uniform packet on V inside the common comparison domain Omega, all original
anchors in Omega, common distances in [a0,A], explicit short curves, positive
L=d(x,y)<=min(1,a0/2,epsilon/K), closedBall(x,L) contained in V, and each first
coordinate difference at most epsilon*L. It constructs z IN V, exact balance
of its distances to x and y, L/2<=d(x,z)<3L/4, and the actual packet extended
by the pair (x,y), with every extended anchor still in Omega. Old anchors are
unchanged. The extension is indexed by Option iota; for finite iota this
increases cardinality by exactly one. The theorem returns the packet itself,
not an existential unspecified higher-rank object.

The proof requires only 0<beta<=1 and 0<=delta<=beta/100. This is weaker than
AC26's 0<beta<=1/(200(m+1)), so it applies to that exact contract. No index
finiteness or positive old rank is needed for this step; the empty index
case supplies a useful nonvacuous initial pair. For later AC27, finiteness,
positive rank and the sharper quality restrictions remain explicit. No
uniform neighborhood, injectivity or chart is claimed yet.

Blueprint207A AC26's complete statement/proof (lines3338–3402) and the
AC24–29 consumer route were reread. The unchanged BGP/BBI and errata checks
recorded in angle_reversal_midpoint_sources.json are reused, including the
corrected strict almost-midpoint angle direction. The exact curvature-minus-
one estimates are proved here; no single-center strainer complement theorem
or curvature-zero shortcut is imported. Earlier mathematical leaves and
blueprint207 are unchanged; the migrated foundation is untouched.

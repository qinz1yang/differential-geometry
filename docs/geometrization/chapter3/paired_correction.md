# Paired geometric correction: AC21

Three public theorems in two new leaves prove the short-angle estimate
and AC21's actual geometric correction. Two private scalar helpers are
included in the axiom audit.

The main theorem takes an actual four-point comparison on a specified
subset Omega, a working subset V contained in it, an ordered pair of
anchors u,v, and a set W of other anchors, all in Omega. Throughout V,
all these anchor distances lie in [a,A], opposite-pair angles exceed
pi-delta, and angles from each other anchor to both u and v exceed
pi/2-delta. With a>0, 0<delta<=1/100, a closed t-ball at x contained
in V, and 0<t<=min(1,a/2,delta^2/K), it produces an actual y in V with

    d(x,y)=t,
    (1-delta^2)*t <= d(x,u)-d(y,u) <= t,
    (1-3*delta^2)*t <= d(y,v)-d(x,v) <= t,
    |d(y,c)-d(x,c)| <= 6*delta*t  for every c in W.

Here K is EXACTLY 4*cosh(A+1)/sinh(a). The ordered pair may be supplied
in either order. The other-anchor set need not be finite; no count or
openness hypothesis is used in the move itself. This is a modest
generalization of the finite paired-packet contract, not a different
curvature predicate. No tangent space, compactness, completeness or
minimizing segment is assumed. Arbitrarily short continuous curves
with their actual metric variation are the length-space input.

The proof constructs y by AC20. All subsequent four-point comparisons
are performed at x or y with actual anchors in the SAME Omega. Positive
anchor bounds exclude central-point coincidences, and d(x,y)>0 excludes
coincident centers. The existing four-point definition already allows
repeated noncentral points, as justified in its original adapter. AC19
at both endpoints gives the required finite differences. The scalar
estimate x^2/4<=1-cos(x) on [0,1] controls the near-pi angle. The exact
three advertised coefficients, including 6 for every cross coordinate,
are retained.

## Source checked

Reopened blueprint207A's paired-packet definitions and AC21's entire
statement/proof, lines3055–3121; AC19–AC20 and AC22's consumer were read
alongside it. The model cosine-law source, BGP5.8 and BBI10.8.15 source
identities and author-errata qualifications are unchanged from the
preceding records and are reused. These negative-curvature constants
are project estimates, not printed BGP/BBI constants. The Lean proof
uses no omitted source result or unproved curvature adapter.

## Remaining scope

The supplied packet must still be localized from pointwise data, and the
finite distance-map application must be assembled with AC22 and AC23.
Thus AC21 is proved, but full AC23 and the rank-exclusion/injectivity
route are not claimed by this checkpoint. Blueprint207, prior mathematical
leaves and PC migration interfaces remain unchanged. See the review and
evidence for executed checks and an actual one-dimensional packet example.

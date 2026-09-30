# Closed segment neighborhoods and distances outside an isometric ray

Four public theorems in three leaves begin a noncompact route to AC47.
Actual metric segments between all pairs and openness of every isometric
finite-segment interior imply a CLOSED-ball version of the accepted local
segment equality, including the boundary points, whenever the positive
radius fits inside the parameter interval. Closed-ball density from actual
segments and compactness of the finite segment image justify the passage
from open to closed balls; ambient completeness is not assumed.

Consequently an actual isometric ray gamma:[0,infinity)->X satisfies
closedBall(gamma(R),R)=gamma([0,2R]) for every R>0. For every point x OUTSIDE
the entire ray image, and every t>=0, the exact distance formula is

    d(x,gamma(t)) = d(x,gamma(0)) + t.

This is proved, not assumed as a nonbranching property. Choose R larger
than both d(x,gamma(0)) and t. A minimizing segment from gamma(R) to x
has length greater than R; its radius-R point lies at gamma(0) or gamma(2R)
by the closed-ball identity. The latter option contradicts the distance
bound to x. The segment therefore passes through gamma(0), giving the
formula at R and then at t by both triangle inequalities. No completeness,
properness, curvature, ray-production or global-classification premise is
hidden in these metric statements.

A separate comparison theorem works on ANY specified four-point comparison
set at curvature parameter kappa>=0. If p lies between x and z and also
between y and the SAME z!=p, then

    d(x,y) = |d(x,p)-d(y,p)|.

The two straight model angles are pi, so the four-point condition forces
the third angle to zero. The accepted inverse model-side identity gives
the exact distance, including x=p or y=p through separate branches. This
uses the actual model formula for arbitrary kappa>=0, not an unproved
curvature-monotonicity result or a global geodesic assumption.

Source bodies checked: blueprint207A AC46 full4421-4428 with source
conventions4430-4443; AC47 full4445-4501; ALR03 full7134-7161 and ALR04 full7163-7195. The accepted
SegmentNeighborhood, ClosedBallDensity and SegmentConcatenation proofs
were reread, as were ModelSide's zero-angle and inverse comparison-angle
identities and FourPoint's actual definition. Prior AKP local-recognition
and model/errata checks remain unchanged. The closed-ball/ray argument is
a new explicit formal proof decomposition toward the noncompact branch;
it is not attributed verbatim to the blueprint's continuation proof.

These results do NOT yet construct a ray from noncompactness, construct a
global signed coordinate, classify an endpoint-free space, or treat the
periodic circle branch. Those remain the next obligations. The completed
endpoint branch is unchanged, as are blueprint207 and all earlier leaves.

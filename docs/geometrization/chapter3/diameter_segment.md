# Exact exterior distances for a diameter-realizing segment

Five public theorems in three leaves provide an explicit compact-case route
toward AC47. A continuous map from ANY preconnected space that meets an open
isometric-segment interior and also leaves the full segment range must pass
through an endpoint. This uses the segment's compact closed image and the
actual open interior, not uniqueness of geodesics or a tangent argument.
For a geodesic space and an isometric sigma:[0,D]->X with open interior,
every x outside its entire range satisfies, for ALL t in[0,D],

    d(x,sigma(t)) = min(d(x,sigma(0))+t, d(x,sigma(D))+D-t).

Both endpoints and D=0 remain in this statement. An actual minimizing
segment from x to sigma(t) hits an endpoint; its exact additivity supplies
one candidate route, and the two triangle inequalities give the minimum.
Neither curvature nor completeness is required.

If moreover EVERY pair of points in X has distance<=D, the balanced
parameter t=(d(x,sigma(D))+D-d(x,sigma(0)))/2 lies in the segment. Evaluating
the exact formula there shows that every exterior point satisfies

    d(x,sigma(0)) + d(x,sigma(D)) = D.

Under four-point comparison at ANY kappa>=0, two exterior points x,y then
satisfy d(x,y)=|d(x,sigma(0))-d(y,sigma(0))|. A sufficiently short positive
point on sigma is a common opposite point for both; the accepted exact
common-opposite theorem gives this equality. No compactness assumption is
hidden in these diameter-bound statements. Separately, a nontrivial compact
geodesic metric space has a positive-length isometric segment realizing
a bound for ALL its pairwise distances, by the actual extreme-value theorem.

Source reading: blueprint207A AC47 full4445-4501 and ALR03-04 full7134-7195;
pinned AKP dim.tex874-951 was reopened to distinguish its local recognition
argument from a global classification. The present balanced-parameter and
common-opposite proof is a new explicit decomposition, not attributed
verbatim to AKP or the blueprint continuation proof. Accepted segment
no-exit, common-opposite and arclength-conversion proof bodies were read.
Mathlib's actual extreme-value proof and compact product hypotheses were
checked. Existing local-recognition/source-model errata records remain.

The second arc, its surjectivity, and the onto metric-circle isometry remain
to be assembled. This milestone does not claim compact classification,
full AC47/AC48 or completed Chapters3-4. Earlier leaves and blueprint207
remain unchanged.

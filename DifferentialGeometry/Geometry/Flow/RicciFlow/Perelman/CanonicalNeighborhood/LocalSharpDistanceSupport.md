# LocalSharpDistanceSupport

Owner Chapter25; claim 9eabca0f-025f-402f-9b33-2fb4a187ee11.
SOURCE-ONLY during Chapter23's compiler window. No verification yet.

Adapt the native SharpDistanceSupport route with sectional curvature assumed
only at points on minimizing paths between the two endpoints. The arbitrarily
short Calabi shift and the sharp radial Hessian comparison are reused unchanged.
Two segment-length upper bounds and the triangle inequality show every point
of the Calabi tail lies on a minimizing path between the original endpoints.

Do not reuse calabiData_of_tail merely to obtain the support value/gradient:
its Ricci comparison input covers an extension beyond the terminal point.
Instead prove the touching value and upper-support property directly using
the same exponential branch. The new statement needs no unit-gradient output;
it retains the actual gradient in the sharp radial Hessian correction, which
is exactly what the squared-distance convexity calculation consumes.

Completeness here belongs to the auxiliary metric. This leaf does not assume
global nonnegative curvature for it, and does not by itself prove the local
convexity or the original end-angle card.

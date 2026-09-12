# CompleteTriangleEquality

Owner: Chapter25 continuation; claim ee840c30-7b59-47bc-81c7-9e0c8e0106df.
Verified 2026-09-09 15:55 UTC: focused5 EMPTY (15.192s), named1 lint-clean
(26.542s), fresh audit1 (14.107s), all four publics depend only on propext,
Classical.choice and Quot.sound. Source SHA256
799868c9b4faf995b77d2729b654e2a232a86d027e4fac1d8891bbd8d27ea312.

Use the native unit minimizing vector producer, broken-minimizer velocity
matching, and intrinsic geodesic continuation. Equality in the triangle
inequality forces a unit geodesic to continue to the third vertex. Inside
the native exponential diffeomorphism radius, two unit initial vectors with
the same endpoint therefore coincide. Every point on a merely metric segment
can be treated as the middle vertex, identifying the entire short segment
with one actual smooth intrinsic geodesic. A fourth producer identifies a
two-sided metric segment using the exponential radius only at its middle:
continue a minimizing geodesic from the left endpoint through the middle,
then use middle-point exponential injectivity for both halves. No
differentiability of the metric segment is assumed.

The complete metric hypotheses here are real. FiniteHornLocalCompletion is the
separate producer of a legitimate local complete metric; applying this result
to the original incomplete horn directly would be invalid. The planned next
step in FiniteHornRayRegularity uses both sides of an interior ray point to
obtain a two-sided smooth germ; extendible-ray uniqueness follows later.

Lean detail: for continuation at a new base point, use congrArg with the
velocity explicitly typed in the model space E. Rewriting a term whose
velocity is already annotated TangentSpace at the new base fails under
implicit transparency despite model-level definitional equality.

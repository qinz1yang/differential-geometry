# FiniteHornRayApproximation

Owner Chapter25; four-file claim acbb9f06-0df5-4b51-b66d-0b0bc9bf8f3f.
SOURCE-ONLY during Chapter23's window. No verification claim yet.

Target is the complete existing RayApproximation record: actual common bases,
whole smooth minimizing arms, closed nested tail buffers, all cross-connectors,
monotone parameters on arbitrary requested closed intervals, and simultaneous
uniform base/parameter/point/pair-distance errors. Do not substitute endpoint
convergence for any of these fields.

Choose a geometric cutoff D from ApproximatePair in any prescribed outer tail,
retain the actual connector index as an equality, return d=D/4, and for each
ray set R=min(ray.length,D/2). Truncated radii R*(1-eps(n)/2), with
eps(n)=1/(n+1), are positive and strictly inside both the ray and cutoff.
Apply the actual arbitrary-tolerance pair producer once for each n. Parameters
L(n)*min(s,r(n))/r(n) stay on the actual arms and converge uniformly to s on
the requested interval. Both position errors are less than
eps(n)+(R-r(n)); four triangle inequalities give the pair-distance error.
This handles hi=ray.length and even a singleton terminal target interval.

The prescribed outer index is required by the next local comparison: choose
it inside the compact-completion producer's deep tail before constructing the
arms. Hard-coding outer=0 would lose this containment. The original named
depth producer is retained by specializing the stronger result to outer=0.

The resulting producer retains CommonArms' explicit sufficiently long collar
condition. Its threshold is chosen before g,H for fixed W. Do not count the
original unqualified finite_horn_ray_approximation slot as closed merely from
this result; uniformity in a subsequently constructed W and the recorded
raw ambient/source defects remain distinct obligations.

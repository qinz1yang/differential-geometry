# Padded midpoint transfer and its limit consequence: MC21 / MC14

`PointedBallApprox.exists_approximate_midpoint` assumes a source metric
space has approximate midpoints for every pair and every positive error.
For an approximation on radius4M+4, with M≥1, both target endpoint radii≤M,
and ε<1/4, it produces a target point whose two distances are strictly less
than half the endpoint distance plus4ε.

This proves the metric part of MC21 under the weaker sufficient
approximate-midpoint assumption. The source's two coverage preimages are
used to choose an ε/2-midpoint. A radial triangle estimate proves this point
lies inside the actual source domain before evaluating the approximation.
Maps need not be continuous; neither source nor target must be proper.
No claim that a restricted ball is itself a length space is made.

`PointedGHConverges.approximate_midpoints` consequently proves that the
limit has approximate midpoints if every source has them. Its radius and
accuracy choices are made for each fixed pair and tolerance; convergence
supplies one source index where the needed approximation exists. This is
not yet the length-space criterion or the geodesic construction. A separate
curve-length argument supplies the source hypothesis from a length space.

Source: master207A.tex `lem:metric-midpoint-transfer`, lines1480–1530 and
MC14's length-closure argument; the displayed domain/distortion argument was
read for this implementation. The choice of an approximate midpoint replaces
the blueprint's near-short curve plus intermediate-value step only after
that property is explicitly assumed. Existing source checks for BBI2.4.16,
7.5.1,8.1.9 and its erratum remain in the metric contract records. No new
unverified length-space equivalence is hidden in the signature.

The new compiled consumer `exists_metric_segment_of_source_curves` now discharges
the source midpoint assumption using CurveMidpoint and constructs actual segments
in a proper limit using GeodesicMidpoint. See curve_toolkit.md.

The additional compiled consumer `PointedGHConverges.arbitrarily_short_curves`
now proves the general complete-limit length-closure assertion, by applying the
completeness-only MC22 producer. No properness or local compactness is assumed
for this conclusion. See approximate_midpoint.md.

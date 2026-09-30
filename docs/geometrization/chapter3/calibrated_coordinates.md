# AC60: quantitative coordinate squeeze from opposite calibration

Three public theorems prove the finite estimate and uniform convergence of the
actual supplied scalar coordinates along the actual supplied approximation maps.
An onto isometry e aligns the supplied line gamma with the real axis in R x_2 Z.
For a 1-Lipschitz h, positive and negative source points calibrated up to eta and
nonnegative absolute excess E, whose images are within zeta of gamma(plus/minus T),
the coordinate error at every image within distance B of gamma(0), T>B, is at most

    E + eta + epsilon + zeta + B^2/(2(T-B)).

Here epsilon is the distortion error of the actual PointedBallApprox. The proof
uses both calibration directions, the actual Lipschitz inequality, distortion,
triangle inequalities and the established signed product estimates. No source
properness, completeness, geodesicity, curvature or dimension is assumed.

The sequential theorem assumes radii tend to infinity and epsilon, E and eta tend
to zero, and, for each fixed positive T and zeta, eventual existence of calibrated
points in the actual approximation domains. It yields convergence uniformly over
ALL points of each fixed source ball, using those same maps and coordinates.
It fixes B=S+1 and then T before taking the source index large; no limit exchange
or uniform convergence on growing balls is asserted. The third theorem specializes
to the actual signed distance coordinate d(o_i,a_i)-d(x,a_i), proving its Lipschitz
bound from the distance function, rather than accepting that bound as an input.
The endpoints a_i need not lie in the approximation domains.

Source body checked: blueprint207A AC58 5033-5085, AC59 5089-5139 and AC60
5148-5205, especially both signs and the order of quantifiers in the final squeeze.
The preceding product_busemann source check supplies the exact product bound and
negative positive-ray Busemann sign; its unchanged KL4.15 and BBI splitting source
records and retained errata are reused. Mathlib at pinned c55e6e786f49471c72fbddbec5415808896aec1e,
Topology/MetricSpace/Lipschitz 143-147, was read for the actual distance Lipschitz
proof. No new current-remote errata clearance is claimed.

This closes the metric squeeze step of AC60 CONDITIONAL on actual calibrated
points converging along an already aligned line. It does not yet produce those
points from almost-shortest curves, extract the limiting line from opposite
endpoints, or align several axes. Those producer obligations remain visible.
Earlier mathematical leaves, blueprint207 and migration interfaces are unchanged.

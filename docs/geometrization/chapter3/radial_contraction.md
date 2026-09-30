# AC03: exact radial contraction on actual chosen paths

Four public theorems in two leaves prove AC03's quantitative map estimate,
using the written ALG06 route. The finite radial estimate now includes zero
arms: if either endpoint is the center, its subpoint is also the center,
and tD/sinh(D)<=t gives the assertion directly. Both nonzero arms use the
accepted exact hyperbolic estimate. No continuity-of-triangles argument or
unproved limiting adapter is needed for these degeneracies.

For q in B(o,R/2), 0<delta<R and ANY supplied family of exact unit-interval
minimizing segments from q to the points of the CLOSED R-ball, evaluate the
same family at t=delta/(2R). If four-point comparison at curvature-1 holds
on B(o,2R), every resulting point lies in the OPEN delta-ball about q and
its pairwise distances are at least delta/sinh(2R) times the original distances.
All radial points remain in the same2R comparison domain. Repeated endpoints
and q itself are included; an exact segment ending at q is constant. The
map on endpoints is not asserted continuous.

The actual existence consumer constructs those paths using ambient completeness,
actual length curves and local compactness only of a specified larger open
L-ball with2R<L. The source-facing256R consumer uses local AMBIENT comparison
at curvature-1, transfers it to the actual intrinsic metric, applies ALG06,
and constructs the contraction. No source properness, uniformly positive
chart radius or global curvature is added. This supplies AC03 with the
ALG06 margin; the separate sharp8R/KL comparison input remains distinct.

Checked sources: blueprint207A full AC03 lines2193-2230 and AC04 lines2232-2269, with implementation note2271-2277,
AC02's radial domain and ALG06/07 unchanged; BBI AMS2001 printed369-371/PDF384-386,
with full Lemma10.6.2 and proof at printed370/PDF385, and retained July6,2024
errata PDF13. The formula on printed370 was visually inspected as well as
text-extracted. BBI prints -k, rather than sqrt(-k), in its general-curvature
coefficient; no correction for370 is listed on the inspected retained sheet.
That general normalization is not imported here. At the ONLY normalization
used by AC03, k=-1, this discrepancy disappears; our smaller explicit
coefficient delta/sinh(2R) is proved by the already checked cosine-law and
convex-sinh algebra. No assertion of a current remote errata version is made.

The preceding RadialModel and FiniteRadialComparison source checks and the
actual local Hopf--Rinow proof are reused unchanged. Exact source hashes and
locators are recorded separately. AC04's chart-to-net assembly remains next;
no full original-input growing-region compactness is claimed. Earlier
mathematical leaves and blueprint207 remain unchanged.

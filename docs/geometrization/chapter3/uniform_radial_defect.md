# AC31: uniform finite-distance stability

Five public theorems in four new leaves prove AC31, including its actual
metric-space consumer. For fixed 0<a<=D, 0<t<1 and epsilon>0, one positive
eta works for EVERY metric space (in the theorem's universe), every common
curvature-minus-one comparison domain and every five-point configuration
in it with r,s in [a,D], dist(x,y)>=epsilon, exact inner radii tr,ts,
and radial segment defects between zero and eta. The conclusion is
((tD/sinh D)/2)*dist(x,y)<=dist(u,v). Eta is chosen BEFORE the metric
space/domain/points; no effective formula is claimed.

The contradiction proof uses the existing accepted
Metric.exists_pseudometric_subseq_tendsto_dist unchanged. It bounds all
pairwise distances of the violating five labels by 2D, extracts one
convergent array subsequence, and retains the limiting pseudometric. New
fixed-positive-parameter model-angle continuity applies when the adjacent
central sides are positive, including degenerate triangles. It proves
four-point comparison on the limit array exactly at those positive sides.

The limit array need not separate labels. A new general-index theorem
uses Mathlib's standard SeparationQuotient, with all matrix distances
preserved, and applies AC30 to the resulting metric space. The two radial
defects vanish along the selected subsequence, the outer separation remains
at least epsilon, and AC30 contradicts the limiting bad inequality. The
actual metric theorem forms the distance matrix of the supplied five points;
no alternate configuration is substituted in its output.

Blueprint207A AC31 full statement and proof, lines3641–3678, and AC32's
finite-set consumer were reread. BGP6.3 and BBI10.8.20 checks and correction
records from the accepted AC30 milestone are reused. This supplies the
explicit finite almost-short-path stability adaptation left unstated in
those passages. Mathlib at c55e6e786f49471c72fbddbec5415808896aec1e supplies
the separation quotient (MetricSpace/Basic.lean185–210), pseudometric
construction (Pseudo/Defs.lean127–158), and the 1/(n+1) limit
(SpecificLimits/Basic.lean58–75). The existing project distance-matrix
subsequence implementation was read in full and is unchanged.

No compactness, completeness, geodesic or curve hypothesis is imposed on
the source metric space. Compactness is used only for bounded finite real
arrays inside the accepted extraction theorem. AC32 geometric first-hit
packing transport and AC33's polynomial packing/local compactness remain
open, as do the intrinsic adapter and global one-dimensional classification.
Chapters3–4 and the migration remain incomplete.

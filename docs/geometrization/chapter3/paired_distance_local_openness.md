# AC23: pointwise packets give open distance coordinates

Four public theorems in two new leaves close the pointwise localization of
AC23. Actual curvature-minus-one comparison angles are continuous away from
the two anchors. A finite packet of quality delta/2 at q localizes to an open
neighborhood V inside the supplied common comparison neighborhood, with
quality delta and common positive lower and finite upper anchor-distance
bounds. The packet itself excludes anchor coincidence when delta < pi/2.
The finite localization lemma also allows an empty index type; the geometric
open-map theorem requires positive rank.

`exists_open_distanceCoordinates_of_pointwise_packet` assumes the existing
explicit almost-short-curve property, four-point comparison on the SAME
Omega containing all anchors and a neighborhood of q, positive delta at most
1/(100 m), and complete closed balls locally at points of Omega. It proves
openness of the actual first-anchor distance map on V in both l1 and l2,
Lipschitz constants m and sqrt(m), and m <= dimH V. Consequently an upper
Hausdorff bound n gives m <= n. It uses no minimizing geodesics, local
compactness, injectivity or lower Lipschitz estimate. The neighborhood is
chosen before either norm conclusion; it is not replaced between conclusions.
The local-completeness input is explicit in ambient closed-ball form. The
curve input remains on the ambient space, not its potentially non-length
open subspace.

The proof follows blueprint207A AC23, lines3160–3223. The full body was
reopened for this step. The unchanged BGP5.8/BBI10.8.15 source and errata
checks recorded in residual_correction_sources.json and
paired_distance_openness_sources.json are reused. These project constants
are not attributed to the printed source. Earlier mathematical leaves and
blueprint207 remain unchanged. This proves AC23 to its stated metric scope;
AC24 onward, rank-maximal injectivity, curvature-to-covering production and
full Chapters3–4 remain unfinished. No PC/Riemannian migration interface is
changed and no migrated root build is claimed.

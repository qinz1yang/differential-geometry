# Full AC51 metric product limit with actual coordinate control

Three public theorems and one definition in two leaves close the full metric
AC51 contract. Given pointed convergence to the specified proper targetY and
supplied actual KL maps X_i -> E x_2 Z_i with errors tending to zero, produce one
complete proper factorW, one strictly increasing subsequence, factor convergence
toW, retained source convergence toY, and one onto pointed isometrye:Y -> E x_2 W.
For suitable actual source approximationsg_i on radii tending to infinity and
errors tending to zero, the actual LEFT coordinates of the ORIGINAL supplied
maps converge uniformly to the left coordinate ofe(g_i(x)) on every fixed source
ball. The theorem retains the quantified maps, radii, errors, and convergence
estimates in its conclusion. The fixed left factorE is any proper metric space;
EuclideanFin(k) with basepoint0 gives exactly AC51, since Euclidean distance is
the norm of the difference. No map continuity, source/factor completeness,
properness, length, curvature or dimension is assumed.

The finite constructor composes the original KL map (converted with strict
positive slack) with the actual coordinate-preserving product lift of a factor
approximation. It keeps the raw intermediate errors to avoid losing the actual
map through error-index transport. Its first-coordinate identity is exact on
the whole controlled ball, before any limit is taken. Uniform-tail availability
follows from the factor convergence and the original errors tending to zero.

AC50 supplies an initial common subsequence and one complete proper factor.
Choose J_j=j+1 and epsilon_j=(1/(j+1))/100. For eachj, choose a common source
index admitting both a source-to-Y approximation and a coordinate-preserving
source-to-E x_2 W approximation on4J_j+4 balls, each with error epsilon_j.
Strict diagonal extraction makes those source indices increase. The controlled
common-source theorem then chooses one further subsequence and one onto pointed
isometry, with uniform full-product comparison on every fixed source ball.
Projection is1-Lipschitz and the intermediate coordinate identity is exact, so
this proves the claimed convergence of the ORIGINAL left coordinates. All
three subsequences are composed explicitly; factor and source convergence are
retained on that same final sequence.

Sources: blueprint207A AC49-AC51 full4568-4735, including actual-map hypotheses,
common-factor compactness, coordinate-preserving product coverage and uniform
MC24 assembly. The same unchanged source passages, KL definitions/Lemmas4.15-4.16
and retained corrections were checked in approximate_factor_compactness_sources,
approximate_product_limit_sources and controlled_isometry_sources. Pinned Mathlib
Filter/AtTopBot/Basic109-140 was read for the exact strict diagonal extraction
used here. The accepted finite product, factor compactness, KL conversion and
controlled common-source proof bodies were inspected. This completes the
blueprint's metric AC51 claim by the documented ultrafilter/finite-net route;
no new external result or current-remote errata clearance is claimed.

AC49 uses the existing actual normalized KL product-map interface, AC50 now
supplies factor compactness, and AC51 supplies the onto product with coordinate
control. This does NOT prove KL4.8 compatibility between independently supplied
splittings, uniqueness/alignment of coordinates without a subsequence, or the
long-strainer-to-splitting production. Those geometric and compatibility layers
remain next. Earlier leaves, blueprint207 and migration interfaces are unchanged.

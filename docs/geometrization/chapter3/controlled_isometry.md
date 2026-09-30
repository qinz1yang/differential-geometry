# MC24 and AC51: control of the actual approximation maps

Three public theorems in two leaves strengthen pointed isometry existence to
uniform subsequential convergence of the supplied maps. The source and target
of the first theorem are proper metric spaces. Radii tend to infinity and errors
tend to zero; the inputs are actual pointed closed-ball approximations. The
conclusion produces ONE onto pointed isometry and ONE strictly increasing index
map. For every fixed source radiusS and every eta>0, all sufficiently late maps
are within eta of the isometry at EVERY source point of distance<=S in their
controlled domain. Neither the maps nor their extensions are assumed continuous.

The construction retains the accepted ultrafilter proof of isometry and onto-ness,
including compactness of the coverage preimages. For each compact source ball,
a finite eta/5-net and small distortion upgrade pointwise ultrafilter convergence
to uniform convergence. Countably many integer-radius/reciprocal-error conditions
then select a single strictly increasing subsequence, uniformly valid on every
fixed ball. This is an explicit alternative to the blueprint's dense-set diagonal
route; no unjustified passage from an ultrafilter to a sequence is made. The
previous accepted isometry leaf is unchanged. Its public theorem did not expose
map convergence, so the refined construction necessarily retains that evidence.

For two actual approximations f_i:T_i->X and g_i:T_i->Y on4J_i+4 balls with
J_i>=1, J_i->infinity, epsilon_i->0 and10epsilon_i<J_i, the second leaf proves
the finite comparison estimate d(g_i(x),C_i(f_i(x)))<3epsilon_i whenever f_i(x)
is in the J_i-ball. It uses the ACTUAL commonSourceComparison and inverseLift,
including the error-index transport in that existing definition. The final
theorem produces one pointed onto isometry e:X->Y and one subsequence with
uniform d(g_i(x),e(f_i(x)))->0 on every fixed original-source ball. The T_i need
not be complete, proper or length spaces; the two limit targets are proper.

Sources read: blueprint207A MC24 complete1614-1682 and AC51 complete4650-4733;
the actual accepted PointedIsometry proof; RealBallExamples' actual comparison
constructor; PointedBallApproximation107-184 (chosen inverse, distortion, forward
image and left-error estimates); FiniteNets33-44; pinned Mathlib Filter/Finite246-262
(finite intersections of eventual estimates) and Filter/AtTopBot/Basic109-140
(strict subsequence selection). AC51/KL scope and correction checks reuse the
unchanged approximate_product_limit and approximate_factor_compactness source
records. No additional external theorem or current-remote errata claim is made.

The actual approximate-product coordinate conclusion still needs assembly with
AC50's factor subsequence and coordinate-preserving product maps. This milestone
supplies its missing controlled MC24 dependency, not KL4.8 compatibility or the
long-strainer geometric production. Earlier leaves and blueprint207 are unchanged.

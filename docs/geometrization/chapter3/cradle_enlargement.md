# ALG02: full quantitative cradle enlargement

Twenty-one public theorems, three definitions and one actual minimizing-hinge
structure in six leaves assemble the full ALG02 metric statement.
Metric.MinimizingHinge p q stores an actual center and the two supplied
isometry segments with exact endpoints. Reversal swaps those same segments.
Its numerical germAngle and modelSide are the previously established actual
canonical germ angle and cosine-law side; the structure contains no target
comparison assertion, convergence witness or successor assumption.

For kappa>=0, ell>0 and fixed endpoints p,q, assume endpoint comparison at
both p and q for EVERY specified minimizing hinge of positive arms and sum
less than 2ell/3. At each center z with d(z,p)+d(z,q)<ell, assume actual
minimizing joins to both endpoints are available and that z has an open
four-point comparison neighborhood in the SAME metric. Then EVERY supplied
MinimizingHinge p q of arm sum below ell has model side at least d(p,q).
For positive arms, the actual comparison angle is at most that hinge's
canonical germ angle. The side conclusion includes zero arms and coincident
endpoints. No ambient completeness, dimension, compactness or globally
geodesic typeclass is required once the stated joins are supplied.

The proof derives positive arms and failure of the small-hinge stopping case
for any putative failing hinge. It chooses the prescribed interior point
on the actual longer segment, excludes the endpoint stopping case by exact
metric betweenness, and obtains a new chosen join. The successor retains
that join and the forward part of the original longer segment, with exact
canonical-angle and model-side identities. Local adjacent comparison and
endpoint small-hinge comparison give nonincrease and short-angle domination.
The shorter/longer arm ordering is handled by reversing the actual hinge;
min/max lengths and the same germ angle feed the accepted state-space
iteration. The infinite sequence and its convergence are derived in that
iteration, not assumed by the headline.

Every successor center stays on the chosen longer segment and retains the
sum-of-arms bound. The accepted whole-segment containment lemma places all
chosen joins inside both endpoint balls of radius ell. Thus the source's
B(p,2ell) containment follows whenever those are the available joins. The
new headline assumes comparisons in the restricted metric under discussion;
it does not assert an intrinsic/restricted metric identification or produce
minimizing joins from a Riemannian or completed PC interface.

The two order theorems prove that the actual model-side function reflects
angle order on[0,pi] for positive arms, and convert the side conclusion back
to the exact comparison-angle statement, including collinear triangles.
The intended public headlines are modelSide_ge_dist_of_small_hinges and
comparisonAngle_le_of_small_hinges in Metric.MinimizingHinge.

Sources used and retained: frozen blueprint207A ALG01/02 full bodies7264-
7415, especially ALG027339-7415; pinned AKP vol1
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 defs-CBB.tex307-386 and951-1090
(thm:defs_of_alex and key-lem:globalization), model.tex74-215 (model side,
angle/side correspondence and extension). These actual bodies were read
in this continuation; unchanged source/version and author-errata checks
from the preceding milestones are reused. The formal quantitative infinite
argument uses the blueprint's explicit ell/36 late-arm estimates, already
proved in cradle_sequence, rather than importing the source's informal
late-arm assertion. The adjacent-angle INEQUALITY is sufficient; equality
of adjacent germ angles is not assumed.

Blueprint stays207. Final globalization ALG04 and later consumers, endpoint-
free recognition, intrinsic adaptation and uniform curvature-to-covering
production remain open. This proves ALG02 in the explicit supplied-join
metric scope; Chapters3-4 as a whole are not complete and the PC migration
boundary is unchanged.

# ALG04: complete geodesic globalization for nonpositive curvature

Seven public theorems in four leaves prove all conclusions of ALG04 for
kappa>=0, representing lower curvature -kappa. The space is a complete
metric space. Geodesicity is the explicit actual-segment hypothesis: every
pair x,y admits an isometry [0,d(x,y)] -> X with endpoints x,y. Each point
has an open neighborhood satisfying four-point comparison for the SAME
ambient/restricted metric. No global comparison, dimension, local compactness,
properness, uniform neighborhood radius, or PC release interface is assumed.

The headline conclusions are global model-side comparison for every supplied
MinimizingHinge, global comparison-angle bounds for positive arms, the full
endpoint comparison property at every real radius, and global four-point
comparison. The latter uses three specified radial segments and their SAME
canonical germ angles, not a separately chosen hinge for each angle. Outer
points may repeat; only the original four-point definition's center
noncoincidence requirements are retained.

The proof uses the actual capped comparison radius from the preceding
milestone. A putative failing hinge gives r(o)<M after choosing M above its
arm sum. Uniform local positivity permits the complete-ball almost-minimum
theorem with epsilon=1/4. For its selected p*, r*<=r(o)<M and radii at points
within 4r* exceed 3r*/4. With ell=17r*/16, ALG02/endpoint enlargement gives
comparison through ell. The admissible radius min(ell,M) is strictly larger
than r*, contradicting the defining supremum. Every use of a comparison
radius is strictly below it; no attainment or continuity of that radius
function is assumed. Ambient completeness supplies the complete closed ball
required by ALG03. This proof never needs to identify the finite encoding
with a separate extended-real supremum.

A generic point-on-side theorem converts the accepted four-point shortening
inequality through the actual model-side cosine laws. It includes zero
shortened arms, a third vertex at the basepoint, and collinear triangles.
Its complete-local consumer gives the global model-distance lower bound.
The last theorem proves independent coordinatewise comparison-angle
monotonicity for every supplied pair of minimizing radial germs, without
requiring their full ranges to lie in one original local neighborhood.
These are the remaining point-on-side and independent-arm conclusions of
ALG04, not an appeal to an unproved global angle theorem.

Source reading: frozen blueprint207A ALG04 full body7447-7484 (and ALG05/
context through7605); pinned AKP vol1
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 defs-CBB.tex1131-1218, comparison
radius and geodesic globalization proof; earlier checked307-386 and951-1090
supply local angle/cradle dependencies. The general ultrapower argument is
outside this theorem. Mathlib Topology/UniformSpace/Cauchy.lean445-448 was
freshly read for IsClosed.isComplete. The actual accepted AngleShortening
body was reread for the point-on-side consumer. Exact source hashes,
locators and reused July12,2026 errata checks are recorded separately.

Blueprint207 and earlier mathematical leaves are unchanged. ALG05's complete
interior buffer, ALG06's intrinsic/ambient transfer, endpoint-free recognition
and uniform curvature-to-covering consumers remain open. Chapters3-4 as a
whole and the PC migration are not claimed complete.

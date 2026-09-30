# Joint germ-angle limits from local four-point comparison

Sixteen public theorems and one definition in three leaves implement ALG01's
metric conclusions. The parameter kappa>=0 represents curvature -kappa.
The two finite shortening inequalities hold for every such kappa; the proof
reuses curvature-zero shortening and transports the accepted curvature-minus-one
estimate through the accepted metric rescaling by sqrt(kappa). Positive
shortened arms are explicit. An unchanged arm is allowed. No earlier leaf
is changed.

The new limitingComparisonAngle is the supremum of ACTUAL comparison-angle
values on the positive rectangle of arm lengths. Unit-speed minimizing
segments are represented by real-parameter functions with explicit radial
and within-segment distance identities on Ioc(0,R); their values outside
that interval do not enter the supremum. The common-domain theorem derives
coordinatewise monotonicity from four-point comparison and proves convergence
for the PRODUCT of the two right-neighborhood filters. It therefore permits
independent arm parameters and arbitrary relative rates. The existing pinned
library theorem tendsto_sSup_positiveRectangle is reused and its exact proof
and axiom closure checked; no second generic limit construction is added.

The angle lies in [0,pi], dominates every positive finite hinge in the supplied
common domain, is symmetric, and is unchanged by shortening both positive
radii. The zero-curvature definition is identified with the existing
limitingRadialAngle. A germ has angle zero with itself; opposite parts have
angle pi. Three specified germs have sum <=2*pi; opposite outer germs give
the adjacent bound <=pi. Repeated germs are permitted. No adjacent-angle
equality, space of directions, or nonbranching theorem is assumed.

Localization chooses ONE positive a before the center, lengths and specified
hinge. Whenever one endpoint lies in B(p,a) and the sum of arms is <a,
both entire arms and their center lie in the original open comparison domain.
The same actual supremum is then the joint limit and dominates the endpoint
comparison angle. A second theorem restricts any two given positive-length
germs to a positive common radius and obtains their local joint limit.
Neither completeness, local compactness nor a dimension bound is needed.
The domain metric is the original restricted metric throughout.

Sources actually checked: frozen blueprint207A ALG01, lines7264-7343;
pinned AKP vol1 ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245,
defs-CBB.tex307-386, thm:defs_of_alex (2-sum, point-on-side, angle), and
model.tex74-92,170-215. The source's global Alexandrov hypotheses and converse
are not silently imported: these local fixed-germ results are proved from
the actual finite inequalities. Prior source/errata comparisons in revision140
are reused with their version distinctions. Detailed hashes and reused source
records are in evidence/germ_angle_sources.json.

This closes the stated local germ-angle conclusions of ALG01 in explicit
metric interfaces. ALG02's cradle and the remaining complete/localized
globalization consumers are not proved by this milestone. Endpoint-free
line/circle recognition, intrinsic adaptation and curvature-to-uniform-covering
production also remain open. Blueprint207 is unchanged; no PC migration
interface or final-release acceptance claim is made.

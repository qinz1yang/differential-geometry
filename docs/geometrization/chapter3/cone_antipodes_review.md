# Actual cone antipodes, coordinate and arc acceptance

Nine public theorems and one definition in three new leaves add the observed 12 owned declarations (10 declared and 2 compiler-generated). The 443-module shared gate checks 2,125 owned declarations in 3,281 jobs. Its observed increment is 12 owned declarations, comprising 10 declared public declarations (nine theorems and one definition) and 2 compiler-generated declarations. Ten new concrete regressions and twenty canonical-import standard-axiom reports pass, with silent selected lint. The separate unchanged blueprint static audit remains pending due to historical iCloud input downloads; no static pass is claimed.

Every owned transitive axiom closure is restricted to propext, Classical.choice and Quot.sound. The twenty explicit reports cover all ten public production declarations (including twoRayPath) and ten new tests. Earlier frozen fixtures are re-elaborated once and are not counted as new regressions. The generated increment is calculated from the actual shared gate over the preceding verified milestone124 receipt, not predicted from source counts. There are no new instances, private production declarations, admissions or mathematical axioms. Earlier mathematical leaves are unchanged. No full migrated-root, PDF, Overleaf or human-approval claim is made.

The inherited AreaUpperBarrier build warning remains outside these owned axiom closures.

The actual signed cone path retains a on its positive ray, b on its negative ray, and the same tip at zero. It is a global isometry of the real line exactly when pi<=dist(a,b); the metric cap deliberately permits larger distances in a general angular base. For actual completed directions the existing diameter bound reduces this to equality pi. The exact canonical coordinate is r*cos(min(pi,dist(a,u))), with the correct positive-ray orientation. Its zero locus at positive r is precisely original angular distance pi/2, with no hidden diameter hypothesis and no assumed assertion that the path is a line.

The arc consumer assumes ONE supplied cone curve of constant positive radius with its exact cosine pair-distance law. It recovers a continuous exact-speed segment in a base of diameter at most pi, retaining f(t)=mk(r,g(t)) for EVERY original parameter. It does not supply such a meridian arc. The positive-radius and cap hypotheses are essential; explicit failure regressions check both. No base properness, completeness, CBB, angular geodesicity or prior curve continuity is smuggled into these elementary metric statements.

Ten regressions cover the unbounded angular cap and below-pi failure, actual real tangent antipodes, actual plane representatives of unequal positive domain lengths, coordinate equator/cap/zero-radius values, the signed original oblique-plane coordinate at all radii, a nonconstant radius2 arc spanning [0,pi] with pointwise original parameter identity, coincident endpoints, and the separate radius0/cap recovery failures.

KLP6.20(c) additionally needs an actual nonempty transverse suspension factor to produce meridians after splitting. This package does not derive that condition, full antipodal angular geodesicity, or a cone/base curvature equivalence. An upper dimension bound n>=2 does not imply the needed lower-dimensional nondegeneracy. Blueprint207 and migration interfaces remain unchanged; Chapters3-4 are not declared complete.

# Prescribed opposite cone rays, the actual tip, and the canonical equator

## Exact contracts and natural homes

`Metric.EuclideanCone.twoRayPath a b : Real -> EuclideanCone Y` joins the actual ray in direction a at nonnegative times and the actual ray in direction b at nonpositive times. This definition requires only the carrier Y. Three exact simp laws retain the ORIGINAL labels: for every r:NNReal, path(r)=mk(r,a), path(-r)=mk(r,b), and path(0)=tip. Both formulas agree at0 because mk0 collapses every supplied direction to the actual tip. No direction is chosen in an empty base.

For a metric base Y, `dist_mk_eq_add_of_pi_le` gives d(mk(r,a),mk(s,b))=r+s under pi<=d(a,b), for all nonnegative radii including zero. `isometry_twoRayPath_iff` proves the exact equivalence

    Isometry (twoRayPath a b) <-> pi <= dist a b.

This uses the accepted actual cone distance with its min(pi,d_Y) cap. It deliberately permits distances strictly greater than pi in an arbitrary angular base. It adds no diameter, curvature, properness, completeness, geodesic or nonempty-space premise. In actual SpaceOfDirections(q), the accepted pi upper bound specializes it to precisely antipodal pairs. The core has five public theorems and one definition, with no private production declarations. Planned canonical home: Geometry/Metric/ConeAntipodalLine.lean; only Geometry/Metric/EuclideanCone is needed.

The separate Comparison/ConeLineCoordinate leaf has two public theorems. `Toponogov.lineCoordinate_twoRayPath_mk` identifies the accepted quadratic coordinate exactly:

    lineCoordinate (twoRayPath a b) (mk r u) = r * cos(min(pi,dist(a,u))).

`lineCoordinate_twoRayPath_mk_eq_zero_iff`, for r>0, identifies its zero slice with the ACTUAL equator dist(a,u)=pi/2. Neither formula needs an antipodal premise: it computes the accepted quadratic coordinate for the explicit path. When the path is an antipodal isometry, this is exactly the accepted line-splitting coordinate. The second theorem needs no global diameter assumption: cosine injectivity makes the capped angle pi/2, which is strictly below the cap and forces the uncapped distance pi/2. The positive-radius condition is essential. Minimal imports are the new Metric.ConeAntipodalLine and accepted Comparison.LineDistance, where lineCoordinate itself is defined.

## Actual source audit

Fresh full reading of KLP, Lectures on Alexandrov spaces with curvature bounded below, archived v1 July14 2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`:

- Exercise6.20(a)-(c), printed69/PDF71, including the explicit necessity of LinDim(A)>1 for part(c) and the real-line two-direction counterexample.
- Entire semisolution6.20, printed138/PDF140: strict-pi geodesics already come from6.5; a pair at distance>=pi induces a line through the tangent origin; splitting gives a spherical suspension with the specified poles over a NONEMPTY angular equator, using the preceding dimension information.
- Direct-sum definition, splitting theorem5.5, and its full proof, printed52-54/PDF54-56: actual product retractions, the zero Busemann slice, inverse flows and the onto isometry. The current accepted splitting implementation is reused, not replaced by a citation to this proof.
- Exercise5.8 and semisolution, printed54/PDF56 and printed133-134/PDF135-136: the two rays form a line iff their actual base distance is>=pi. This source explicitly distinguishes the capped cone formula from the subsequent curvature consequence d<=pi.
- The earlier cone definition/Exercise3.2 and full semisolution checks, printed36/PDF38 and printed129/PDF131, retain their accepted source roles.

The actual text was read from the source-linked extraction /tmp/gc140/KLP.txt; the archived PDF identity is the retained source receipt. The retained AKP erratum at vol1 commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 was reread; it is an AKP published-book erratum, not a KLP erratum sheet. The existing revision63 qualification remains: no separate KLP author errata sheet was confirmed. No fresh external retrieval or absence-of-errata claim is made. Source files and blueprint are unchanged.

## Complete proof and existing splitting reuse

For pi<=d(a,b), the cap is pi and cos(pi)=-1, so the squared cross-ray distance is (r+s)^2. Nonnegative radii give the positive square root r+s. Same-ray distances are already abs(r-s). Four sign cases for two real parameters give the full isometry of the actual signed path, including0.

Conversely, evaluate any claimed path isometry at+1 and-1. Their cone distance is2. The exact squared cone law forces cos(min(pi,d(a,b)))=-1. Both the capped angle and pi lie in[0,pi], so cosine injectivity forces the cap to equal pi, hence d(a,b)>=pi. There is no curvature argument or hidden angle bound.

For the coordinate formula, the accepted lineCoordinate definition uses only distances to path0=tip and path1=mk1a. Substitute d(mk(r,u),tip)=r and the exact squared cone cosine law; the radial squares cancel. For a positive radius, coordinate0 forces the cosine to vanish. Cosine injectivity on[0,pi] and the strict inequality pi/2<pi give the uncapped equator equality. At radius0 the coordinate is0 for every direction, so this hypothesis is not a totalization artifact.

The accepted complete LineSplitting.lean API was read, including its canonical lineSplitting map, exact lineSplitting_apply_line, and exists_isometryEquiv_real_prod. The previous full finite-dimensional tangent producer was also read: it returns ProperSpace of literal TangentCone(q), global fourPointComparison0, and actual all-pair segments, together with compact actual directions and same-target blowup convergence. Therefore for actual poles a,b in the SAME SpaceOfDirections(q) with dist(a,b)=pi, these existing outputs and the new proved line isometry directly satisfy the accepted splitting theorem. Its exact `forall t, e(twoRayPath a b t)=(t,z)` preserves both original poles, both entire radial halves, and the tip. The factor is the accepted canonical zero-coordinate subtype when lineSplitting is used. No supplied-line splitting alias is added to production.

## Remaining full-pi issue

The new core closes the previously missing actual-line construction. It does NOT by itself construct a geodesic in directions between antipodal poles. That later construction needs a genuine transverse point off this prescribed line, equivalently a nontrivial transverse metric factor or a point of its angular equator, followed by the meridian construction. The metric splitting factor always has its basepoint; the missing fact is NONTRIVIALITY, not existence of that basepoint. The source's phrase “over a nonempty space” concerns the angular suspension equator.

KLP6.20(c) uses the genuine LOWER dimension assumption LinDim(A)>1 together with the dimension identity in6.20(b). The currently proved source-facing APIs assume only dimH(U)<=n. Even choosing n>=2 does not exclude a real source satisfying that upper bound. Thus neither a transverse point, the dimension identity, nor full unrestricted direction geodesicity is inferred from the upper bound. An independently given actual off-line tangent point, or an independently proved lower-dimension/non-line exclusion, is an honest next premise. A third actual direction distinct from both prescribed poles is another possible natural source for an off-line unit cone point; no such direction is manufactured here.

## Actual concrete regressions

Four new core tests are in /tmp/gc_cone_antipodal_line_review_body.lean:

1. The unbounded angular base Y=Real with directions0 and2pi: the actual distance is STRICTLY above pi, yet the explicit capped-cone path is an isometry, preserves every original half-ray and tip, and its values at2 and-3 are distance5.
2. The same base with directions0 andpi/2: the unit chord is exactly sqrt2 and the explicit path is NOT an isometry. This is the strict-below-pi failure test.
3. The actual complete real source at7: original positive/negative representatives of length1, their explicit original paths7+t and7-t, and their independently proved completed-direction distancepi give the actual line in literal TangentCone(7). Both entire tangent-vector rays are retained for every nonnegative radius.
4. The actual translated Euclidean plane at(7,-3), with original positive/negative representative domains of lengths1 and3: the actual angle is independently proved pi, and the actual line retains those exact representative tangent vectors for every radius.

Two new coordinate tests are in /tmp/gc_cone_line_coordinate_review_extra.lean. The real angular base checks an actual equator, the cap at2pi, an intermediate cosine atpi/3, and the radius0 counterexample to removing positivity. The actual translated plane checks the canonical coordinate of the original oblique representative (-3/5,4/5) against the original positive/negative poles, at EVERY radius: it is exactly (-3/5)*r. Frozen real and plane fixture bodies are reused once and are not counted as new tests.

## Compiler and independent evidence

Core minimal normal driver /tmp/gc_ConeAntipodalLine_agent.lean actually exited0 with an empty log. Selected lint/axiom driver /tmp/gc_ConeAntipodalLine_lint.lean exited0, no findings, and all six public declarations including the definition have exactly the standard propext/Classical.choice/Quot.sound closure. The four core regressions compiled exit0 with an empty log, then linted exit0 with four standard-axiom reports and no diagnostics. Coordinate minimal normal driver /tmp/gc_ConeLineCoordinate_agent.lean compiled exit0 with an empty log. The final coordinate lint and combined regression results are appended after completion.

Root read the entire core and reported the signed path, exact iff and empty/tip cases sound. Agent65 independently read the same frozen core and recorded a pass in /tmp/gc_ConeAntipodalLine_independent_read.md, without claiming a separate compiler run. Default Lean resource limits were retained throughout. Mathlib revision c55e6e786f49471c72fbddbec5415808896aec1e. No repository mutation, shared build, blueprint/static audit, migrated-root, PDF-build or chapter-completion claim is made in this temporary record.

## Final coordinate and combined freeze

Coordinate selected lint actually exited0 with no findings and both public closures exactly the standard three axioms. The combined six-test normal driver exited0 with an empty log. Its final selected lint driver exited0, emitted exactly fourteen reports (eight production declarations, including the single definition, plus six new regressions), and had no other diagnostics. Each report contains exactly propext, Classical.choice and Quot.sound. Agent65 independently read the coordinate leaf and recorded a pass in /tmp/gc_ConeLineCoordinate_independent_read.md; no independent compiler run is attributed to that peer. All production bodies and new tests below are frozen.

- /tmp/gc_ConeAntipodalLine_body.lean: `45c067e2b5dbfa1350cfcb44f2f041d9ad5bcbf814ab6a2cc30d794cdec336e9`
- /tmp/gc_ConeAntipodalLine_agent.lean: `4d9e13892f09c06b8611e6374395513d48918608e26004b24f2ff735c946447f`
- /tmp/gc_ConeAntipodalLine_lint.lean: `280129cbf00185258700ba1000526760894b178303199bec172bc8dbd014617d`
- /tmp/gc_ConeAntipodalLine_lint.log: `0db938af2708343a00839fc58cc89b3a4a967bbdcaaa5a48b139d2473e1a0e71`
- /tmp/gc_ConeLineCoordinate_body.lean: `366ded0dedf2cb3bd92ef69589e0a2456ffc979bebceba08f117bfe54a0c6d57`
- /tmp/gc_ConeLineCoordinate_agent.lean: `6634689c42f72776946d21a72c2d08a197247ef1d4b3e950bba61ea2b2e56c6a`
- /tmp/gc_ConeLineCoordinate_lint.lean: `ad8f5df6c7febc284be5bc49b8b131163760cbd71e6cd32934cc06571605ca70`
- /tmp/gc_ConeLineCoordinate_lint.log: `3e1f8f36c69b423fcc57d16731a8e5f340b10afdf7f080e03a7036b4fdce4205`
- /tmp/gc_cone_antipodal_line_review_body.lean: `e99a3f545439448f82580882506b32687e4305ae12d4cafdb4882ecc050d77bc`
- /tmp/gc_cone_line_coordinate_review_extra.lean: `82cfb9c9b2593d0095a84a6eedbbed31c63d54547f0f88dfc81f5e91bde2aa5e`
- /tmp/gc_cone_line_coordinate_review_agent.lean: `70a7d58b7da9c20f598081c680b2a2b0d5eccde995f059b9a7a6ad25b585f392`
- /tmp/gc_cone_line_coordinate_review_lint.lean: `f7c2a056d33b223f421f88b42b03ec398489149e6bbf35dca86931e07ba14480`
- /tmp/gc_cone_line_coordinate_review_lint.log: `ec7527ce441a71fe3f466cde6730409558a1dfc9c5df33e01b2a06f76a2568ff`

The frozen prior fixture order is direction_space_review_body, real_direction_obstruction_review_extra, plane_direction_packing_review_body, uniform_ray_endpoint_review_scaffold, each from /tmp/gc_*.lean and each included once, followed by the four-test core body and two-test coordinate extra. The combined driver gives the exact imports. No Mathlib.Tactic umbrella is used.


# Independent actual cone two-ray line read

Read complete `/tmp/gc_ConeAntipodalLine_body.lean`, SHA256 `45c067e2b5dbfa1350cfcb44f2f041d9ad5bcbf814ab6a2cc30d794cdec336e9`.

Proof and public contract review: PASS, no defects found. One actual path definition and five theorems. No new geometric source assumptions or conclusion-like witness premise.

The original positive/negative angular points a,b are used in the actual existing Option cone. The path's two branches agree at0 because both radius0 points are the tip. Under π≤dist(a,b), capping makes the exact cross-distance the sum of nonnegative radii; same-sign parameters use the same-direction radial metric. The four real sign cases establish an actual global isometry of ℝ.

Conversely, the actual path's values at1 and−1 must have distance2. The squared cone identity implies the cosine of min(π,dist(a,b)) is−1. This capped angle lies in[0,π], so cosine injectivity there forces it to equalπ, giving the exact conditionπ≤dist(a,b). Arbitrary angular bases with distances exceedingπ are included correctly; there is no implicit diameter bound. In an actual direction space with diameter≤π this specializes to equalityπ.

No CBB, properness, completeness, angular segments, global cone geodesicity, or positive-dimensional source assumption is introduced. In particular the leaf does not supply a transverse point, an equatorial factor, or geodesics between angular antipodes. The strictπ angular-segment boundary from previous accepted work remains intact.

Relevant source context reuses the independently read KLP6.20(c), printed69/PDF71, semisolution138/PDF140, and cone convention/Exercise3.2, printed36/PDF38, semisolution129/PDF131, archive SHA3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67. This read reviews the elementary exact metric implementation; it is not a fresh external source/errata audit or an implementation claim for the full source conclusion.

Compiler, lint and concrete-test evidence remain the implementing agent's responsibility; this reviewer did not independently compile this leaf. No repository or reference edits, shared builds, registration or migration probes were performed.


# Independent cone line-coordinate read

Complete read of `/tmp/gc_ConeLineCoordinate_body.lean`, SHA256 `366ded0dedf2cb3bd92ef69589e0a2456ffc979bebceba08f117bfe54a0c6d57`: PASS, no defects. Two public metric-coordinate theorems, no new definition or assumption package.

The accepted lineCoordinate definition uses the squared distances from γ0 and γ1. For the SAME twoRayPath, these actual points are the tip and mk(1,a). The exact existing cone squared-distance law therefore gives coordinate r*cos(min(π,dist(a,u))) with the correct sign and positive-ray convention. No assertion that the path is a line is needed for this definitional formula, so the absence of an antipodality premise is justified; when used with the separately proved line criterion, it describes precisely that same line.

For positive r, the coordinate vanishes exactly when the capped angle has cosine0. Cosine injectivity on[0,π] gives capped angleπ/2. Since the capπ is strictly larger, the original uncapped distance is then exactlyπ/2. Conversely that angle makes the coordinate vanish. Positivity of r is necessary and explicit, avoiding the apex counterexample. No angular diameter, CBB, properness, or geodesicity hypothesis is silently used, and no claim that all sphere directions occur in an equatorial factor is made here.

Relevant source context is the same cone convention and splitting/equator context recorded in `/tmp/gc_ConeAntipodalLine_independent_read.md`; this exact calculation rests on previously accepted formal definitions and is not a new external theorem attribution. No independent compiler/lint run was performed by this reviewer; implementation checks remain separately reported. No repository/shared-build/reference changes were made.


# Cone arcs recover actual angular segments

Two public theorems in the proposed Metric.ConeArcDirections leaf use only Metric.EuclideanCone. The first recovers an angular distance in [0,pi] from the exact fixed-positive-radius squared chord law. The second takes one actual supplied cone curve f with constant positive radius, its actual endpoint cone points, and the exact cosine pair-distance identity, and returns a continuous exact-speed angular segment g with the public identity f(t)=mk(r,g(t)) at every original parameter.

No base properness, completeness, curvature, segment existence or continuity of f is assumed. The pair-distance identity itself implies the angular Lipschitz estimate. The diameter-at-most-pi hypothesis is explicit because the cone metric caps larger angular distances. The positive radius is essential: the tip alone cannot encode an angular direction. The proof decodes each non-tip f(t), recovers radius r, cancels the strictly positive coefficient 2r^2 and uses injectivity of cos on [0,pi]. Each parameter distance is at most1, so the target angle remains in [0,pi]. Injectivity of mk at fixed positive radius retains the original endpoint directions.

Source context: archived KLP v1 July14,2026, SHA2563dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67, cone definition/Exercise3.2 printed36/PDF38 and semisolution129/PDF131, Exercise6.20(c) printed69/PDF71 and full semisolution138/PDF140, and Exercise5.8 printed54/PDF56 and semisolution133-134/PDF135-136. Root read these actual passages. The source uses the cone/suspension geometry to obtain meridians after splitting an actual antipodal line. This helper is our explicit cosine-law recovery step; it does not claim that these source passages state this exact formal API, and it does not produce the supplied cone arc. Earlier actual-cone source identities and retained errata qualifications are reused; no new external errata or full cone/base equivalence claim is made.

The actual minimal-import root compile /tmp/gc_ConeArcDirections_agent.lean exited0 with an empty /tmp/gc_ConeArcDirections.log. Independent source_review proof review passed. Its sole-EuclideanCone production-and-test driver and selected lint both exited0; six explicit closures are standard. Root read every final test body and full peer record: radius2 full-pi arc retains every direction at every parameter, coincident endpoints, and explicit zero-radius/capped-distance counterexamples. See /tmp/gc_ConeArcDirections_independent_review_record.md and /tmp/gc_cone_arc_directions_review_body.lean. No canonical registration, shared build or publication has occurred. Earlier accepted mathematical files remain unchanged.

Frozen root body SHA256: 63dd6eb6e0ee0ca6e5eda80661fe96b75c5c15138268cdab41d750bfc9ff7c7f.


# Independent cone arc to direction segment review

## Verdict and exact scope

Full root production body `/tmp/gc_ConeArcDirections_body.lean` read. Independent mathematical, public-contract and proof verdict: PASS. The two public declarations are `Metric.EuclideanCone.dist_eq_of_dist_mk_sq_eq` and `Metric.EuclideanCone.exists_base_segment_of_cone_arc`. There are no requested code changes.

This is a generic metric cone **consumer of an actual supplied constant-radius arc with its exact two-parameter chord law**. It does not produce that arc, prove sphere geodesicity from a cone splitting, or prove all of the source's tangent/direction classification. The target base Y needs only a metric and, for the second theorem, diameter at most pi. No completeness, properness, curvature, nonempty-space typeclass, or prior continuity of the supplied curve is added. The endpoints themselves provide the needed local nonemptiness.

## Proof and object preservation

The first theorem expands the literal existing cone cosine-law metric for the same positive radius r. The hypothesis dist(a,b)<=pi removes the metric's angular cap. Positivity of 2*r^2 permits cancellation and gives equality of cosines. Both the actual distance and theta are in [0,pi], so strict antitonicity of cosine gives the exact distance equality. All endpoints of that closed angular interval, including pi, are allowed.

For the second theorem, the actual radius law excludes tip at every time; its positive-pair representation has radius exactly r. Choice selects its actual direction g(t). The map u↦mk(r,u) is injective for positive r by the actual Option/pair representation, independently of the metric's angular cap. Thus the public identity f(t)=mk(r,g(t)) retains the SAME supplied f globally, and the exact two original endpoint identities imply g(0)=a and g(1)=b.

The supplied chord law and the first theorem recover all distances of g. Its candidate angle dist(a,b)*dist(s,t) lies in [0,pi] because s,t∈[0,1] and diam(Y)<=pi. The recovered distance formula itself proves Lipschitz continuity with constant dist(a,b). Hence no continuity premise on f is missing. Coincident endpoints yield the constant segment without an injectivity requirement on its parameterization.

The global diameter premise can in principle be localized to the image, but the current form is natural for actual completed direction spaces and is sound. It is not dispensable merely because mk(r,·) is injective: the metric caps angles beyond pi, as the concrete counterexample verifies.

## Source bodies checked

KLP archived v1 July14 2026 PDF SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`:

- Exercise6.20(c), printed69/PDF71, and its full semisolution printed138/PDF140: the source handles antipodal directions by a line through the cone tip, splitting, and a spherical suspension over a **nonempty** space. That nonemptiness/dimension qualification is not erased by this helper, which only pulls back a supplied arc.
- Exercise5.8, printed54/PDF56, and full semisolution printed133–134/PDF135–136: the source requires a complete geodesic base for its cone/Alexandrov equivalence and explicitly retains diameter<=pi. Its proof discusses capped antipodal distances, splitting/nonbranching, unit-sphere cone geometry, and curvature transfer. This helper claims none of those global curvature implications; it uses only the previously accepted literal cosine metric and its closed-angle inversion.

The entire relevant source bodies and both semisolution passages were read. The cone convention remains the accepted Option tip/positive-radius carrier with min(pi,dist) in the metric. Existing source/errata qualifications are retained; no new external retrieval or error-free-source claim is made. The actual cone construction/import was read rather than assuming an abstract direction-realization package.

## Four concrete regressions

All four are new declarations in `/tmp/gc_cone_arc_directions_review_body.lean`:

1. Actual base Y=[0,pi], actual radius2, f(t)=mk(2,pi*t). The chord law is proved from the concrete cone metric. The theorem returns a continuous segment retaining the whole original f, and the test additionally proves g(t)=pi*t for EVERY t, with distinct endpoints. This includes the exact pi boundary.
2. Actual radius2 constant arc at the left endpoint of the same base. The conclusion is pointwise the original constant direction, exercising coincident endpoints.
3. Radius0 at the two distinct base endpoints: the squared chord equation holds with theta0 but the original angular distance is pi≠0. This proves positive radius cannot be omitted from cosine recovery.
4. Actual base real line, radius2, endpoints0 and2*pi: the cone squared distance has the theta=pi formula while the actual base distance is2*pi≠pi. This proves the cap-bound premise cannot be omitted.

The positive test does not assume angular geodesicity as a theorem input or repeat an unproved output hypothesis. Its concrete coordinate formula independently proves the required actual cone law. The failure tests prove explicit incompatible distance conclusions.

## Independent compiler/lint evidence

The normal review driver imports only the same sole production dependency `DifferentialGeometry.Geometry.Metric.EuclideanCone`, then the unchanged frozen root body and the four concrete tests. No `Mathlib.Tactic` umbrella is added. Actual normal compile exited0 with empty `/tmp/gc_cone_arc_directions_review.log`. The separate lint driver adds `Mathlib.Tactic.Linter`; actual selected lint (unusedArguments, simpNF, synTaut) exited0 with no findings. All six production/test transitive axiom reports contain only `[propext, Classical.choice, Quot.sound]`, in `/tmp/gc_cone_arc_directions_review_lint.log`.

No repository edits, canonical/shared builds, registrations, source changes, commits, or migration probes were performed.

## Frozen hashes

- `/tmp/gc_ConeArcDirections_body.lean`: `63dd6eb6e0ee0ca6e5eda80661fe96b75c5c15138268cdab41d750bfc9ff7c7f`
- `/tmp/gc_cone_arc_directions_review_body.lean`: `8aa4adc85ebb525defac0587a396b24eb3890e1b63e26a4737dac45c1864bf7f`
- `/tmp/gc_cone_arc_directions_review_agent.lean`: `06117befcd0a1424cd9cf4ccadea5ad3e5a65e4b1dfe03842ab38c78fd6948c2`
- `/tmp/gc_cone_arc_directions_review_lint.lean`: `5cb08b7d98e67df0bb554f7e4db8ef44304f5ad33ad6db36401f4a6db050ade4`


```lean
import DifferentialGeometry.Geometry.Metric.ConeAntipodalLine
import DifferentialGeometry.Geometry.Comparison.ConeLineCoordinate
import DifferentialGeometry.Geometry.Metric.ConeArcDirections
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison
import DifferentialGeometry.Geometry.Metric.TangentCone
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.AngularObstruction
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linter

open scoped NNReal

noncomputable section
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GCDirectionSpaceReview

private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private def positiveCurve (L : ℝ) : Icc (0 : ℝ) L → ℝ := fun t => 7 + t.val

private def negativeCurve (L : ℝ) : Icc (0 : ℝ) L → ℝ := fun t => 7 - t.val

private theorem positive_isometry (L : ℝ) : Isometry (positiveCurve L) := by
  apply Isometry.of_dist_eq
  intro s t
  change |7 + (s : ℝ) - (7 + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
  congr 1
  ring

private theorem negative_isometry (L : ℝ) : Isometry (negativeCurve L) := by
  apply Isometry.of_dist_eq
  intro s t
  change |7 - (s : ℝ) - (7 - (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
  rw [show 7 - (s : ℝ) - (7 - (t : ℝ)) = (t : ℝ) - s by ring, abs_sub_comm]

private theorem positive_path {L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    IccExtend hL (positiveCurve L) t = 7 + t := by
  rw [IccExtend_of_mem hL _ ht]
  rfl

private theorem negative_path {L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    IccExtend hL (negativeCurve L) t = 7 - t := by
  rw [IccExtend_of_mem hL _ ht]
  rfl

private theorem same_positive_angle {L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    germComparisonAngle 0 (IccExtend hL.le (positiveCurve L))
      (IccExtend hM.le (positiveCurve M)) = 0 := by
  have heq := germComparisonAngle_congr_on (κ := 0) hL hM
    (γ := IccExtend hL.le (positiveCurve L))
    (β := IccExtend hM.le (positiveCurve M))
    (γ' := fun t : ℝ => 7 + t) (β' := fun t : ℝ => 7 + t)
    (fun t ht => positive_path hL.le ⟨ht.1.le, ht.2⟩)
    (fun t ht => positive_path hM.le ⟨ht.1.le, ht.2⟩)
  rw [heq]
  apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
  intro s _ t _
  rw [Real.dist_eq]
  congr 1
  ring

private theorem positive_negative_angle {L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    germComparisonAngle 0 (IccExtend hL.le (positiveCurve L))
      (IccExtend hM.le (negativeCurve M)) = Real.pi := by
  apply germComparisonAngle_opposite (by norm_num) hL hM
  intro s hs t ht
  rw [positive_path hL.le ⟨hs.1.le, hs.2⟩,
    negative_path hM.le ⟨ht.1.le, ht.2⟩, Real.dist_eq,
    show 7 + s - (7 - t) = s + t by ring, abs_of_pos (add_pos hs.1 ht.1)]


private def positiveRepresentative {L : ℝ} (hL : 0 < L) : GeodesicRepresentative (7 : ℝ) where
  length := L
  length_pos := hL
  curve := positiveCurve L
  isometry := positive_isometry L
  start := by simp [positiveCurve]

private def negativeRepresentative {L : ℝ} (hL : 0 < L) : GeodesicRepresentative (7 : ℝ) where
  length := L
  length_pos := hL
  curve := negativeCurve L
  isometry := negative_isometry L
  start := by simp [negativeCurve]

theorem unequal_length_representatives :
    positiveRepresentative (by norm_num : (0 : ℝ) < 1) ≠
      positiveRepresentative (by norm_num : (0 : ℝ) < 2) := by
  intro h
  have hl := congrArg GeodesicRepresentative.length h
  norm_num [positiveRepresentative] at hl

theorem shortening_retains_actual_original_path (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1 / 3)) :
    ((positiveRepresentative (by norm_num : (0 : ℝ) < 2)).shorten
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num [positiveRepresentative])).path t = 7 + t := by
  rw [GeodesicRepresentative.shorten_path _ _ _ ht]
  change IccExtend _ (positiveCurve 2) t = 7 + t
  exact positive_path (by norm_num) ⟨ht.1, ht.2.trans (by norm_num)⟩

theorem singleton_representatives_empty : IsEmpty (GeodesicRepresentative (PUnit.unit : PUnit)) :=
  inferInstance


private instance : HasAnglesAt (7 : ℝ) :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ
    (real_comparison (by norm_num)) (mem_univ _)

theorem unequal_length_same_geodesic_direction :
    (positiveRepresentative (by norm_num : (0 : ℝ) < 1)).geodesicDirection =
      (positiveRepresentative (by norm_num : (0 : ℝ) < 2)).geodesicDirection := by
  rw [GeodesicRepresentative.geodesicDirection_eq_iff]
  exact same_positive_angle (by norm_num [positiveRepresentative])
    (by norm_num [positiveRepresentative])

theorem unequal_length_same_completed_direction :
    (positiveRepresentative (by norm_num : (0 : ℝ) < 1)).direction =
      (positiveRepresentative (by norm_num : (0 : ℝ) < 2)).direction := by
  rw [GeodesicRepresentative.direction_eq_iff]
  exact same_positive_angle (by norm_num [positiveRepresentative])
    (by norm_num [positiveRepresentative])

theorem opposite_completed_directions_distance :
    dist (positiveRepresentative (by norm_num : (0 : ℝ) < 1)).direction
      (negativeRepresentative (by norm_num : (0 : ℝ) < 2)).direction = Real.pi := by
  rw [GeodesicRepresentative.dist_direction]
  exact positive_negative_angle (by norm_num [positiveRepresentative])
    (by norm_num [negativeRepresentative])

theorem shortening_preserves_completed_direction :
    ((positiveRepresentative (by norm_num : (0 : ℝ) < 2)).shorten
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num [positiveRepresentative])).direction =
      (positiveRepresentative (by norm_num : (0 : ℝ) < 2)).direction :=
  GeodesicRepresentative.direction_shorten _ _ _

theorem approximation_by_actual_positive_segment (v : SpaceOfDirections (7 : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : GeodesicRepresentative (7 : ℝ), dist v σ.direction < ε ∧
      dist (7 : ℝ) (σ.path (σ.length / 2)) = σ.length / 2 := by
  obtain ⟨σ, hσ⟩ := v.exists_representative_dist_lt hε
  exact ⟨σ, hσ, σ.dist_base_path ⟨by linarith [σ.length_pos], by linarith [σ.length_pos]⟩⟩

private instance : HasAnglesAt (PUnit.unit : PUnit) where
  tendsto_angle σ := isEmptyElim σ

theorem singleton_completed_directions_empty :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit)) := inferInstance

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

private instance realHasAnglesAt (p : ℝ) : HasAnglesAt p :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ
    (real_comparison (by norm_num)) (mem_univ _)

private def positiveRepresentativeAt (p : ℝ) : GeodesicRepresentative p where
  length := 1
  length_pos := by norm_num
  curve := fun t => p + t.val
  isometry := by
    apply Isometry.of_dist_eq
    intro s t
    change |p + (s : ℝ) - (p + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
    congr 1
    ring
  start := by simp

private def negativeRepresentativeAt (p : ℝ) : GeodesicRepresentative p where
  length := 1
  length_pos := by norm_num
  curve := fun t => p - t.val
  isometry := by
    apply Isometry.of_dist_eq
    intro s t
    change |p - (s : ℝ) - (p - (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
    rw [show p - (s : ℝ) - (p - (t : ℝ)) = (t : ℝ) - s by ring, abs_sub_comm]
  start := by simp

private theorem positive_path_at (p t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (positiveRepresentativeAt p).path t = p + t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private theorem negative_path_at (p t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (negativeRepresentativeAt p).path t = p - t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private theorem real_representative_paths_at (p : ℝ) (σ : GeodesicRepresentative p) :
    (∀ t ∈ Icc (0 : ℝ) σ.length, σ.path t = p + t) ∨
    (∀ t ∈ Icc (0 : ℝ) σ.length, σ.path t = p - t) := by
  have hend := σ.dist_base_path ⟨σ.length_pos.le, le_rfl⟩
  rw [Real.dist_eq] at hend
  rcases (abs_eq σ.length_pos.le).mp hend with hneg | hpos
  · right
    intro t ht
    have h := σ.dist_base_path ht
    have hdist := σ.dist_path ht ⟨σ.length_pos.le, le_rfl⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hdist
    rw [Real.dist_eq] at h
    have hlow := le_abs_self (σ.path t - σ.path σ.length)
    have hhigh := le_abs_self (p - σ.path t)
    linarith
  · left
    intro t ht
    have h := σ.dist_base_path ht
    have hdist := σ.dist_path ht ⟨σ.length_pos.le, le_rfl⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hdist
    rw [Real.dist_eq] at h
    have hlow := neg_le_abs (σ.path t - σ.path σ.length)
    have hhigh := neg_le_abs (p - σ.path t)
    linarith

private theorem representative_direction_cases_at (p : ℝ) (σ : GeodesicRepresentative p) :
    σ.direction = (positiveRepresentativeAt p).direction ∨
      σ.direction = (negativeRepresentativeAt p).direction := by
  rcases real_representative_paths_at p σ with hp | hm
  · left
    rw [GeodesicRepresentative.direction_eq_iff]
    change germComparisonAngle 0 σ.path (positiveRepresentativeAt p).path = 0
    have h := germComparisonAngle_congr_on (κ := 0) σ.length_pos (by norm_num : (0 : ℝ) < 1)
      (γ := σ.path) (β := (positiveRepresentativeAt p).path)
      (γ' := fun t : ℝ => p + t) (β' := fun t : ℝ => p + t)
      (fun t ht => hp t ⟨ht.1.le, ht.2⟩)
      (fun t ht => positive_path_at p t ⟨ht.1.le, ht.2⟩)
    rw [h]
    apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
    intro s _ t _
    rw [Real.dist_eq]
    congr 1
    ring
  · right
    rw [GeodesicRepresentative.direction_eq_iff]
    change germComparisonAngle 0 σ.path (negativeRepresentativeAt p).path = 0
    have h := germComparisonAngle_congr_on (κ := 0) σ.length_pos (by norm_num : (0 : ℝ) < 1)
      (γ := σ.path) (β := (negativeRepresentativeAt p).path)
      (γ' := fun t : ℝ => p - t) (β' := fun t : ℝ => p - t)
      (fun t ht => hm t ⟨ht.1.le, ht.2⟩)
      (fun t ht => negative_path_at p t ⟨ht.1.le, ht.2⟩)
    rw [h]
    apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
    intro s _ t _
    rw [Real.dist_eq, show p - s - (p - t) = t - s by ring, abs_sub_comm]

private theorem direction_cases_at (p : ℝ) (v : SpaceOfDirections p) :
    v = (positiveRepresentativeAt p).direction ∨ v = (negativeRepresentativeAt p).direction := by
  by_contra hn
  have hp : 0 < dist v (positiveRepresentativeAt p).direction :=
    dist_pos.mpr (fun h => hn (Or.inl h))
  have hm : 0 < dist v (negativeRepresentativeAt p).direction :=
    dist_pos.mpr (fun h => hn (Or.inr h))
  obtain ⟨σ, hσ⟩ := v.exists_representative_dist_lt (lt_min hp hm)
  rcases representative_direction_cases_at p σ with h | h
  · rw [h] at hσ
    exact (not_lt_of_ge (min_le_left _ _)) hσ
  · rw [h] at hσ
    exact (not_lt_of_ge (min_le_right _ _)) hσ

theorem actual_real_direction_obstruction_everywhere (p : ℝ) :
    AngularObstruction (SpaceOfDirections p) 1 (1 / 16) := by
  rintro ⟨ξ, ζ, hζ, hξ⟩
  have hpair := hζ (0 : Fin 2) 1 (by decide)
  have hzero := hξ (0 : Fin 2)
  have hone := hξ (1 : Fin 2)
  rcases direction_cases_at p (ζ 0) with h₀ | h₀ <;>
    rcases direction_cases_at p (ζ 1) with h₁ | h₁ <;>
    rcases direction_cases_at p ξ with hx | hx
  all_goals
    simp only [h₀, h₁, hx, dist_self] at hpair hzero hone
    linarith [Real.two_le_pi]


theorem actual_real_opposite_directions_everywhere (p : ℝ) :
    ∃ σ τ : GeodesicRepresentative p, σ.length = 1 ∧ τ.length = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ.path t = p + t ∧ τ.path t = p - t) ∧
      dist σ.direction τ.direction = Real.pi := by
  refine ⟨positiveRepresentativeAt p, negativeRepresentativeAt p, rfl, rfl,
    fun t ht => ⟨positive_path_at p t ht, negative_path_at p t ht⟩, ?_⟩
  rw [GeodesicRepresentative.dist_direction]
  change germComparisonAngle 0 (positiveRepresentativeAt p).path
    (negativeRepresentativeAt p).path = Real.pi
  apply germComparisonAngle_opposite (by norm_num)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  intro s hs t ht
  rw [positive_path_at p s ⟨hs.1.le, hs.2⟩, negative_path_at p t ⟨ht.1.le, ht.2⟩,
    Real.dist_eq, show p + s - (p - t) = s + t by ring,
    abs_of_pos (add_pos hs.1 ht.1)]

end GCDirectionSpaceReview

noncomputable section

open Set Filter Topology Metric InnerProductGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCPlaneDirectionPackingReview

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem comparison_eq_angle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : comparisonAngle ‖x‖ ‖y‖ ‖x - y‖ = angle x y := by
  rw [comparisonAngle, angle, norm_sub_pow_two_real]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem inner_comparison {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    fourPointComparison 0 (univ : Set V) := by
  intro p hp a ha b hb c hc hap hbp hcp
  simp only [comparisonAngleNegCurvature_zero]
  have he (x y : V) : comparisonAngle (dist p x) (dist p y) (dist x y) = angle (x - p) (y - p) := by
    rw [dist_comm p x, dist_comm p y]
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using comparison_eq_angle (x - p) (y - p)
  rw [he a b, he b c, he c a]
  have ht := angle_le_angle_add_angle (a - p) (-(b - p)) (c - p)
  rw [angle_neg_right, angle_neg_left, angle_comm (a - p) (c - p)] at ht
  linarith

private def base : Plane := WithLp.toLp 2 ![7, -3]

private def vector (i : Fin 3) : Plane :=
  ![WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![-3/5, 4/5], WithLp.toLp 2 ![-3/5, -4/5]] i

private theorem vector_norm (i : Fin 3) : ‖vector i‖ = 1 := by
  have hs : ‖vector i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    change (∑ j : Fin 2, (vector i) j * (vector i) j) = 1
    fin_cases i <;> norm_num [vector, Fin.sum_univ_two]
  nlinarith [norm_nonneg (vector i)]

private theorem vector_inner_neg (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (vector i) (vector j) < 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [vector, PiLp.inner_apply, Fin.sum_univ_two] at *

private def ray (i : Fin 3) (t : ℝ) : Plane := base + t • vector i

private theorem ray_isometry (i : Fin 3) : Isometry (ray i) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, ray, ray,
    show base + s • vector i - (base + t • vector i) = (s - t) • vector i by
      rw [sub_smul]; abel,
    norm_smul, Real.norm_eq_abs, vector_norm, mul_one, Real.dist_eq]

private def representative (i : Fin 3) : GeodesicRepresentative base where
  length := (i.val : ℝ) + 1
  length_pos := by positivity
  curve := fun t => ray i t.val
  isometry := (ray_isometry i).comp isometry_subtype_coe
  start := by simp [ray]

private theorem representative_path (i : Fin 3) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) ((i.val : ℝ) + 1)) :
    (representative i).path t = ray i t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private instance : HasAnglesAt base :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ inner_comparison (mem_univ _)

private theorem ray_comparison (i j : Fin 3) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    comparisonAngleNegCurvature 0 s t (dist (ray i s) (ray j t)) =
      angle (vector i) (vector j) := by
  rw [comparisonAngleNegCurvature_zero, dist_eq_norm,
    show ray i s - ray j t = s • vector i - t • vector j by unfold ray; abel]
  have h := comparison_eq_angle (s • vector i) (t • vector j)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hs, abs_of_pos ht, vector_norm, vector_norm, mul_one, mul_one] at h
  rw [h, angle_smul_left_of_pos _ _ hs, angle_smul_right_of_pos _ _ ht]

private theorem representative_angle (i j : Fin 3) :
    (representative i).angle (representative j) = angle (vector i) (vector j) := by
  change germComparisonAngle 0 (representative i).path (representative j).path = _
  rw [germComparisonAngle_congr_on (representative i).length_pos (representative j).length_pos
    (γ' := ray i) (β' := ray j)
    (fun t ht => representative_path i t ⟨ht.1.le, ht.2⟩)
    (fun t ht => representative_path j t ⟨ht.1.le, ht.2⟩)]
  apply germComparisonAngle_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  have hp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hp.prod_inl _, hp.prod_inr _] with z hs ht
  exact (ray_comparison i j hs ht).symm

theorem actual_translated_plane_direction_packing :
    (∀ i : Fin 3, (representative i).length = (i.val : ℝ) + 1) ∧
    (∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) ((i.val : ℝ) + 1),
      (representative i).path t = base + t • vector i) ∧
    (∀ i j : Fin 3, dist (representative i).direction (representative j).direction =
      angle (vector i) (vector j)) ∧
    ∀ i j : Fin 3, i ≠ j → Real.pi / 2 <
      dist (representative i).direction (representative j).direction := by
  refine ⟨fun _ => rfl, representative_path, ?_, ?_⟩
  · intro i j
    rw [GeodesicRepresentative.dist_direction, representative_angle]
  · intro i j hij
    rw [GeodesicRepresentative.dist_direction, representative_angle]
    exact inner_neg_iff_pi_div_two_lt_angle.mp (vector_inner_neg i j hij)

end GCPlaneDirectionPackingReview

namespace GCPlaneDirectionPackingReview

private theorem plane_segments (x y : Plane) :
    ∃ f : unitInterval → Plane, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → Plane := fun t => x + (t : ℝ) • (y - x)
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  rw [dist_eq_norm, show f s - f t = ((s : ℝ) - t) • (y - x) by
    dsimp [f]; rw [sub_smul]; abel, norm_smul, Real.norm_eq_abs,
    ← dist_eq_norm y x, dist_comm y x]
  change |(s : ℝ) - t| * dist x y = dist x y * |(s : ℝ) - t|
  exact mul_comm _ _

private theorem plane_short_curves : ∀ x y : Plane, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → Plane, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments plane_segments

private def center : Plane := ray 0 (1 / 2)

private theorem base_center_dist : dist base center = 1 / 2 := by
  have h := (ray_isometry 0).dist_eq 0 (1 / 2)
  simpa [ray, center, Real.dist_eq] using h

private theorem plane_intrinsic_local :
    ∀ z : ball center (8 * (2 : ℝ)), ∃ Ω : Set (ball center (8 * (2 : ℝ))),
      @IsOpen _ (intrinsicBallMetricSpace plane_short_curves center
        (by norm_num : (0 : ℝ) < 8 * 2)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ (intrinsicBallMetricSpace plane_short_curves center
        (by norm_num : (0 : ℝ) < 8 * 2)) 1 Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff plane_short_curves center
    (by norm_num : (0 : ℝ) < 8 * 2) z).mpr
    ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num), mem_univ _⟩

private def negative_ray (t : ℝ) : Plane := base - t • vector 0

private theorem negative_ray_isometry : Isometry negative_ray := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, negative_ray, negative_ray,
    show base - s • vector 0 - (base - t • vector 0) = (t - s) • vector 0 by
      rw [sub_smul]; abel,
    norm_smul, Real.norm_eq_abs, vector_norm, mul_one, Real.dist_eq, abs_sub_comm]

private def negative_rep : GeodesicRepresentative base where
  length := 3
  length_pos := by norm_num
  curve := fun t => negative_ray t.val
  isometry := negative_ray_isometry.comp isometry_subtype_coe
  start := by simp [negative_ray]

private theorem negative_rep_path (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 3) :
    negative_rep.path t = negative_ray t := by
  rw [GeodesicRepresentative.path_of_mem _ ht]
  rfl

private theorem opposite_endpoint_distance (t : ℝ) (ht : 0 ≤ t) :
    dist (ray 0 t) (negative_ray t) = 2 * t := by
  rw [dist_eq_norm, ray, negative_ray,
    show base + t • vector 0 - (base - t • vector 0) = (2 * t) • vector 0 by
      rw [mul_smul]; norm_num; module,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), vector_norm, mul_one]

private theorem opposite_direction_distance :
    dist (representative 0).direction negative_rep.direction = Real.pi := by
  rw [GeodesicRepresentative.dist_direction]
  change germComparisonAngle 0 (representative 0).path negative_rep.path = Real.pi
  apply germComparisonAngle_eq_of_tendsto
  have hev : ∀ᶠ z : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
      z.1 ∈ Ioc (0 : ℝ) 1 ∧ z.2 ∈ Ioc (0 : ℝ) 3 :=
    by
      have h₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) 1 :=
        Ioc_mem_nhdsGT (by norm_num)
      have h₂ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) 3 :=
        Ioc_mem_nhdsGT (by norm_num)
      filter_upwards [h₁.prod_inl _, h₂.prod_inr _] with z hz₁ hz₂ using ⟨hz₁, hz₂⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with z hz
  rw [representative_path 0 z.1 (by simpa using ⟨hz.1.1.le, hz.1.2⟩),
    negative_rep_path z.2 ⟨hz.2.1.le, hz.2.2⟩]
  have hd : dist (ray 0 z.1) (negative_ray z.2) = z.1 + z.2 := by
    rw [dist_eq_norm, ray, negative_ray,
      show base + z.1 • vector 0 - (base - z.2 • vector 0) =
          (z.1 + z.2) • vector 0 by rw [add_smul]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos hz.1.1 hz.2.1), vector_norm, mul_one]
  rw [hd]
  exact (comparisonAngleNegCurvature_add (by norm_num) hz.1.1 hz.2.1).symm

private theorem noncollinear_direction_distance :
    dist (representative 0).direction (representative 1).direction = Real.arccos (-3 / 5) := by
  rw [GeodesicRepresentative.dist_direction, representative_angle, angle, vector_norm, vector_norm]
  norm_num [vector, PiLp.inner_apply, Fin.sum_univ_two]

private theorem noncollinear_endpoint_distance_sq :
    dist ((representative 0).path 1) ((representative 1).path 1) ^ 2 = 16 / 5 := by
  rw [representative_path 0 1 (by norm_num), representative_path 1 1 (by norm_num),
    dist_eq_norm, ← real_inner_self_eq_norm_sq]
  change (∑ j : Fin 2, (ray 0 1 - ray 1 1) j * (ray 0 1 - ray 1 1) j) = 16 / 5
  norm_num [ray, vector, Fin.sum_univ_two, base]

end GCPlaneDirectionPackingReview

noncomputable section

open Set Metric
open scoped NNReal
open Metric.EuclideanCone

namespace GCConeAntipodalLineReview

theorem unbounded_angular_cap_preserves_both_rays :
    Real.pi < dist (0 : ℝ) (2 * Real.pi) ∧
    Isometry (twoRayPath (0 : ℝ) (2 * Real.pi)) ∧
    twoRayPath (0 : ℝ) (2 * Real.pi) 0 = tip ∧
    (∀ r : ℝ≥0, twoRayPath (0 : ℝ) (2 * Real.pi) r = mk r 0 ∧
      twoRayPath (0 : ℝ) (2 * Real.pi) (-r) = mk r (2 * Real.pi)) ∧
    dist (twoRayPath (0 : ℝ) (2 * Real.pi) 2)
      (twoRayPath (0 : ℝ) (2 * Real.pi) (-3)) = 5 := by
  have hd : dist (0 : ℝ) (2 * Real.pi) = 2 * Real.pi := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  have hi : Isometry (twoRayPath (0 : ℝ) (2 * Real.pi)) :=
    isometry_twoRayPath_iff.mpr (by rw [hd]; linarith [Real.pi_pos])
  refine ⟨by rw [hd]; linarith [Real.pi_pos], hi, twoRayPath_zero _ _,
    fun r => ⟨twoRayPath_coe _ _ r, twoRayPath_neg_coe _ _ r⟩, ?_⟩
  rw [hi.dist_eq, Real.dist_eq]
  norm_num

theorem sub_pi_directions_do_not_form_a_line :
    dist (twoRayPath (0 : ℝ) (Real.pi / 2) 1)
      (twoRayPath (0 : ℝ) (Real.pi / 2) (-1)) = Real.sqrt 2 ∧
    ¬ Isometry (twoRayPath (0 : ℝ) (Real.pi / 2)) := by
  have hd : dist (0 : ℝ) (Real.pi / 2) = Real.pi / 2 := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  constructor
  · have hp : twoRayPath (0 : ℝ) (Real.pi / 2) (1 : ℝ) = mk 1 0 :=
      twoRayPath_coe _ _ 1
    have hm : twoRayPath (0 : ℝ) (Real.pi / 2) (-1 : ℝ) = mk 1 (Real.pi / 2) :=
      twoRayPath_neg_coe _ _ 1
    rw [hp, hm, dist_mk]
    unfold coneDistance
    rw [hd, min_eq_right (by linarith [Real.pi_pos]), Real.cos_pi_div_two]
    norm_num
  · rw [isometry_twoRayPath_iff, hd]
    linarith [Real.pi_pos]

end GCConeAntipodalLineReview

namespace GCDirectionSpaceReview

theorem actual_real_antipodal_tangent_line :
    ∃ σ τ : GeodesicRepresentative (7 : ℝ),
      σ.length = 1 ∧ τ.length = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ.path t = 7 + t ∧ τ.path t = 7 - t) ∧
      Isometry (twoRayPath σ.direction τ.direction) ∧
      twoRayPath σ.direction τ.direction 0 = (tip : TangentCone (7 : ℝ)) ∧
      ∀ r : ℝ≥0,
        twoRayPath σ.direction τ.direction r = σ.tangentVector r ∧
        twoRayPath σ.direction τ.direction (-r) = τ.tangentVector r := by
  obtain ⟨σ, τ, hσ, hτ, hp, hd⟩ := actual_real_opposite_directions_everywhere 7
  exact ⟨σ, τ, hσ, hτ, hp, isometry_twoRayPath_iff.mpr hd.ge,
    twoRayPath_zero _ _, fun r => ⟨twoRayPath_coe _ _ r, twoRayPath_neg_coe _ _ r⟩⟩

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

theorem actual_plane_unequal_domain_antipodal_tangent_line :
    (representative 0).length = 1 ∧ negative_rep.length = 3 ∧
    dist (representative 0).direction negative_rep.direction = Real.pi ∧
    Isometry (twoRayPath (representative 0).direction negative_rep.direction) ∧
    twoRayPath (representative 0).direction negative_rep.direction 0 =
      (tip : TangentCone base) ∧
    ∀ r : ℝ≥0,
      twoRayPath (representative 0).direction negative_rep.direction r =
        (representative 0).tangentVector r ∧
      twoRayPath (representative 0).direction negative_rep.direction (-r) =
        negative_rep.tangentVector r := by
  exact ⟨by norm_num [representative], rfl, opposite_direction_distance,
    isometry_twoRayPath_iff.mpr opposite_direction_distance.ge, twoRayPath_zero _ _,
    fun r => ⟨twoRayPath_coe _ _ r, twoRayPath_neg_coe _ _ r⟩⟩

end GCPlaneDirectionPackingReview

namespace GCConeAntipodalLineReview

open DifferentialGeometry.Geometry.Comparison.Toponogov

theorem actual_equator_cap_and_zero_radius :
    lineCoordinate (twoRayPath (0 : ℝ) Real.pi) (mk 3 (Real.pi / 2)) = 0 ∧
    lineCoordinate (twoRayPath (0 : ℝ) Real.pi) (mk 2 (2 * Real.pi)) = -2 ∧
    lineCoordinate (twoRayPath (0 : ℝ) Real.pi) (mk 2 (Real.pi / 3)) = 1 ∧
    lineCoordinate (twoRayPath (0 : ℝ) Real.pi) (mk 0 (0 : ℝ)) = 0 ∧
    dist (0 : ℝ) 0 ≠ Real.pi / 2 := by
  have hhalf : dist (0 : ℝ) (Real.pi / 2) = Real.pi / 2 := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  have hdouble : dist (0 : ℝ) (2 * Real.pi) = 2 * Real.pi := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  have hthird : dist (0 : ℝ) (Real.pi / 3) = Real.pi / 3 := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  refine ⟨(lineCoordinate_twoRayPath_mk_eq_zero_iff _ _ _ (by norm_num)).mpr hhalf,
    ?_, ?_, ?_, ?_⟩
  · rw [lineCoordinate_twoRayPath_mk, hdouble,
      min_eq_left (by linarith [Real.pi_pos]), Real.cos_pi]
    norm_num
  · rw [lineCoordinate_twoRayPath_mk, hthird,
      min_eq_right (by linarith [Real.pi_pos]), Real.cos_pi_div_three]
    norm_num
  · rw [lineCoordinate_twoRayPath_mk]
    norm_num
  · rw [dist_self]
    linarith [Real.pi_pos]

end GCConeAntipodalLineReview

namespace GCPlaneDirectionPackingReview

theorem actual_plane_original_direction_coordinate :
    ∀ r : ℝ≥0,
      lineCoordinate (twoRayPath (representative 0).direction negative_rep.direction)
        ((representative 1).tangentVector r) = (-3 / 5 : ℝ) * r := by
  intro r
  change lineCoordinate (twoRayPath (representative 0).direction negative_rep.direction)
    (mk r (representative 1).direction) = _
  rw [lineCoordinate_twoRayPath_mk, noncollinear_direction_distance,
    min_eq_right (Real.arccos_le_pi _), Real.cos_arccos (by norm_num) (by norm_num)]
  ring

end GCPlaneDirectionPackingReview

noncomputable section

namespace GCConeArcDirectionsReview

open Set Metric Metric.EuclideanCone
open scoped NNReal

private abbrev Angle := Icc (0 : ℝ) Real.pi

private def leftAngle : Angle := ⟨0, by simp [Real.pi_pos.le]⟩

private def rightAngle : Angle := ⟨Real.pi, by simp [Real.pi_pos.le]⟩

private theorem angle_diameter (a b : Angle) : dist a b ≤ Real.pi := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor <;> linarith [a.property.1, a.property.2, b.property.1, b.property.2]

private def anglePath (t : Icc (0 : ℝ) 1) : Angle :=
  ⟨Real.pi * t.val, mul_nonneg Real.pi_pos.le t.property.1,
    by simpa using mul_le_mul_of_nonneg_left t.property.2 Real.pi_pos.le⟩

private theorem anglePath_dist (s t : Icc (0 : ℝ) 1) :
    dist (anglePath s) (anglePath t) = Real.pi * dist s t := by
  change |Real.pi * s.val - Real.pi * t.val| = Real.pi * |s.val - t.val|
  rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]

private theorem endpoint_dist : dist leftAngle rightAngle = Real.pi := by
  change |0 - Real.pi| = Real.pi
  rw [zero_sub, abs_neg, abs_of_pos Real.pi_pos]

theorem actual_radius_two_full_pi_arc :
    ∃ g : Icc (0 : ℝ) 1 → Angle, Continuous g ∧
      g ⟨0, by norm_num⟩ = leftAngle ∧ g ⟨1, by norm_num⟩ = rightAngle ∧
      (∀ t, mk (2 : ℝ≥0) (anglePath t) = mk 2 (g t)) ∧
      (∀ s t, dist (g s) (g t) = Real.pi * dist s t) ∧
      (∀ t, g t = anglePath t) ∧ g ⟨0, by norm_num⟩ ≠ g ⟨1, by norm_num⟩ := by
  have hd : ∀ s t : Icc (0 : ℝ) 1,
      dist (mk (2 : ℝ≥0) (anglePath s)) (mk 2 (anglePath t)) ^ 2 =
        2 * ((2 : ℝ≥0) : ℝ) ^ 2 * (1 - Real.cos (dist leftAngle rightAngle * dist s t)) := by
    intro s t
    rw [dist_mk, coneDistance_sq (by norm_num) (by norm_num), min_eq_right (angle_diameter _ _),
      anglePath_dist, endpoint_dist]
    norm_num
    ring
  obtain ⟨g, hg, h0, h1, hsame, hdg⟩ := exists_base_segment_of_cone_arc angle_diameter
    (r := 2) (by norm_num) leftAngle rightAngle (fun t => mk 2 (anglePath t))
    (by congr 1; apply Subtype.ext; simp [anglePath, leftAngle])
    (by congr 1; apply Subtype.ext; simp [anglePath, rightAngle])
    (fun t => radius_mk _ _) hd
  have hactual : ∀ t, g t = anglePath t := by
    intro t
    have h := hsame t
    rw [mk_pos (by norm_num : (0 : ℝ) < ((2 : ℝ≥0) : ℝ)),
      mk_pos (by norm_num : (0 : ℝ) < ((2 : ℝ≥0) : ℝ))] at h
    exact (congrArg Prod.snd (Option.some.inj h)).symm
  refine ⟨g, hg, h0, h1, hsame, ?_, hactual, ?_⟩
  · simpa only [endpoint_dist] using hdg
  · rw [h0, h1]
    intro he
    have := congrArg Subtype.val he
    exact Real.pi_ne_zero (by simpa only [leftAngle, rightAngle] using this.symm)

theorem actual_radius_two_coincident_arc :
    ∃ g : Icc (0 : ℝ) 1 → Angle, Continuous g ∧
      (∀ t, mk (2 : ℝ≥0) leftAngle = mk 2 (g t)) ∧ ∀ t, g t = leftAngle := by
  obtain ⟨g, hg, h0, _, hsame, hdg⟩ := exists_base_segment_of_cone_arc angle_diameter
    (r := 2) (by norm_num) leftAngle leftAngle (fun _ => mk 2 leftAngle)
    rfl rfl (fun _ => radius_mk _ _) (by intros; simp)
  refine ⟨g, hg, hsame, ?_⟩
  intro t
  have h := hdg t ⟨0, by norm_num⟩
  simpa only [h0, dist_self, zero_mul, dist_eq_zero] using h

theorem zero_radius_does_not_recover_angle :
    dist (mk (0 : ℝ≥0) leftAngle) (mk 0 rightAngle) ^ 2 =
      2 * ((0 : ℝ≥0) : ℝ) ^ 2 * (1 - Real.cos 0) ∧
      dist leftAngle rightAngle ≠ 0 := by
  constructor
  · simp
  · rw [endpoint_dist]
    exact Real.pi_ne_zero

theorem cap_does_not_recover_uncapped_distance :
    dist (mk (2 : ℝ≥0) (0 : ℝ)) (mk 2 (2 * Real.pi)) ^ 2 =
      2 * ((2 : ℝ≥0) : ℝ) ^ 2 * (1 - Real.cos Real.pi) ∧
      dist (0 : ℝ) (2 * Real.pi) ≠ Real.pi := by
  have hdist : dist (0 : ℝ) (2 * Real.pi) = 2 * Real.pi := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  constructor
  · rw [dist_mk, coneDistance_sq (by norm_num) (by norm_num), hdist,
      min_eq_left (by linarith [Real.pi_pos])]
    norm_num
  · rw [hdist]
    linarith [Real.pi_pos]

end GCConeArcDirectionsReview

#lint- only unusedArguments simpNF synTaut
#print axioms Metric.EuclideanCone.twoRayPath
#print axioms Metric.EuclideanCone.twoRayPath_coe
#print axioms Metric.EuclideanCone.twoRayPath_neg_coe
#print axioms Metric.EuclideanCone.twoRayPath_zero
#print axioms Metric.EuclideanCone.dist_mk_eq_add_of_pi_le
#print axioms Metric.EuclideanCone.isometry_twoRayPath_iff
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineCoordinate_twoRayPath_mk
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineCoordinate_twoRayPath_mk_eq_zero_iff
#print axioms Metric.EuclideanCone.dist_eq_of_dist_mk_sq_eq
#print axioms Metric.EuclideanCone.exists_base_segment_of_cone_arc
#print axioms GCConeAntipodalLineReview.unbounded_angular_cap_preserves_both_rays
#print axioms GCConeAntipodalLineReview.sub_pi_directions_do_not_form_a_line
#print axioms GCDirectionSpaceReview.actual_real_antipodal_tangent_line
#print axioms GCPlaneDirectionPackingReview.actual_plane_unequal_domain_antipodal_tangent_line
#print axioms GCConeAntipodalLineReview.actual_equator_cap_and_zero_radius
#print axioms GCPlaneDirectionPackingReview.actual_plane_original_direction_coordinate
#print axioms GCConeArcDirectionsReview.actual_radius_two_full_pi_arc
#print axioms GCConeArcDirectionsReview.actual_radius_two_coincident_arc
#print axioms GCConeArcDirectionsReview.zero_radius_does_not_recover_angle
#print axioms GCConeArcDirectionsReview.cap_does_not_recover_uncapped_distance
```

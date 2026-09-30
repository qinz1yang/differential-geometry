# Actual Euclidean cone, apex and completeness

Twenty-eight public theorems, five definitions and two metric/completeness instances in four leaves construct an actual Euclidean cone over any metric space and prove completeness when its base is complete. No base nonemptiness, diameter bound, properness, compactness, curvature or supplied cone realization is assumed. The exact cosine rule uses min(pi,direction distance); the angular shell is not mislabeled an isometric copy of the base.

## Source and edge convention

Fresh body reading of archived AKP, Alexandrov geometry: foundations, Section6E printed/PDF67–68 gives the Euclidean cone, tip, norm and actual tangent-space definition. The complete-base implication is explicitly used in the gluing proof on printed/PDF128; our proof uses only the cosine formula, not the CAT or gluing hypotheses surrounding that application. PDF SHA2561ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed. The separately pinned retained TeX revision is ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245. Retained author errata were checked with no relevant correction; no fresh external retrieval is claimed.

For nonempty bases the Option of positive-radius/direction pairs is the normal form of the source's collapsed-zero quotient. For an empty base the implementation explicitly adjoins a singleton apex. The literal empty-product quotient would be empty; this pointed extension is stated rather than hidden by assuming a direction. It is needed for the tangent of a singleton source and agrees with admitting a constant zero-speed germ.

## Proof and hypotheses

The scalar triangle is realized by three actual Euclidean-plane polar points after capping the three angular distances at pi. Cone metric triangles involving the apex follow from the same scalar triangle or the radial-distance lower bound; positive-pair separation follows from the exact cosine formula. The actual carrier supports arbitrary nonnegative radial constructors, an isometric half-line for every direction, a 1-Lipschitz radius and exact dilation identity/product/metric scaling.

The new inverse estimate is 2*rho*min(pi,direction distance)<=pi*coneDistance when both radii are at least rho>=0. It follows from the half-angle cosine identity and Jordan's sine inequality; a strict threshold yields actual direction closeness, without a diameter assumption. Thus a cone-Cauchy sequence whose radii stay positive has Cauchy directions. Any cone-Cauchy sequence first has convergent radii. Radius limit zero gives convergence to the apex. For a positive limit, an actual positive sequence element supplies the only local fallback direction; no global nonempty instance is invented. Completeness of the base and continuity of the scalar formula finish convergence.

The unchanged canonical Geometry/Metric/ConeDistance leaf is reused after a full source inspection and targeted build, with its hash recorded. No duplicated scalar definition or changing-PC interface is introduced. The actual tangent association and Euclidean-tangent strut adapter are separate consumers. No claim of CBB geometry of arbitrary cones or existence of Euclidean tangents is made. Blueprint207 and earlier mathematical leaves are unchanged.

## Verification

All four frozen leaves compile in the shared412-module gate, which checks2011 owned declarations. Seventeen actual-object regressions,51 standard axiom reports, selected lint, independent full reviews and the separate blueprint static audit pass. Final actual checks are recorded in the acceptance receipt and review.

# Actual Euclidean cone constructor

Verdict: the temporary implementation compiles with minimal imports, selected lint is silent, and every public theorem has only the standard three axioms. Independent proof review and concrete regressions are separately authored by ac65_same_lines. Repository registration, accepted-import verification, shared gates and delivery remain parent responsibilities.

## Contract

`Metric.EuclideanCone Y` is the concrete carrier `Option ({r : ℝ // 0 < r} × Y)`. Its apex is `none`; a positive pair retains its original radius and direction. The metric instance requires only `MetricSpace Y`. There is no diameter bound, nonemptiness, CBB assumption, properness, completeness, or supplied realization. For arbitrary nonnegative NNReal radii the `mk` distance is precisely the existing `coneDistance` formula using `cos (min pi (dist u v))`. Zero-radius inputs all map to the apex.

The public API consists of five definitions (carrier, tip, radius, mk, dilate), one metric instance, and 24 theorems. It includes exact tip distances and radii, positive-pair and positive-mk elimination, the radius-zero/apex equivalence, the 1-Lipschitz radius map, an actual isometric ray for each direction, and dilation zero/one/product laws and exact distance scaling. Pure carrier/radial algebraic lemmas impose no metric assumption. Dilation is defined on the actual carrier and handles the apex without choosing any direction.

## Proof

The distance is defined by four apex/positive-pair cases. Metric symmetry and positive-radius separation use the accepted scalar cone distance; the eight triangle cases use the independently proved scalar triangle plus its zero-radius upper bound or its lower bound by radial difference. Positive pairs at zero distance are equal as radius-direction pairs, hence equal in the actual Option carrier. The apex-to-positive distance cannot vanish. Every scalar-to-carrier distance rewrite is checked for both zero and positive radii.

Dilation maps a positive pair to `mk` at the multiplied radius. The product/identity laws use actual point elimination, and its metric scaling law invokes the existing exact scalar radial multiplication identity. The radial isometry is from the ordinary metric NNReal half-line; it is not a claim that the unit shell has the original angular distance.

## Source and conventions

Archived Alexander--Kapovitch--Petrunin, *Alexandrov geometry: foundations*, Chapter 6E, printed/PDF pp.67–68; archive PDF SHA256 `1ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed`. The actual definition, cosine formula, tip/norm and tangent-space paragraphs were reread from `/tmp/gc125_assessment/AlexanderKapovitchPetrunin303Alexandrov.txt`, lines about2660–2720. Section6D on the preceding page defines the angle-zero quotient and completion; it is the separate direction-space interface already reviewed. The pinned retained TeX revision is `ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`; these initial6D/E paragraphs are absent from the retained excerpt, so they are not falsely attributed to `tan.tex`. The retained erratum file was checked in the preceding direction-space review and contains no correction affecting these definitions; no new remote errata claim is made.

For nonempty Y, the Option carrier represents exactly the source's quotient of `[0,infinity) × Y` collapsing the zero shell. For empty Y, this implementation explicitly adjoins a singleton apex; the literal quotient of the empty product would be empty. This is a deliberate pointed extension, needed for the tangent cone at a singleton space, and is not hidden behind an assumed direction or an inhabitedness hypothesis. The corresponding actual empty-direction cone test is independently compiled.

The scalar triangle is the frozen `/tmp/gc_ConeDistanceTriangle_body.lean`, SHA256 `507fe5cb217f94463a96853e5b5902a0ac3f7cf8b73c4579af59bb6bb2fdc3b9`; its actual planar proof and source record are separate. The existing canonical `DifferentialGeometry.Geometry.Metric.ConeDistance` is reused unchanged, as reviewed and individually built by the parent.

## Verification and integration

Normal driver: `lake env lean /tmp/gc_EuclideanCone_agent.lean`, actual exit0 with empty log. This driver imports only canonical ConeDistance, Mathlib.Analysis.InnerProductSpace.PiL2, Mathlib.Tactic.LinearCombination, then concatenates the scalar triangle and constructor body. Once registered, the constructor should import the canonical scalar triangle leaf, whose transitive imports supply these dependencies. No Mathlib.Tactic umbrella is needed in production.

Lint/axiom driver: `lake env lean /tmp/gc_EuclideanCone_lint.lean`, actual exit0. `#lint- only unusedArguments simpNF synTaut` is silent. All24 public theorem closures are exactly `[propext, Classical.choice, Quot.sound]`. Production contains no comments, admissions, new axioms, resource-budget settings, or warning suppression. Lean4.35.0-rc3 and Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e`.

Completeness and the actual tangent-cone association are separate implementations. This constructor itself does not claim a Euclidean tangent realization, properness, finite dimensionality, or a CBB property. Blueprint207 and the PC migration boundary are unchanged.

## Frozen files

- `/tmp/gc_EuclideanCone_body.lean`: SHA256 `35f376c6d51931577dae6d9c1a9cf1222482775a3e032fcfe216b28d2eed1c96`.
- `/tmp/gc_EuclideanCone_agent.lean`: SHA256 `2b25c0eecaa9ae635630bb3df62ab65be0a3f5f282d99188b84687ae6a4ad36b`.
- `/tmp/gc_EuclideanCone_lint.lean`: SHA256 `d88fa92388a184e52855992e88cabb203096749cb2dbc8497d16ff7206dd1c82`.
- `/tmp/gc_EuclideanCone_lint.log`: SHA256 `f62d0c4d6bfaae84ae32f466c51a8ae8afd4fa440b28fc904e11ae4e54ce325f`.

# Generic cone distance triangle

Verdict: frozen temp production and regression proof/compiler/lint/axiom checks pass. Repository registration and shared-build delivery are separate parent responsibilities. No repository edits or shared builds were made by the implementing subagent.

## Frozen files

- `/tmp/gc_ConeDistanceTriangle_body.lean`: SHA256 `507fe5cb217f94463a96853e5b5902a0ac3f7cf8b73c4579af59bb6bb2fdc3b9`.
- `/tmp/gc_ConeDistanceTriangle_agent.lean`: SHA256 `9e60725e8dc3fa508b8c7fd655b11b65063cf3dc1cf1a54da81947f532cd4f87`.
- `/tmp/gc_cone_distance_triangle_review_body.lean`: SHA256 `35ac4399b258f6d27e1f0615300c567c93451c47c8fdcd003ce0a6abafc321bb`.
- `/tmp/gc_cone_distance_triangle_review_agent.lean`: SHA256 `9a4fedd7fcc018c5e67528e75bee942b4cacf74c51e193291773f5bbaa438d41`.
- `/tmp/gc_cone_distance_triangle_review_lint.lean`: SHA256 `5670fae7b742afe9660248fe5d1b9e8d78cdc1cebeb6da82ee99f55a25ced1b6`.

## Exact contract and implementation

One new public theorem, `Metric.coneDistance_triangle`, with one private plane-point definition and one private exact distance theorem. For any PseudoMetricSpace Y and original x,y,z:real×Y with nonnegative radii, the existing Metric.coneDistance satisfies triangle. It uses the existing exact formula with min(pi,dist directions). No diameter bound, nonemptiness, CBB, completeness, actual source approximation, or presumed realization in a cone is assumed. The three original points and all radii are retained; zero radii are allowed.

Minimal imports: canonical DifferentialGeometry.Geometry.Metric.ConeDistance, Mathlib.Analysis.InnerProductSpace.PiL2, Mathlib.Tactic.LinearCombination. The parent independently audited and built the unchanged existing ConeDistance leaf before its reuse; no duplicate scalar definition was added.

The proof realizes explicit points (r cos theta,r sin theta) in the actual Euclidean plane and proves their squared cosine distance from the actual EuclideanSpace distance formula. The capped directional distances a,b,c obey c<=a+b. Put d=min(pi,a+b); then c<=d, a<=d, and d-a<=b. Cosine monotonicity bounds the original outer distance by the outer plane distance and the last plane side by the original last distance. The same middle plane point yields the desired result via the ordinary plane metric triangle inequality. The nonnegative radial guards are used by cosine monotonicity; they are not decorative. No square-root differentiability or strict angular/radial hypothesis is needed.

## Source

Archived AKP Alexandrov geometry: foundations, Chapter6E, printed/PDF67–68, PDF SHA2561ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed: Euclidean cone cosine formula with angle cap pi. Its displayed metric is now proved triangular by a direct algebraic planar proof. The archived source definition and retained pinned TeX/erratum are kept distinct; detailed source and empty-apex discussion is in /tmp/gc_EuclideanCone_tangent_API_audit.md. Cone(empty) as a singleton apex is the explicit pointed extension required by the tangent construction; this scalar theorem neither invents a direction nor assumes an inhabited base.

## Independent review and tests

Parent independently read the complete production body and actual Euclidean-plane proof, reporting no findings. The proof handles arbitrary capped angles and zero radii.

Three concrete public tests:
1. Y=real with actual direction parameters0,pi/3,2pi/3 and radii1,2,3. The three exact cone distances are sqrt3,sqrt7,sqrt13, and the new theorem supplies sqrt13<=sqrt3+sqrt7.
2. Y=real with actual parameters0,2pi,4pi and radii1,2,3. This exercises angular truncation beyond pi; exact distances3,5,4 and the triangle conclusion are exposed.
3. Arbitrary nonnegative outer radii and actual real directions, with middle radius0. The new theorem gives distance<=sum of radii, exercising the apex-middle branch needed by the genuine cone metric.

Final normal combined production-and-test driver exited0 with no diagnostics. Final #lint- only unusedArguments simpNF synTaut was silent, and all four public production/test axiom closures are exactly propext, Classical.choice, Quot.sound. The private point/distance helper is included in the transitive production closure. No admissions or additional axioms were introduced.

This supplies the generic triangle dependency for the actual Option-apex cone constructor. Completeness and association with the actual completed geodesic directions are separately assigned; no claim of their completion is made here. Blueprint207 and the PC migration boundary remain unchanged.

# Genuine Euclidean cone completeness

Temp-only production; no repository mutation/shared build. Four public declarations across two natural leaves, no new mathematical assumptions or definitions:

- `/tmp/gc_ConeDistanceDirectionControl_body.lean`, SHA256 `5c2bd82dd3a70ab494f10717241733042f34c9f35b1fbee8b045fd3636f3c77f`.
  - `Metric.two_mul_radius_mul_min_dist_le_pi_mul_coneDistance`
  - `Metric.dist_lt_of_coneDistance_lt`
  - `Metric.cauchySeq_directions_of_coneDistance_cauchy`
  Minimal imports: existing `DifferentialGeometry.Geometry.Metric.ConeDistance`; `Mathlib.Topology.MetricSpace.Cauchy`.
- `/tmp/gc_EuclideanConeComplete_body.lean`, SHA256 `be78e55cc61adfcc067604666c8bf9eb5f694698112d8a2444f9a2fdacfebd50`.
  - instance `Metric.EuclideanCone.completeSpace`.
  Natural imports: new EuclideanCone and new ConeDistanceDirectionControl. No other geometry/smooth dependency.

## Source checked and mathematical scope

Actual archived AKP, *Alexandrov geometry: foundations*, Section6E printed/PDF67–68, full metric-cone definition and the statement identifying completion of the geodesic-direction cone with the cone of completed directions. Archived PDF SHA256 `1ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed`; actual text `/tmp/gc125_assessment/AlexanderKapovitchPetrunin303Alexandrov.txt` lines2650–2704. Also freshly read the actual gluing proof printed/PDF128, lines5290–5320, which explicitly asserts completeness of Cone A from the cone-distance formula when A is complete. That occurrence is within a CAT gluing application, but the elementary completeness argument here uses only the metric formula and completeness of the base, with no CAT/length hypothesis imported.

The quantitative inverse bound is an elementary formal proof from the source cosine law and Mathlib's Jordan inequality `Real.mul_le_sin`, not a numerical estimate quoted from AKP. It is valid for any pseudometric base: radii at least ρ≥0 give
`2ρ min(π,dY) ≤ π coneDistance`.
Its proof uses the exact half-angle expansion, `(r−s)^2≥0`, the product lower bound `rs≥ρ²`, and `θ/π≤sin(θ/2)` on[0,π]. The cutoff must remain for arbitrary unbounded base distances. With ρ>0 and ε≤π, a sufficiently small actual cone distance yields dY<ε. Applying this with ε capped atπ yields the actual Cauchy-directions result, including any finite prefix outside the positive-radius tail.

Existing scalar source `DifferentialGeometry/Geometry/Metric/ConeDistance.lean` SHA256 `330f7cad296ca2270d0775d8647e8a5423ca8b9a92f92b40b4da2def15c119b2`, last change `dd7efd87644369082f05d2a24f8a31715261caa2`, was read in full and reused unchanged with root authorization. No broader smooth/PC adapter is involved. Current generic cone inputs are sibling65's actual scalar triangle body SHA256 `507fe5cb217f94463a96853e5b5902a0ac3f7cf8b73c4579af59bb6bb2fdc3b9` and siblinghalf's genuine Option cone body SHA256 `35f376c6d51931577dae6d9c1a9cf1222482775a3e032fcfe216b28d2eed1c96`.

Retained source/author-errata distinctions from the earlier cone/direction audit are reused; no fresh remote identity claim. The Option constructor's explicit convention Cone(empty)={tip} is retained. The literal empty product quotient in the displayed AKP formula would otherwise be empty; the singleton pointed extension is explicit rather than attributed to that set-theoretic formula.

## Completeness proof

For any CompleteSpace metric base Y, every actual cone Cauchy sequence has Cauchy radii by the distance lower bound. Radius limit0 gives convergence to the actual tip without selecting any direction. If the limiting radius is positive, an actual positive-radius term supplies a local fallback direction, proving local Nonempty Y from the sequence itself. Every original sequence element, including any early tip terms, is reconstructed exactly as mk(radius,direction). Its directions are Cauchy by the preceding scalar estimate, so base completeness gives an actual direction limit. Continuity of the unchanged scalar cone-distance formula gives convergence of the original same sequence to mk(limit radius,limit direction). No global Nonempty Y, diameter bound, compactness/properness, geodesicity, or curvature assumption enters.

## Compiler, lint, axioms and independent review

Combined minimal production driver `/tmp/gc_EuclideanConeComplete_agent.lean` SHA256 `17065d10184c8ed45e7af07d4ed71d24f38f63e6821f880a44eacad41b28ef5b` imports only existing ConeDistance, PiL2, LinearCombination, and MetricSpace.Cauchy, then concatenates the frozen new bodies. Separate selected-lint driver `/tmp/gc_EuclideanConeComplete_lint.lean` SHA256 `038ced32e9e151025d1b05b331ceb696f3a867f7115190e231dbd802339adaa7` exited0, no unusedArguments/simpNF/synTaut findings, and all4 new public declarations have exactly propext/Classical.choice/Quot.sound.

Root and siblinghalf independently read the complete four-declaration proof chain and reported no findings, specifically checking the positive-tail local inhabitant construction, exact reconstruction, cutoff removal only belowπ, and empty-base branch.

## Frozen eight-test suite

`/tmp/gc_euclidean_cone_completeness_review_body.lean`, SHA256 `5ce6716125ecbbd6fc942290f3a5e801d16625b3995d0ab0e54fcdf05a957b41`.
Combined minimal test driver `/tmp/gc_euclidean_cone_completeness_review_agent.lean`, SHA256 `44446a87ff89344d5effdb6cbce6af6bb57269cb947ed8f74b19f83ba085a372`, actual compiler exit0, silent selected lint, all8 public tests standard3.

Tests prove: exact saturated inverse bound for actual base real distanceπ+1; failure of the tempting uncapped global bound; inverse bound at arbitrary positive radius; explicit application of the NEW completeSpace instance to Empty and ℝ; every empty-base cone element equals tip; collapse to tip for completely arbitrary direction sequences (no direction convergence premise); and an actual positive-radius sequence converging to mk(1,0) with both radius and direction varying. Together these exercise the cutoff, positive-radius branch, zero-radius branch, unbounded base, and empty base.

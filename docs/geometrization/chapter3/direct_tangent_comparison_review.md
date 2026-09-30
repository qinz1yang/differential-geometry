# Direct tangent comparison acceptance

Four public theorems and two private proof helpers in four new leaves. The 499-module shared gate checks 2,304 owned declarations in 3,337 jobs. Its observed increment is 7 owned declarations, comprising four public theorems, two private helpers and 1 compiler-generated declarations. Four new concrete regressions and eight canonical-import standard-axiom reports pass, with silent selected lint. The separate blueprint static audit completed with failure (exit 1); no static pass is claimed. Its actual failure log and recorded status are retained in the receipt.

All owned transitive axioms are restricted to propext, Classical.choice and Quot.sound. The eight explicit reports cover four public production theorems and four new tests. Two inherited geometry fixtures occur once and are not counted as new regressions. Owned/generated increments are observed from the shared gate relative to verified milestone141. No definition, instance, admission or mathematical axiom is added; earlier leaves are unchanged.

The inherited AreaUpperBarrier warning remains outside these owned axiom closures.

Arbitrary original local metric comparison yields zero-curvature comparison on the SAME literal tangent and local spherical comparison on the SAME completed directions. The actual path-domain guards, six simultaneous distance limits, zero-speed and empty-direction cases are retained. No completeness, near-short curves, finite dimension, compactness or properness premise is supplied. Geodesicity, GH convergence and global spherical comparison remain separate; source and migration boundaries are explicit.

# Direct comparison on the actual tangent cone — production/source record (142)

Author: ac65_same_lines. Temporary proof production is complete. This record does not claim canonical registration, a shared build, regression execution by the author, a push, or final repository acceptance.

## Source and precise mathematical scope

Reopened the archived Kapovitch–Lebedeva–Petrunin, Lectures on Alexandrov spaces with curvature bounded below, v1 July 14, 2026, PDF SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`. The directions/cone definitions are printed 35–36 / PDF 37–38. Proposition 3.3 is printed 36 / PDF 38 and its entire proof printed 37 / PDF 39; the exact text in `/tmp/gc140/KLP.txt` was reopened at lines 1575–1615. The source first reduces to the dense cone of original geodesic directions, realizes four vectors at small common time on the original paths, uses the first-order pair-distance formula, rescales curvature by the time squared, and passes to zero-curvature comparison. The implemented proof follows these steps on the literal accepted quotient/completion and cone metric.

The source explicitly warns that a tangent cone can fail to be geodesic, so it need not be Alex(0) under the book's definition. Proposition 3.4's compact-direction pointed-GH statement is separate, as are the finite-dimensional proper/geodesic conclusions of Exercise 6.20(a), printed 69 / PDF 71. This suite proves ONLY the literal nonnegative four-point comparison inequality. It introduces no geodesicity, properness, compactness, GH convergence, source completeness, short-curve or Hausdorff-dimension premise or conclusion. Existing finite-dimensional tangent geometry is unchanged.

The original source theorem is stated for an Alexandrov space; inspecting its proof shows it uses only actual local four-point comparison and the associated actual geodesic-angle limits at the chosen point. Our natural primary statement exposes exactly these sufficient local metric hypotheses and derives HasAnglesAt internally from the accepted producer. The model convention is κ≥0 for geometric lower bound −κ; no positive-model adapter is asserted. No fresh external errata check is claimed. The prior feasibility/source/API record is `/tmp/gc_DirectTangentComparison_feasibility_audit.md` (SHA256 `8f4e6ed352c172bf70e4f60ff54d08e5908b808a8658cb3c600099f137e06caf`).

## Public inventory and canonical homes

1. `DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison.closure_zero`, proposed `Geometry/Comparison/FourPointClosure.lean`. For any metric space and subset s, actual fourPointComparison 0 s implies the same comparison on closure s. Imports Comparison.FourPoint and Mathlib.Topology.Sequences. One public theorem, no private declarations.
2. `Metric.TangentCone.dense_representative_vectors`, proposed `Geometry/Metric/TangentConeDensity.lean`. For the actual HasAnglesAt q, the union of the actual tip and the range of `(r,σ) ↦ σ.tangentVector r` is dense in the SAME actual TangentCone q. Imports Metric.TangentCone and Metric.EuclideanConeProper; the latter's continuous_mk is generic and has no compactness hypothesis. One public theorem, no private declarations.
3. `DifferentialGeometry.Geometry.Comparison.Toponogov.tangentCone_fourPointComparison_zero_of_local_fourPointComparison`, proposed `Geometry/Comparison/TangentComparison.lean`. Inputs are only MetricSpace X, κ≥0, open Ω, actual fourPointComparison κ Ω and q∈Ω. The conclusion derives the accepted HasAnglesAt q with letI and asserts fourPointComparison 0 univ on the SAME TangentCone q. Intended canonical imports: Comparison.FourPointClosure, Metric.TangentConeDensity, Comparison.LocalGeodesicDirections, Comparison.GermDistanceAsymptotic. One public theorem and two private proof helpers.

Exactly three public theorems, two private theorems, no new definitions, structures, instances, axioms, resource overrides, admissions or comments in the production bodies. Each leaf explicitly carries its scopes/opens and `autoImplicit false` setting. Existing source definitions, theorem bodies and PC interfaces are unchanged.

## Proof/dependency audit

The generic closure theorem chooses four sequences in the original subset. It uses only the three center-arm inequalities required by the definition; positive limiting center-arm distances give eventual actual nonzero arms. The other three points may coincide. Three accepted scalar comparison-angle limits at constant curvature zero give the closed inequality. No global continuity at a zero center arm is assumed.

Cone density uses actual completed-direction density and the accepted continuous radial constructor at fixed radius. The tip is included explicitly, so the empty original direction space is covered without selecting a nonexistent representative. It does not identify the cone with an unrelated completion or target.

The first private tangent helper puts each fixed original clamped representative path at radial speed r≥0 inside the same original Ω for all sufficiently small positive times. Original length positivity and the exact radial identity justify this, including r=0.

The second private helper proves comparison for four actual representative vectors of arbitrary nonnegative radii. It invokes `GeodesicRepresentative.dist_div_tendsto_tangentVector` for every needed pair, which already covers zero speeds. Positive limiting center-arm distances imply genuine distinct original source points eventually. The original local four-point inequality is rewritten by `comparisonAngleNegCurvature_mul_scale`, with parameter κt² and original distances divided by t. The accepted `tendsto_comparisonAngleNegCurvature_zero` and `le_of_tendsto` finish; there is no duplicated pair-distance-asymptotic proof or GH lifting premise.

For the headline, if there is an actual representative, the actual tip is its zero vector, so the union-density theorem gives density of the same range and the closure theorem finishes. If no representative exists, the accepted actual completed direction space is empty and its Option cone is a singleton; no forbidden configuration exists. This is the exact empty-direction convention, not an extra nonemptiness assumption.

All public hypotheses are used and natural. Root read the full closure/density proofs and approved their scope before final freeze. Final independent review of the whole headline and original-input regressions is delegated by root and is not claimed in this author record.

## Compiler and axiom evidence

All commands are `lake env lean` on `/tmp` drivers from GC_CHAPTER3_435_RC3, at normal default Lean limits and without repository/shared build mutation. Final combined normal driver `/tmp/gc_TangentComparison_agent.lean`: actual session 80978 exited 0; log is empty. Final selected lint/axiom driver `/tmp/gc_TangentComparison_lint.lean`: actual session 35677 exited 0; no lint or other diagnostics, and exactly three axiom reports, each `[propext, Classical.choice, Quot.sound]`. The selected checks are unusedArguments, simpNF and synTaut.

Separate minimal first-two leaf drivers are included in the production freeze with actual exit status and log hashes. The combined driver expands exactly the three proposed new leaves over accepted imports; it is not a claim that canonical new-module imports have already been registered. The production freeze binds final exact file bytes. Earlier compiler repairs concerned explicit path-parameter elaboration, the actual division positivity theorem name, and proof-local let syntax; no public contract changed.

Root owns later original-input regression verification, repository registration/gates and publication. The source warning about nongeodesic tangent spaces remains explicit.


# Bounded feasibility audit: direct nonnegative comparison on the actual tangent cone (142)

Reviewer: ac65_same_lines. Verdict: mathematically sound, source-matched and implementation-ready. This is a source/API/proof-route audit only; no new Lean theorem has been written or compiled and no repository file changed.

## Exact source

The archived Kapovitch–Lebedeva–Petrunin *Lectures on Alexandrov spaces with curvature bounded below*, v1 July14,2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`, full directions/cone definitions and Proposition3.3 with its complete proof, printed35–37 / PDF37–39, were reopened in `/tmp/gc140/KLP.txt`, especially the displayed scaling formula and all of the paragraph following it. Proposition3.3 starts on printed36/PDF38; its proof is printed37/PDF39. The proof first uses density of actual geodesic directions in their completion, then takes FOUR original geodesics with prescribed radial speeds, applies original four-point comparison to their small-time points, rescales curvature by epsilon², and takes the pair-distance limits. This is exactly the proposed route.

The source explicitly says a tangent space can fail to be geodesic (Halbeisen example), and hence need not be an Alex(0) SPACE under its definition despite having nonnegative Alexandrov comparison. Proposition3.4’s compact-direction/GH premise is separate. Exercise6.20(a), printed69/PDF71, adds finite dimension to obtain proper Alex(0); its cited proof uses3.2,3.3,6.5. The later π-geodesicity and length-space questions were also reopened (5.22 printed59/PDF61 and remarks after6.20). Thus the correct new headline is the literal four-point inequality, NOT geodesicity, properness, compact directions, GH convergence, or the full finite-dimensional tangent-geometry package.

No fresh external errata retrieval is asserted. Existing archived/pinned-author-source distinctions remain intact.

## Minimal natural source-facing statement

For ANY ambient metric X, a point q, a nonnegative comparison parameter κ, an open Ω containing q and actual `fourPointComparison κ Ω`, derive the usual `HasAnglesAt q` by the accepted local producer and prove

```
letI : HasAnglesAt q := hasAnglesAt_of_local_fourPointComparison hκ hΩ hcomp hq
fourPointComparison 0 (Set.univ : Set (Metric.TangentCone q))
```

A generic working core may expose `[HasAnglesAt q]` with the same actual local comparison inputs, so it preserves an already chosen actual direction/tangent carrier. The source-facing version need not require a redundant angle instance. Since the angle class is propositional and the actual metric is the accepted quotient/completion/cone metric, this does not introduce a replacement target.

No `CompleteSpace X`, global near-short curves, global/local length-space premise, source local compactness, dimension upper bound, `CompactSpace (SpaceOfDirections q)`, or `ProperSpace (TangentCone q)` is necessary. The proof uses only those original unit-speed representatives that actually exist; an empty representative/direction space gives the existing singleton-tip cone. The source’s arbitrary curvature statement is implemented in the existing nonpositive-model convention κ≥0 (geometric lower bound−κ); no positive-curvature model adapter is silently added.

Proposed home: a new `Geometry.Metric.TangentComparison` or `Geometry.Comparison.TangentComparison` leaf (root chooses naming), leaving accepted `Metric.TangentGeometry` and `FiniteDimensionalTangentGeometry` unchanged.

## Accepted bodies inspected and exact available APIs

- `Geometry.Metric.TangentGeometry`: currently obtains comparison0 AND actual segments using compact directions, full pointedGH convergence, rescaled source length and `ComparisonLimit`. This is a sufficient stronger-hypothesis route, not evidence those hypotheses are necessary for the comparison component.
- `Comparison.FiniteDimensionalTangentGeometry`: adds original finite-dimensional geometry to derive that compactness/properness/GH package. Its SAME-target scope should remain unchanged.
- `Metric.TangentCone`: `GeodesicRepresentative.dist_div_tendsto_tangentVector σ τ r s` gives the actual rescaled pair-distance limit for ANY NNReal speeds, including zero, with only actual `HasAnglesAt`. `dist_tangentVector` is the exact accepted capped-cosine metric formula; `tangentVector_shorten` preserves the original direction.
- `Metric.GeodesicRepresentative`: positive length, actual isometric Icc curve, original start, clamped all-real path, `path_zero`, `dist_path`, `dist_base_path` supply the finite-domain/radial controls. No artificial global-ray realization is needed.
- `Comparison.GermDistanceAsymptotic`: `comparisonAngleNegCurvature_mul_scale hκ ht` is the exact scalar curvature-rescaling identity, including κ0. No monotonicity or approximate scaling premise is needed.
- `Comparison.ModelAngle`: `tendsto_comparisonAngleNegCurvature_zero` already handles varying nonnegative curvature tending0 and THREE converging scalar sides, needing positive limiting center arms only. Repeated other endpoints or zero opposite sides are allowed.
- `Comparison.RescaledLocalComparison`: the existing eventual rescaled-ball theorem is valid, but a direct finite-quadruple proof can simply use the same scalar identity at real times t↓0; no GH or sequence extraction is needed.
- `Comparison.FourPoint`: the definition only requires the three center arms to be nonzero. It does NOT require the other three points to be pairwise distinct. `fourPointComparison_of_distinct` is optional and unnecessary.
- `Metric.SpaceOfDirections`: `exists_representative_dist_lt` proves density from the ACTUAL quotient/completion; no supplied density record is needed. The global angular bound≤π is already proved. The empty representative and direction instances are explicit.
- `Metric.EuclideanCone` and `EuclideanConeProper`: tip/mk and zero-radius identities handle all degeneracies; `continuous_mk` is GENERIC with only MetricSpace base, despite residing in a file that also proves properness. It has no compactness premise. It combines with direction density to give density of actual representative cone points plus tip.
- `Metric.Approximation.ComparisonLimit`: the last part of its accepted GH proof already demonstrates precisely the scalar three-angle limit and `le_of_tendsto` mechanism. Its GH lift-configuration input should not be imported as a premise for this new proof.

The relevant accepted definitions, full theorem bodies and actual hypotheses were read, not inferred from filenames. A targeted search found no existing public four-point extension-to-dense-set theorem in these inspected comparison/limit/cone leaves; no claim of an exhaustive theorem-name search through unrelated PC sources is made.

## Bounded proof decomposition / missing glue

1. **Finite actual representative cone configurations.** Represent a dense subset by an Option of `(NNReal radius × GeodesicRepresentative q)`, with none mapping to the actual tip and source point q, and some(r,σ) mapping to `σ.tangentVector r` and the original point `σ.path(r*t)`. This is proof-local bookkeeping, not a new conclusion-shaped premise or replacement tangent definition. For every pair, the accepted NNReal fixed-speed limit gives normalized distances. Tip/some cases use the SAME representative at speed0; none/none is the zero constant, so no global nonempty-representative choice is needed.

   For each of the four fixed source paths, eventually r*t lies in its original positive Icc and dist(q,path(r*t))=r*t→0; hence the actual four points lie in the SAME Ω. Positive limiting center-arm distances imply eventually positive normalized source arms, hence genuine distinct source endpoints. Apply actual local comparison there. The exact scaling identity rewrites the original angles using curvature κ*t² and normalized distances. The accepted varying-curvature continuity and `le_of_tendsto` give the comparison inequality for that SAME dense quadruple. This needs finite intersections of eventual statements only, no uniform all-direction estimates.

2. **Dense actual cone subset.** The subset consisting of tip and all actual representative tangent vectors is dense in the literal actual cone. Positive-radius points follow by completed-direction density at that fixed radius and generic continuous_mk. The tip is included explicitly, so the empty-base case is valid. This is an elementary missing API, naturally a small public `TangentCone.dense_representative_vectors` lemma if reuse warrants it, or a private part of the direct proof. No cone-completion identification theorem is necessary.

3. **Four-point closure.** A natural reusable generic helper would state that `fourPointComparison 0 s` plus `Dense s` implies `fourPointComparison 0 univ`. For each arbitrary target quadruple, independently choose sequences in s converging to its four points (metric spaces are first countable). The three target center arms are positive, so the three corresponding approximating arms are eventually positive. Apply the same accepted scalar continuity at constant curvature0 and pass the inequality to the limit. The inequality is NOT globally continuous at zero center arms; the eventual positivity step must be explicit. Alternatively this can stay private inside the tangent proof. No completeness, compactness, separability or dimension is required.

These are finite-configuration/density glue gaps, not new Alexandrov geometry. The scalar limit, actual direction completion and source-path radial identities already exist. A direct diagonal approximation could combine steps1–3, but the two-stage dense-subset proof matches the source and avoids unnecessarily proving uniform convergence in varying representatives.

## Useful non-vacuity checks for a later implementation

- An actual noncomplete open interval with its inherited real metric and original local comparison gives a nontrivial tangent comparison application without `CompleteSpace` being inferable; retain positive original rays and a nonzero tangent point.
- An actual translated plane can exercise non-tip center and three genuinely distinct tangent arms with unequal radii, rather than only the tip-angle bound.
- The singleton/empty-direction case verifies the explicit tip convention, with no fabricated representative.
- An infinite-dimensional Hilbert fixture would be valuable only if its actual four-point comparison is already available naturally; it should not delay this bounded proof or be replaced by an assumed cone-comparison premise.

No implementation has been started pending root’s contract/partition decision.


# Independent full source/proof review: direct actual-tangent comparison (142)

Reviewer source_review. All THREE complete frozen production bodies and both private proof helpers read; verdict PASS. This record is a mathematical/API/source review, not the author’s compiler run. A separately authored original-input regression driver will compile the exact full production snapshot as well.

Source freshly reopened: KLP, Lectures on Alexandrov spaces with curvature bounded below, archived PDF SHA2563dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67, actual direction quotient/completion and cosine-rule cone definitions printed35–36/PDF37–38, Proposition3.3 printed36/PDF38 and its full proof printed37/PDF39. Retained text `/tmp/gc140/KLP.txt` lines1535–1628, SHA25617248a72d6354278fef73d75c4bda9a060a90bf959ea3a28a6fcfde2b2e2509c. The source reduces to actual geodesic directions by density, chooses FOUR original radial-speed geodesics, uses their first-order pair distances, rescales curvature by time squared, and passes to the flat comparison. The proof implemented here follows that route on the literal accepted completed directions and actual cone. Source3.4’s compact-direction/GH conclusion is explicitly separate. KLP states tangents can fail to be geodesic, so nonnegative four-point comparison is not silently called an Alex(0) length space. No new external errata retrieval for KLP is claimed.

`FourPointClosure`: the four chosen sequences stay in the SAME original subset and converge to the supplied four closure points. Exactly the three required nonzero center arms are eventually positive; no continuity at a zero denominator is used. The other anchors may coincide. Constant-zero-curvature scalar comparison limits and the closed inequality yield the exact original predicate. No compactness, completeness, separability or auxiliary net premise is needed.

`TangentConeDensity`: actual representative direction density is used only at fixed radius through the already-proved continuous mk constructor. This continuity theorem has no compactness assumption despite its file’s properness title. The actual tip is included separately. A positive-radius cone point supplies its own actual direction; no representative is chosen in the empty-direction case. No cone-completion isometry/GH identification or fabricated dense subset is assumed.

`TangentComparison`: each fixed original representative at any NNReal speed, including0, eventually lies in the SAME original open neighborhood because its original domain length is positive and its true radial distance is r*t. The four-point proof uses all six actual pair-distance limits from the supplied original paths; the three positive target center distances force genuine source noncentrality at small common positive time. The exact accepted scaling identity changes original parameterκ toκ*t² and distances to distance/t, includingκ0. The positive-side filter, curvature nonnegativity and original-domain eventual statements are explicit. Scalar varying-curvature continuity then gives flat comparison for that SAME dense cone quadruple.

The headline derives HasAnglesAt from the actual local comparison at the SAME original point. If a representative exists, its radius-zero vector is exactly the actual tip, so the proved dense range and closure theorem apply. If no representative exists, the actual completed direction space is empty and the literal Option cone is singleton, making the forbidden noncentral quadruple impossible. There is no global nonempty-direction assumption or arbitrary fallback representative. Proof irrelevance only aligns propositional HasAnglesAt witnesses; no metric/tangent target is changed.

The public hypotheses are only original MetricSpace, κ≥0, one actual open comparison neighborhood and membership of the chosen original point. No CompleteSpace, local compactness, global near-short curves, length-space, finite dimension, compactΣ, properT, or GH convergence enters. κ≥0 denotes geometric lower bound−κ, consistent with the accepted scalar normalization; this is not a new positive-curvature adapter. The proof is a legitimate stronger minimal-hypothesis extraction from KLP3.3’s actual argument. Existing finite-dimensional geometry remains unchanged.

Frozen production files:
- `/tmp/gc_FourPointClosure_body.lean`: `e0d5e58a7451af21efa2d6cc1876ea1e6f73e5b404bfbd57b6eeee65b29ba930`
- `/tmp/gc_TangentConeDensity_body.lean`: `8f3850b644e4d9fb6e29f17a597af9ec20c50c02cc33b3a906971a832f2c9e5c`
- `/tmp/gc_TangentComparison_body.lean`: `6d207a924393c89dde85061560785dffddc20c8e1743f477ef9e82adea0fd344`
- `/tmp/gc_DirectTangentComparison_production_freeze.json`: `bdf97616e47f2778c8216f79033489f15a018073b5407a7450f3ba90bbfc4204`
- `/tmp/gc_DirectTangentComparison_feasibility_audit.md`: `8f4e6ed352c172bf70e4f60ff54d08e5908b808a8658cb3c600099f137e06caf`


# Direct local spherical comparison on actual directions

One public theorem in the new Comparison.DirectSphericalDirections leaf. Canonical imports are Comparison.TangentComparison and Comparison.ConeSphericalComparison. No definition, instance or private helper is added, and all prior mathematical files remain unchanged.

For ANY metric source X, an original open region Ω containingq, a nonnegative parameterκ and actual fourPointComparison κ Ω, the theorem derives the canonical HasAnglesAtq and proves fourPointSphericalComparison on every pi/4 ball in the SAME completed SpaceOfDirectionsq. It imposes no source completeness, near-short-curve or length assumption, dimension upper bound, compactness, properness, supplied tangent comparison, supplied angular model or nonempty-direction premise. The original comparison parameterκ means geometric curvature lower bound−κ; the output is the new positive-unit spherical model convention with its explicit strict2pi guards.

The proof composes the genuinely proved direct tangent four-point theorem with the genuinely proved local cone-to-sphere theorem. The literal TangentConeq is definitionally the accepted EuclideanCone of the same completed actual directions; its canonical HasAnglesAt instance agrees by proof irrelevance. There is no new target or alternative completion. The universal angular-center conclusion manufactures no direction in the empty case.

Sources actually reread: KLP Lectures archivedv1July14,2026, SHA3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67, full3.3 statement/proof and preceding directions/cone definitions, printed35--37/PDF37--39, retained gc140/KLP.txt lines1536--1610. The proof uses a dense subcone of actual geodesic representatives, four simultaneous original paths, exact first-order distances and curvature scalingε². The source expressly distinguishes this nonnegative comparison from geodesicity/full Alex(0); no such extra conclusion is inferred here. AKP archived11.6(a) converse, printed/PDF175, was reread during141: right-triangle lifts give LOCAL spherical comparison before a separate globalization. Its Euclidean secant specialization is the accepted141 proof. The defining6B/model.tex strict2pi convention and missing2 source discrepancy/author-errata distinctions remain in141 records, not silently changed.

This is the source-facing local consequence that removes the extra completeness, finite-dimensionality and near-short-curve hypotheses used by141's first original-source route. It does NOT claim global CBB1, positive-curvature globalization, compact directions, proper tangent, tangent geodesicity, Hausdorff dimension or any smooth/migration result.

Normal source-copy21339 compiled actualexit0 with empty log. It concatenates actual proved142 tangent dependencies and actual proved141 cone-to-sphere dependencies; no placeholder theorem or new axiom is used. Selected lint/axiom evidence is bound by the final freeze. Source_review extends its SAME actual incomplete-open-interval regression with this exact universal spherical conclusion while retaining the independently proved failure of source completeness, original nonzero representative and actual tangent comparison. That test is bound by the142 test freeze rather than duplicated here.

Final selected source-copy lint62958 exited0 with no findings and exactly one report, containing only propext, Classical.choice and Quot.sound. Source_review independently read the entire one-theorem body and passed its exact API/proof before integrating the same incomplete-interval test. No redundant new test fixture or fifth regression is introduced; the final142 suite retains four tests and eight public-production/test reports.


# Independent review of direct local spherical direction comparison

Reviewer source_review. Full proof/API read PASS against `/tmp/gc_DirectSphericalDirections_body.lean` SHA2560a90669591777a226e52ba04f3216d85ccf980565f1b3746d4fece9513bb9a99. No duplicate producer-only compiler run is claimed; the exact body is also elaborated in the separately authored full142 original-input regression driver.

The sole theorem derives the SAME actual HasAnglesAt q from original local fourPointComparisonκ on one open neighborhood, κ≥0 (geometric lower bound−κ). The new direct tangent theorem gives comparison0 on the literal actual TangentCone q, then141’s generic cone theorem proves the exact perimeter-guarded unit-spherical predicate on EVERY pi/4-ball in the SAME completed actual direction space. No target re-selection, additional curvature hypothesis, global length/short-curves/completeness, compactness, properness or dimension premise appears. Empty completed direction spaces retain the legitimate vacuous forallξ without inventing a direction.

The source route combines freshly reread KLP3.3 printed36–37/PDF38–39 (dense actual radial-speed quadruples give tangent comparison only) with AKP11.6(a) conversep/PDF175 (right-triangle cone lifts give LOCAL spherical comparison before separate globalization8.31). Source records `/tmp/gc_DirectTangentComparison_source_independent_read.md` SHA25609fd662b34665194deaf848ee495929cc8d6d84b35c045a3a1988291cf51f2d9 and `/tmp/gc_Post140_frontier_source_assessment.md` SHA2566ae73cca1c8888d9ee599706a470ed5c25c8ae49469c9868ddec1431148f0b3e preserve the exact local/global and2pi-model-perimeter conventions. No global CBB1/geodesicity conclusion is asserted.

The shared incomplete-interval regression invokes this theorem at actual originalκ4 and q0 in(-2,2), alongside a proved failure of CompleteSpace and an original unit representative giving a nonzero tangent vector. It keeps the full∀ξ guarded spherical predicate. Final normal/lint results and test hashes are bound in the separate142 review freeze when finished.


# Independent direct actual tangent comparison and original-input regressions (142)

Author/reviewer source_review. The complete frozen3-leaf direct tangent production plus both private helpers received a full source/proof read PASS, separately recorded at `/tmp/gc_DirectTangentComparison_source_independent_read.md` SHA25609fd662b34665194deaf848ee495929cc8d6d84b35c045a3a1988291cf51f2d9. The additional direct local-spherical consumer received a full read PASS in `/tmp/gc_DirectSphericalDirections_source_independent_read.md` SHA2561777e8e09302a38db2e7fb6a9ff140c852fdebe5fda48a94d06dadf355ca7fea. Source KLP3.3’s entire definitions/proof paragraph was freshly reopened; the nongeodesic-tangent warning and separate compact/GH3.4 statement are retained. Source AKP11.6 motivates only the additional LOCAL spherical comparison; no global positive-curvature conclusion follows here.

Four newly authored tests compile the exact same frozen production bodies. Final test extra SHA2563aadeec2058d680ab5d2cea55c023b0a299a407b4cfd2f216d0536598b272967.

1. Actual incomplete open interval(-2,2) at originalq0. A genuine positive-length unit-speed representative in the inherited interval metric produces an actual tangent vector at distance1 from the tip. Incompleteness is PROVED by the closed-range consequence of hypothetical completeness and the excluded closure endpoint2. Actual local comparison parameter4 comes from the original real metric. The test invokes both the direct literal-tangent four-point theorem and the direct local-spherical theorem, retaining EVERY actual directionξ and the exact pi/4-ball guarded predicate. No CompleteSpace, source curves, dimension or compactness premise is supplied to those applications.
2. Actual translated Euclidean plane with original three rational unit directions and unequal original representative lengths. Four actual tangent vectors have radii1,2,3,4, with the first two on the same original direction and the others on the other two directions. Radius identities prove that ALL four are non-tip and pairwise distinct. The first, non-tip vector is the comparison center. Full tangent comparison AND its exact non-tip cyclic-angle inequality are obtained from the original source local comparison4, not supplied as a hypothesis.
3. Actual singleton/PUnit source with empty completed direction space. Full flat comparison and singleton tangent are retained. The actual tip singleton is dense, while the representative-vector range is empty and NOT dense. This explicitly tests the essential tip-union convention in the generic density theorem, with no invented representative.
4. The closure theorem is applied to original real interval(-1,1), yielding comparison on[-1,1]. The new endpoints−1 and1 are proved absent from the original open set. At center0, anchors−1,1,1 give the exact cyclic sum2pi: repeated anchors and zero opposite side are valid, while the two center arms remain positive. This tests the actual closure extension rather than merely reapplying an already closed input set.

Final independent full normal driver session43598 exited0 with EMPTY log. Final selected lint/axiom driver session40535 exited0, no findings/other diagnostics, and exactlyEIGHT reports (four new production public theorems, four tests), all and only propext/Classical.choice/Quot.sound. This independent full driver also elaborates the two private load-bearing helpers and the141 dependencies; it does not claim a fresh shared canonical build. Resource limits are default, no tactic umbrella or warning suppression. Early test-only repairs were explicit subtype Subsingleton instance selection, real numeral type annotations, normalization and style; no production body/statement was edited.

The uniquely named source-copy generator is `/tmp/gc_make_direct_tangent_comparison_author_review.py`. A later canonical integration generator MUST use its separate `_canonical_review.py` name. Exact imports/body order are bound in the freeze and inputs JSON. Only two unchanged inherited fixtures are included once:
- `/tmp/gc_direction_space_review_body.lean`: `0fbb770f853222b05f6c2f246ecda76620fde276d8311afe242d6df5224111cf`
- `/tmp/gc_plane_direction_packing_review_body.lean`: `da72dffd52a1167361f8d9155ccd1722e5213ab52c2b24790dd20a39f65794a2`

The parent is separately reviewing these four tests before integration; that review is not mislabeled as another compiler run. No repository/reference edits, shared lake builds, migration probes, registration, commit or push were performed by this subtask.


# Independent direct-tangent production and original-input regression read

Reviewer ac57_half_angle. Full-read PASS for ac65's three production leaves, including both private helpers, and source_review's four final tests. The separately authored DirectSphericalDirections consumer is mine, so its independent proof review is attributed to source_review's distinct record, not this author. No duplicate Lean compilation is claimed here.

The closure theorem chooses four sequences in the SAME original set. Its three positive limiting central distances give eventual nonzero source arms on one common tail, exactly the hypotheses required by scalar comparison continuity. Repeated other anchors remain allowed. No unproved continuity at a zero denominator, compactness or completeness is used.

The tangent-density theorem transports genuine representative-direction density at each fixed radius through the actual continuous cone constructor. It includes the actual tip separately, which is essential when there is no representative. The direct tangent proof keeps all four original representatives and NNReal speeds, including zero. It proves that every original path evaluation lies in the original open neighborhood eventually, simultaneously with all three source noncentrality bounds obtained from positive limiting tangent distances. The same six pairwise limits and exact curvature scaling produce zero-curvature comparison on this actual dense subcone. Its closure is the SAME literal tangent. The no-representative case uses actual empty completed directions and the singleton Option cone, with no fallback direction.

The incomplete interval test is substantive: X is the actual open real interval(-2,2), and its failure of CompleteSpace is independently proved from the missing endpoint2 in its closure. The actual original representative t↦t has length1 and its actual tangent vector has radius/distance1. Actual inherited real comparison atκ4 gives both the whole-tangent CBB0 conclusion and the new universal local spherical conclusion, without supplying compactness, finite dimension, completeness or those desired conclusions.

The singleton test retains actual empty directions, actual singleton tangent and tip density, and explicitly disproves density of the representative-vector range alone. The closure test adds BOTH original boundary points±1 and evaluates a repeated-anchor cyclic sum exactly2pi, testing the noncentral-only guard. The plane test uses genuine original representatives at four unequal radii1,2,3,4; radius identities imply injectivity/non-tip status. It applies the new tangent comparison to a quadruple whose center is the first NON-TIP vector, and returns the actual cyclic inequality. This is not only a tip-angle test.

Sources independently reread: full KLP3.3 and preceding actual quotient/completion/cosine-rule cone definitions, printed35--37/PDF37--39, retained gc140/KLP.txt lines1536--1610, archiveSHA3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67. The source explicitly distinguishes tangent nonnegative comparison from geodesicity/full Alex(0). AKP11.6(a)'s converse and separate globalization qualification apply to the direct spherical consumer through141. No stronger conclusion or new erratum is inferred.

Frozen mathematical bodies: FourPointClosure e0d5e58a7451af21efa2d6cc1876ea1e6f73e5b404bfbd57b6eeee65b29ba930; TangentConeDensity 8f3850b644e4d9fb6e29f17a597af9ec20c50c02cc33b3a906971a832f2c9e5c; TangentComparison 6d207a924393c89dde85061560785dffddc20c8e1743f477ef9e82adea0fd344. Exact final test hash/compiler evidence is bound by gc_DirectTangentComparison_review_freeze.json SHA464806fa63529d4e77d3ccc1e04cc379db0414581aaa6d51c7cf043a0758635e (normal43598 and eight-report selectedlint40535 both actual0/clean). No mathematical files or tests were changed for this review.


```lean
import DifferentialGeometry.Geometry.Comparison.FourPointClosure
import DifferentialGeometry.Geometry.Metric.TangentConeDensity
import DifferentialGeometry.Geometry.Comparison.TangentComparison
import DifferentialGeometry.Geometry.Comparison.DirectSphericalDirections
import DifferentialGeometry.Geometry.Comparison.FourPoint
import Mathlib.Topology.Sequences
import DifferentialGeometry.Geometry.Metric.TangentCone
import DifferentialGeometry.Geometry.Metric.EuclideanConeProper
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.GermDistanceAsymptotic
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import DifferentialGeometry.Geometry.Comparison.ConeSphericalComparison
import Mathlib.Tactic.Linter

open Set Metric Filter Topology Real
open scoped NNReal ENNReal Topology

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

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCDirectionSpaceReview

private abbrev OpenInterval := Ioo (-2 : ℝ) 2

private def openIntervalBase : OpenInterval := ⟨0, by constructor <;> norm_num⟩

private theorem openIntervalComparison : fourPointComparison 4 (univ : Set OpenInterval) := by
  intro x _ a _ b _ c _ hax hbx hcx
  exact real_comparison (by norm_num) x.val (mem_univ _) a.val (mem_univ _)
    b.val (mem_univ _) c.val (mem_univ _)
    (fun h => hax (Subtype.ext h)) (fun h => hbx (Subtype.ext h))
    (fun h => hcx (Subtype.ext h))

private instance : HasAnglesAt openIntervalBase :=
  hasAnglesAt_of_local_fourPointComparison (by norm_num) isOpen_univ
    openIntervalComparison (mem_univ _)

private def openIntervalRep : GeodesicRepresentative openIntervalBase where
  length := 1
  length_pos := zero_lt_one
  curve := fun t => ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  isometry := Isometry.of_dist_eq fun _ _ => rfl
  start := rfl

theorem actual_noncomplete_interval_nonzero_tangent_comparison :
    ¬CompleteSpace OpenInterval ∧
    dist (openIntervalRep.tangentVector 1) EuclideanCone.tip = 1 ∧
    fourPointComparison 0 (univ : Set (TangentCone openIntervalBase)) ∧
    ∀ ξ : SpaceOfDirections openIntervalBase,
      fourPointSphericalComparison (ball ξ (Real.pi / 4)) := by
  refine ⟨?_, by simp [GeodesicRepresentative.tangentVector], ?_, ?_⟩
  · intro h
    let := h
    have hi : Isometry (Subtype.val : OpenInterval → ℝ) := isometry_subtype_coe
    have hc : IsClosed (Ioo (-2 : ℝ) 2) := by
      simpa only [Subtype.range_val] using hi.isUniformInducing.isComplete_range.isClosed
    have h2 : (2 : ℝ) ∈ closure (Ioo (-2 : ℝ) 2) := by
      rw [closure_Ioo (by norm_num)]
      constructor <;> norm_num
    rw [hc.closure_eq] at h2
    exact (lt_irrefl (2 : ℝ)) h2.2
  · exact tangentCone_fourPointComparison_zero_of_local_fourPointComparison
      (by norm_num) isOpen_univ openIntervalComparison (mem_univ openIntervalBase)
  · exact spherical_direction_comparison_of_local_fourPointComparison
      (by norm_num) isOpen_univ openIntervalComparison (mem_univ openIntervalBase)

theorem actual_singleton_empty_directions_tip_density_and_comparison :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    Subsingleton (TangentCone (PUnit.unit : PUnit.{1})) ∧
    fourPointComparison 0 (univ : Set (TangentCone (PUnit.unit : PUnit.{1}))) ∧
    Dense ({EuclideanCone.tip} : Set (TangentCone (PUnit.unit : PUnit.{1}))) ∧
    ¬Dense (Set.range (fun z : ℝ≥0 × GeodesicRepresentative (PUnit.unit : PUnit.{1}) =>
      z.2.tangentVector z.1)) := by
  have he : Set.range (fun z : ℝ≥0 × GeodesicRepresentative (PUnit.unit : PUnit.{1}) =>
      z.2.tangentVector z.1) = ∅ := by
    ext x
    simp only [mem_range, mem_empty_iff_false, iff_false]
    rintro ⟨z, _⟩
    exact isEmptyElim z.2
  refine ⟨inferInstance,
    inferInstanceAs (Subsingleton (Option ({r : ℝ // 0 < r} ×
      SpaceOfDirections (PUnit.unit : PUnit.{1})))), ?_, ?_, ?_⟩
  · have hcomp : fourPointComparison 4 (univ : Set PUnit.{1}) := by
      intro p _ a _ _ _ _ _ hap
      exact (hap (Subsingleton.elim _ _)).elim
    exact tangentCone_fourPointComparison_zero_of_local_fourPointComparison
      (by norm_num) isOpen_univ hcomp (mem_univ PUnit.unit)
  · have h := TangentCone.dense_representative_vectors (q := (PUnit.unit : PUnit.{1}))
    simpa only [he, union_empty] using h
  · rw [he]
    intro hd
    have h := hd (EuclideanCone.tip : TangentCone (PUnit.unit : PUnit.{1}))
    simp only [closure_empty, mem_empty_iff_false] at h

theorem closure_adds_boundary_with_repeated_anchors :
    (-1 : ℝ) ∉ Ioo (-1) 1 ∧ (1 : ℝ) ∉ Ioo (-1) 1 ∧
    fourPointComparison 0 (Icc (-1 : ℝ) 1) ∧
    comparisonAngleNegCurvature 0 (dist (0 : ℝ) (-1)) (dist (0 : ℝ) 1) (dist (-1 : ℝ) 1) +
      comparisonAngleNegCurvature 0 (dist (0 : ℝ) 1) (dist (0 : ℝ) 1) (dist (1 : ℝ) 1) +
      comparisonAngleNegCurvature 0 (dist (0 : ℝ) 1) (dist (0 : ℝ) (-1)) (dist (1 : ℝ) (-1)) =
      2 * Real.pi := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · have h := ((real_comparison (by norm_num : (0 : ℝ) ≤ 0)).mono
      (subset_univ (Ioo (-1 : ℝ) 1))).closure_zero
    simpa only [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using h
  · norm_num only [Real.dist_eq, sub_neg_eq_add, zero_add, zero_sub, abs_neg,
      abs_one, neg_sub, sub_self, abs_zero, comparisonAngleNegCurvature_zero]
    have hadd : comparisonAngle 1 1 2 = Real.pi := by
      convert comparisonAngle_add (a := (1 : ℝ)) (b := 1) zero_lt_one zero_lt_one using 1
      norm_num
    have hself : comparisonAngle 1 1 0 = 0 := by
      simpa only [sub_self, abs_zero] using comparisonAngle_abs_sub zero_lt_one zero_lt_one
    norm_num [hadd, hself]
    ring

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

private def tangentQuadruple : Fin 4 → TangentCone base :=
  ![(representative 0).tangentVector 1, (representative 0).tangentVector 2,
    (representative 1).tangentVector 3, (representative 2).tangentVector 4]

private theorem tangentQuadruple_radius (i : Fin 4) :
    EuclideanCone.radius (tangentQuadruple i) = (i.val : ℝ) + 1 := by
  fin_cases i <;> norm_num [tangentQuadruple, GeodesicRepresentative.tangentVector]

theorem actual_translated_plane_non_tip_quadruple_comparison :
    (∀ i : Fin 4, EuclideanCone.radius (tangentQuadruple i) = (i.val : ℝ) + 1) ∧
    (∀ i : Fin 4, tangentQuadruple i ≠ EuclideanCone.tip) ∧
    Function.Injective tangentQuadruple ∧
    fourPointComparison 0 (univ : Set (TangentCone base)) ∧
    comparisonAngleNegCurvature 0
        (dist (tangentQuadruple 0) (tangentQuadruple 1))
        (dist (tangentQuadruple 0) (tangentQuadruple 2))
        (dist (tangentQuadruple 1) (tangentQuadruple 2)) +
      comparisonAngleNegCurvature 0
        (dist (tangentQuadruple 0) (tangentQuadruple 2))
        (dist (tangentQuadruple 0) (tangentQuadruple 3))
        (dist (tangentQuadruple 2) (tangentQuadruple 3)) +
      comparisonAngleNegCurvature 0
        (dist (tangentQuadruple 0) (tangentQuadruple 3))
        (dist (tangentQuadruple 0) (tangentQuadruple 1))
        (dist (tangentQuadruple 3) (tangentQuadruple 1)) ≤ 2 * Real.pi := by
  have hi : Function.Injective tangentQuadruple := by
    intro i j hij
    have hr := congrArg EuclideanCone.radius hij
    rw [tangentQuadruple_radius, tangentQuadruple_radius] at hr
    apply Fin.ext
    exact_mod_cast (add_right_cancel hr)
  have hcomp : fourPointComparison 0 (univ : Set (TangentCone base)) :=
    tangentCone_fourPointComparison_zero_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 4) isOpen_univ
      (inner_comparison.of_zero (by norm_num)) (mem_univ base)
  refine ⟨tangentQuadruple_radius, ?_, hi, hcomp, ?_⟩
  · intro i he
    have h := congrArg EuclideanCone.radius he
    rw [tangentQuadruple_radius, EuclideanCone.radius_tip] at h
    have hnonneg : (0 : ℝ) ≤ i.val := by positivity
    linarith
  · exact hcomp _ (mem_univ _) _ (mem_univ _) _ (mem_univ _) _ (mem_univ _)
      (fun h => (by decide : (1 : Fin 4) ≠ 0) (hi h))
      (fun h => (by decide : (2 : Fin 4) ≠ 0) (hi h))
      (fun h => (by decide : (3 : Fin 4) ≠ 0) (hi h))

end GCPlaneDirectionPackingReview

#lint- only unusedArguments simpNF synTaut
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison.closure_zero
#print axioms Metric.TangentCone.dense_representative_vectors
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.tangentCone_fourPointComparison_zero_of_local_fourPointComparison
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.spherical_direction_comparison_of_local_fourPointComparison
#print axioms GCDirectionSpaceReview.actual_noncomplete_interval_nonzero_tangent_comparison
#print axioms GCDirectionSpaceReview.actual_singleton_empty_directions_tip_density_and_comparison
#print axioms GCDirectionSpaceReview.closure_adds_boundary_with_repeated_anchors
#print axioms GCPlaneDirectionPackingReview.actual_translated_plane_non_tip_quadruple_comparison
```

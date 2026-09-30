# Finite actual-tangent linear dimension acceptance

One definition and six public theorems in four new leaves. The 479-module shared gate checks 2,242 owned declarations in 3,317 jobs. Its observed increment is 10 owned declarations, comprising 6 public theorems, 1 definition and 3 compiler-generated declarations. 9 new concrete regressions and 16 canonical-import standard-axiom reports pass, with silent selected lint. The separate blueprint static audit remains pending; no static pass is claimed. Its recorded status and latest completed failure are retained in the receipt.

Every owned transitive axiom closure is restricted to propext, Classical.choice and Quot.sound. Sixteen explicit reports cover the definition, six theorems and nine new tests. Every frozen fixture occurs once. The generated increment is OBSERVED relative to accepted milestone136, never forecast. No instance, private production helper, admission or mathematical axiom is added; earlier mathematical leaves are unchanged. No full migrated-root, PDF, Overleaf or human-approval claim is made.

The inherited AreaUpperBarrier warning remains outside these owned axiom closures.

The actual tangent metric-embedding rank supremum equals the original source Hausdorff dimension under complete metric geometry, actual near-short endpoint curves, a finite natural global upper bound and local comparison1 everywhere. For nonempty sources ONE m retains global and all nonempty open-region Hausdorff dimension and is the greatest realized rank for BOTH arbitrary metric Euclidean embeddings and pointed dilation-respecting embeddings into actual tangents. The same regular point and same inverse pointed onto tangent isometry attain both. The generic polarization proof supplies the actual nonnegative-dilation identity.

The source distinction is explicit: KLP6A uses metric subspaces, AKP7.9 requires cone multiplication. Only their finite maxima are identified; arbitrary unpointed embeddings are not declared conical. Empty has supremum0 but no greatest realized rank, whereas singleton has attained rank0. Tests cover actual real and plane inputs with loose bounds, all-point/all-map rank bounds, the non-onto halfline, a translated-isometry negative control, the actual real tangent and empty cones. No TopDim, infinite-dimensional converse, every-point regularity, linear dimension of an arbitrary noncomplete open subtype, smooth migration result or full chapter completion is asserted.

# Finite actual-tangent linear dimension: source and API assessment

## Checked source passages and identities

Reopened actual cached KLP Lecture6A definition and6.1-6.6 (printed61-64/PDF63-66), full6.18-6.20 statement/proof (printed69/PDF71) and corresponding semisolutions137-138/PDF139-140. KLP6A defines LinDim as the least upper bound of integers k for which Euclidean E^k is isometric to a subspace of the ACTUAL tangent at some original point. It does not explicitly require that embedding to pass through the cone tip or commute with cone multiplication. The archived PDF is the retained July14,2026 v1, SHA2563dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67; the separately checked extracted text `/tmp/gc140/KLP.txt` has SHA25617248a72d6354278fef73d75c4bda9a060a90bf959ea3a28a6fcfde2b2e2509c, definition lines2565-2573, theorem lines2933-2958, semisolution lines5793-5804. These are distinct artifact hashes.

Reopened archived AKP303 Chapter7B, Definition7.9 (printed/PDF77), including preceding definition of a cone map as a map respecting cone multiplication; also15.6 proof(C=>D), printed/PDF233, where the distance-preserving CONE embedding is used at an actual nearby point. Its definition requires an isometric cone embedding E^k into the actual tangent. PDF SHA2561ba6f6f011a8333d9a20bdbf49d36d68b61bf1aababb19296ed48ecea37248ed; text `/tmp/gc125_assessment/AlexanderKapovitchPetrunin303Alexandrov.txt` SHA256b35855859caa7cabb1e36f57b0712ae96b94866ab3d316771cc0c7325df0d812, definition lines3019-3034, application9833-9841. The pinned AKP TeX snapshot ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 is a distinct source; no uninspected corresponding TeX definition or current repository content is claimed.

Applicable retained correction/source distinctions are unchanged from `/tmp/gc_Post135_frontier_source_assessment.md`: in particular the BBI394 line-10 opposite-pair correction belongs to the dense-frame proof now established, not a new modification of either LinDim definition. No newly retrieved errata or external source is claimed. This is targeted reuse plus fresh reading of the listed exact passages.

## Achievable natural finite suite

Use the ACTUAL existing TangentCone p = EuclideanCone(SpaceOfDirections p), with the original HasAnglesAt family. A natural `Metric.linearDimension X` is the ENNReal supremum over original points p, natural ranks k and actual isometric maps EuclideanSpace(R,Fin k)->TangentCone p, of k. This is precisely the KLP metric-subspace convention, using ENNReal to embed Nat union infinity and align with existing Hausdorff dimension. The supremum of an empty family is0; the empty-source case is an explicitly stated extension, not a false attained witness. No same-named owned or pinned Mathlib API was found. Proposed topic home: Geometry.Metric.TangentLinearDimension.

Under the original complete metric source, actual near-short continuous curves, finite natural upper bound dimH(univ)<=n, and ambient local comparison1 EVERYWHERE, the new dense pointed-Euclidean tangent theorem and accepted all-point tangent dimension equality give linearDimensionX=dimH(univ). No TopDim or infinite-dimensional converse is claimed. The theorem derives HasAnglesAt from the original local geometry. It does not redefine the source dimension or use linear dimension as an earlier chart premise.

A separate strongest finite-rank theorem under Nonempty X can retain ONE m<=n, actual dimH(univ)=m and ALL nonempty open V dimension=m, and prove IsGreatest of BOTH realized-rank sets at m: (i) arbitrary metric isometric embeddings E^k->TangentCone p; (ii) pointed isometric embeddings respecting nonnegative cone dilation. The latter is the exact AKP7.9 convention. For Empty X both realized-rank sets are empty, so IsGreatest is false even at0; retain the nonempty hypothesis. Merely defining their suprema0 causes no issue. There is no need to prove every unpointed KLP embedding is itself conical, nor a general equivalence for arbitrary spaces with defined angles.

Upper bound: for ANY original p and ANY isometric map f:E^k->TangentCone p, use Isometry.dimH_image and monotonicity into the whole SAME tangent, Real.dimH_univ_eq_finrank and finrank_euclideanSpace_fin, then actual dimH(TangentCone p)=m. This does not need f(0)=tip or surjectivity.

Attainment: in a nonempty source the ONE dense G-delta of regular points is nonempty. Choose its actual p and the supplied pointed ONTO isometry e:TangentCone p~=E^m; e.symm is an isometric embedding of rank m. The generic dilation lemma below makes e.symm a genuine cone map, proving the AKP maximum at the SAME p and rank. Quantifier order is one m before all p/k/maps. Empty and singleton remain separate: singleton has E^0 realized at its actual point.

## Highest-risk compatibility bridge and implementation spike

A pointed isometry by itself is a metric map. To use the AKP wording one must prove its scaling identity, not silently call it linear or a cone isomorphism. Existing EuclideanCone exposes dilate, radius, exact radial distances, dist_mk and the cosine law; no accepted dilation-preserving isometry theorem was found. Accepted RadialConeData has metric radial uniqueness, but EuclideanCone is not presently exposed through that structure; building a second cone-data interface would be unnecessary here.

The natural bounded bridge is stronger than needed: for ANY metric Y and ANY real inner-product E, an isometric map f:EuclideanCone Y->E satisfying f(tip)=0 obeys f(dilate c x)=(c:Real) smul f(x), for every c:NNReal and every original x. No properness, compactness, angle-diameter bound, finite dimension or onto assumption is needed. Its inverse specialization for pointed isometry equivalences gives exactly e.symm(c smul v)=dilate c(e.symm v). The proof uses actual norm/radius equality and the two radial distances; polarization makes norm(f(dilate c x)-c smul f(x)) squared zero. This also handles c=0, x=tip and empty Y. A translated isometry is a counterexample without tip preservation.

The source-independent elementary metric/inner-product spike compiled normally at default limits in `/tmp/gc_ConeIsometryDilation_source_spike_agent.lean`, actual session37457 exit0/empty log. The final reusable body is being checked with precise two imports and concrete tests; no canonical registration or shared build has occurred. Compiler evidence for final snapshots will be frozen separately. This closes the only nontrivial convention-compatibility step; the finite rank/Hausdorff consumers use standard accepted dimension transport and the newly proved substantive dense-tangent result.

## Scope kept explicit

This finite original-global theorem recovers the LinDim=HausDim portion of KLP6.18 by an alternate already-proved route, not its full TopDim statement or its infinite-dimensional proof. It does not identify the dimension of a tangent cone by assumption, equate arbitrary bi-Lipschitz chart rank with linear dimension, infer regularity from a mere upper bound, or globalize hypotheses given only on one local region. Applying the theorem to a noncomplete open subspace is not automatic; a separate open-subspace direction/tangent identification would be needed to literally bind LinDim(V), whereas the already proved Hausdorff equality for all nonempty open V can be retained unchanged.


# Pointed cone isometries preserve nonnegative dilation

Frozen natural generic API: three public theorems, no private helpers/definitions/instances. Proposed home Geometry.Metric.ConeIsometryDilation. Minimal imports: accepted Metric.EuclideanCone and Mathlib.Analysis.InnerProductSpace.Basic.

`dist_dilate_self` proves the exact same-ray distance |c-1|*radius(x) for all NNReal c and actual cone x, including c=0 and the tip. `map_dilate_of_isometry` proves that ANY isometric map from EuclideanCone Y into ANY real inner-product space E, taking the literal tip to0, obeys f(dilate c x)=c smul f(x). `symm_map_smul_of_isometryEquiv` returns the inverse identity for a pointed isometry equivalence. No compactness, properness, finite dimension, diameter<=pi, nonempty Y or surjectivity is assumed in the main map theorem. The inverse specialization needs the actual equivalence as stated.

The proof reads off norms from distance to the tip and the actual radial distance to x. Real polarization forces the cross inner product to be c*radius(x)^2 and then the squared norm of f(dilate c x)-c smul f(x) is zero. Thus the law is PROVED from the actual metrics; it is not a supplied cone-map assumption or an unproved appeal to uniqueness of a ray. Empty Y is harmless because the literal cone still contains its actual tip.

Source contract: KLP6A printed61/PDF63 defines the realized linear ranks using metric isometric Euclidean subspaces of actual tangents; archived AKP7.9 printed/PDF77 defines a distance-preserving CONE embedding and explicitly defines cone maps by respecting multiplication. The lemma supplies this latter additional condition for the inverse of the pointed onto actual tangent isometry produced by milestone136. Detailed exact source/PDF versus text identities and finite-suite assessment are in `/tmp/gc_FiniteLinearDimension_source_assessment.md`. This elementary identity does not identify all arbitrary unpointed KLP embeddings with cone maps, prove general LinDim equality, or infer topological dimension. Those consumers are separate.

Final precise-import production normal session64494 exited0 with empty log. Production selected lint95985 exited0, no findings and exactly three reports, all [propext, Classical.choice, Quot.sound]. Four-test normal58148 exited0 with empty log. Full selected lint11879 exited0, no findings and exactly seven standard-three-axiom reports. No resource overrides, Mathlib.Tactic umbrella, shared build, canonical registration, repository mutation or reference edits. Earlier spike37457 was compile evidence only; final evidence here binds the canonical-named temporary body and drivers.

Concrete regressions: (1) actual Cone(PUnit) radius embedding into R is isometric but not required onto; all scalings and actual radius2 scaled by3 are retained. (2) its translate by1 is still isometric and explicitly fails the dilation identity, proving the tip condition cannot be omitted. (3) the independently constructed literal actual real tangent equivalence at7 satisfies BOTH all-parameter identities, including negative vectors (v=-2,c=3). (4) Cone(Empty) has a genuine pointed isometry into EuclideanSpace(Fin0) and obeys all scaling identities without choosing a base direction. Tests supply actual input constructions, not the desired scaling law.

The inherited real fixture is included unchanged in order: `/tmp/gc_direction_space_review_body.lean`, `/tmp/gc_tangent_cone_review_extra.lean`. Its old square-root numerical check requires the precise test-only Mathlib.Tactic.NormNum.RealSqrt import; this replaces neither an assumption nor a proof. The new tests add one private radius-isometry helper.

- `/tmp/gc_ConeIsometryDilation_body.lean` SHA256 `3adcd36509dbf1ff44e87d125ba94e1bd034b77aaf3dc9f817012fa7dc9d7b9e`.
- `/tmp/gc_cone_isometry_dilation_review_extra.lean` SHA256 `8d004702fa4248444ad9e8bed7e78a0d867e391aa1b7cbe2991e4c6e2810fee2`.
- `/tmp/gc_FiniteLinearDimension_source_assessment.md` SHA256 `c83012212bc29a3eaa0388c8183b9da825dcae6a3b32839118bcdc889ca3564d`.
- `/tmp/gc_direction_space_review_body.lean` SHA256 `0fbb770f853222b05f6c2f246ecda76620fde276d8311afe242d6df5224111cf`.
- `/tmp/gc_tangent_cone_review_extra.lean` SHA256 `8f02327cd0a2b5c614c9582f586285afed3425ca6bc09ef8c3c1da14949a5498`.

Independent complete production/four-test read PASS: `/tmp/gc_ConeIsometryDilation_half_independent_read.md` SHA256`a0dcb2708891a46ff89d09dfcfc1435128eed8980a5d89fa1bc967840b9bb3f7`. Root also independently read all three proofs and all four test proofs, PASS, as recorded in its finite-linear-dimension author record. Neither read is mislabeled as a second compiler run.


# Independent proof and regression read: cone isometry dilation

Reviewer: ac57_half_angle. Read the complete three-theorem body and all four test proofs on 2026-09-29. PASS.

Production SHA256: 3adcd36509dbf1ff44e87d125ba94e1bd034b77aaf3dc9f817012fa7dc9d7b9e.
Test body SHA256: 8d004702fa4248444ad9e8bed7e78a0d867e391aa1b7cbe2991e4c6e2810fee2.

The exact same-direction cone distance proves the self-dilation formula, including the tip. Norm preservation from the actual tip condition and the exact two-point distance determine the inner product of f(cx) with f(x); the squared norm then forces equality with c times f(x). This needs neither surjectivity nor an angular diameter restriction. The onto-equivalence corollary preserves the same inverse map. The real inner-product hypothesis is explicit and sufficient.

The tests genuinely exercise a non-onto half-line embedding, a translated isometry for which the missing tip condition fails at c=0, the previously constructed actual real tangent equivalence and its inverse, and an empty angular base with its actual singleton cone and zero-dimensional Euclidean target. No assumed dilation property or assumed classification supplies a test conclusion.

This is an independent full mathematical proof/test read, not a duplicate compiler run or a fresh archival source audit. The author's actual normal and selected-linter runs are distinct evidence.


# Finite actual-tangent linear dimension: author proof and statement review

Three new leaves expose one standard mathematical definition and three ordinary public theorems. Metric.TangentLinearDimension defines Metric.linearDimension X in ENNReal for a metric X with the actual HasAnglesAt family: the supremum of natural k over original points p and actual isometric embeddings EuclideanSpace(R,Fin k)->TangentCone p. Its natural least-upper-bound characterization quantifies over every original point, rank and isometric map. It does not assume those maps are onto, pointed or conical. There are no new proposition packages, private production helpers, duplicate tangent models or arbitrary formal dimension parameters.

This is exactly the KLP6A metric-subspace convention, extended to Empty by the empty supremum0. Root reopened the actual cached KLP definition at /tmp/gc140/KLP.txt lines2565-2573 (printed61/PDF63),6.1-6.6 context and reviewed the finite source comparison from /tmp/gc_FiniteLinearDimension_source_assessment.md SHAc83012212bc29a3eaa0388c8183b9da825dcae6a3b32839118bcdc889ca3564d. The assessment records independently reopened KLP6.18/6.20 and AKP7.9 plus15.6, exact archived PDF and extracted text hashes, retained errata and source-version distinctions. No fresh external query or full-book reading is claimed.

Comparison.LinearDimensionIdentity proves linearDimension(X)=dimH(univ) from the original complete source, genuine continuous near-short endpoint curves, finite natural global Hausdorff bound n, and local four-point comparison parameter1 everywhere. HasAnglesAt is derived for every original point. The upper bound uses arbitrary f:E^k->actual T_p, isometric image dimension, monotonicity and the accepted exact actual tangent dimension. The lower bound uses a regular original point from the newly proved dense Euclidean tangent set, and the actual inverse isometry. Empty is treated using Hausdorff dimension0 and bottom<=sup, without choosing a point. No TopDim statement or infinite-dimensional converse occurs.

Comparison.GreatestTangentRank retains [Nonempty X] and ONE m<=n, global Hausdorff equality and equality for every nonempty open subset. It proves IsGreatest at m for BOTH realized-rank sets: arbitrary metric Euclidean embeddings into actual tangents (KLP), and pointed embeddings commuting with all nonnegative cone dilations (AKP). The same regular point and same pointed inverse onto isometry attain m in both sets. The generic proved dilation identity supplies the conical law, not a renamed metric equivalence. Universal upper rank comes from the definition and just-proved dimension equality and hence applies even to unpointed maps. The nonempty condition is essential: Empty has dimension0 but neither rank set has a greatest element.

The generic cone lemma is reviewed separately: exact radial distance gives norms and a polarization identity, forcing the dilation law in an arbitrary real inner-product space. Root read its whole final production body SHA3adcd36509dbf1ff44e87d125ba94e1bd034b77aaf3dc9f817012fa7dc9d7b9e and all four tests SHA8d004702fa4248444ad9e8bed7e78a0d867e391aa1b7cbe2991e4c6e2810fee2. Tests include nononto halfline radius embedding, translated-isometry counterexample to dropping tip preservation, literal real tangent with negative vectors, and Empty-base cone/Euclidean0. Full proof/test read PASS; source author compiler evidence is separate.

Root actual normal checks: definition/API session44324 exit0/empty with precise undeprecated Mathlib.Basic.ENNReal.Basic import; dimension identity92150 exit0/empty; greatest rank37429 exit0/empty. A prior draft's scoped ENNReal notation and deprecated Data.ENNReal.Basic import were repaired; no warning suppression is used. Final combined selected lint session42319 actually exited0, no unusedArguments/simpNF/synTaut findings and four reports exactly propext, Classical.choice, Quot.sound. Definition and theorem kinds were inspected directly. These drivers use the full proved temporary dependency forest; canonical imports and shared gate remain required after registration.

The result is the finite linear/Hausdorff part of KLP6.18, with explicit AKP cone-rank compatibility. It does not identify the linear dimension of a noncomplete open subtype: only the existing all-open Hausdorff equality is retained. It neither proves arbitrary unpointed embeddings are cone maps nor every-point regularity, angular CBB1, TopDim equality, infinity-case classification or migration-bound smooth results. Earlier accepted mathematical leaves and blueprint207 remain unchanged.

## Canonical import repair

The first canonical shared build (session90720) exited1 because LinearDimensionIdentity used ENNReal notation without its own `open scoped ENNReal`; the concatenated author driver inherited that scope. Only this explicit scope opening was added to the body and canonical leaf; theorem type and proof commands are unchanged. Final canonical source-copy normal compilation session39336 actually exited0 with an empty log. The whole updated root forest selected lint/axiom driver session30799 actually exited0 with the same four standard-axiom reports and no findings. The old root freeze is preserved at /tmp/gc_FiniteLinearDimension_root_freeze_before_scope_repair.json. These are actual repairs, not a waiver of canonical checks; shared gate and canonical test checks must run again after this final edit.


# Independent full finite linear-dimension production review

PASS on all three root production bodies below. This is source-agent independent proof/API review of root's implementation; the actual original-input tests described later were written and compiled by this reviewing agent and are not mislabeled independent of their own author.

The definition is exactly the ENNReal supremum of genuine metric Euclidean embedding ranks in the SAME original tangents, with no onto/pointed requirement. Its least-upper-bound iff follows from the actual nested supremum, quantifying over EVERY original point, rank and isometric map. The definition is not merely an input upper bound and introduces no assumed tangent realization.

The original-source dimension identity derives the HasAnglesAt family from actual local comparison. For the upper bound, any isometric image has exactly the original Euclidean dimension k; monotonicity in the actual tangent and accepted literal tangent dimension=m give k<=dimH X. For the lower bound, the nonempty branch chooses an actual point of the dense regular set and its genuine inverse onto Euclidean tangent isometry. The empty branch uses dimH X=0 and nonnegativity of the genuine supremum without manufacturing a point. All natural upper n, including0, are supported.

The greatest-rank theorem keeps Nonempty X and ONE m before both complete rank sets and all nonempty open V. Metric rank upper applies to ALL unpointed maps. The SAME actual regular point and SAME inverse pointed onto map attain m in both metric and cone-rank sets; the new generic dilation theorem proves the AKP multiplication law for that actual map. Equality of the two finite maxima is not confused with pointwise equality of every embedding or with a general theorem for arbitrary metric spaces. Empty would make both rank sets empty, so its exclusion from IsGreatest is necessary.

Exact source conventions and partial scope are reviewed in `/tmp/gc_FiniteLinearDimension_source_assessment.md`: KLP6A metric-subspace convention and finite6.18 conclusion versus AKP7.9 cone multiplication, no TopDim/infinite-case claim. The all-open Hausdorff equality does not assert LinDim of a noncomplete open subtype. No dependency cycle uses the newly defined linear dimension to produce the previously accepted charts/tangents.

- `/tmp/gc_TangentLinearDimension_body.lean` SHA256 `dde446f44c2c1861bb8de236cffb293160e6c934174891d2d9ee6e1d59264ee8`.
- `/tmp/gc_LinearDimensionIdentity_body.lean` SHA256 `89f13e8d5268f8ee61202012c16445f9ca7f6222d3643a6c419cae60f7937ed3`.
- `/tmp/gc_GreatestTangentRank_body.lean` SHA256 `119fa72c633ba6f73092a25276ce97d454b3db807b5392513ea9a15568616cd7`.
- `/tmp/gc_FiniteLinearDimension_root_freeze.json` SHA256 `cfb0faeb1bd10009ee1df4ba6f89a2b62bb80ca41265d599f47a44a44dfaef75`.


# Five original-input finite linear-dimension regressions

Final normal session93633 exited0 with empty log. Selected lint session48802 exited0 with no findings and exactly nine standard-three-axiom reports: one definition, three root theorems and five NEW tests. Canonical milestone136 is imported; only the four new137 bodies are concatenated. No Mathlib.Tactic umbrella, resource override, shared build, repository mutation or original-source edits.

Real and plane fixtures use deliberately loose natural upper bounds3 and4, but derive literal linearDimension=1/2 respectively and identify the ONE output m with1/2 from independently computed Hausdorff dimension. Each preserves global dimension, ALL nonempty ambient-open V dimension equality, and BOTH full IsGreatest rank sets for the SAME m, including actual pointed maps with their all-NNReal dilation law. The PUnit original source has sharp n0 and obtains linearDimension0 with rank0 genuinely ATTAINED in both sets. The Empty original source has linearDimension0 but its entire metric-embedding rank set is empty and has NO greatest element at any rank. Finally the real all-map upper-bound iff is tested at sharp bound1 and fails at1/2, exercising its universal quantification over every original point/rank/map. No test hypothesizes a linear-dimension value, regular point, Euclidean tangent or greatest-rank witness.

The inherited original fixtures and dense-tangent regressions are included once in the order frozen below. These new tests are author tests by source_review; independent production review of root's bodies is separate, and a peer independent read of these tests is requested separately.

- `/tmp/gc_finite_linear_dimension_review_extra.lean` SHA256 `34ce31682b803136e7807759a993a8639688729cd89fd59c5b56d27967e1224b`.
- `/tmp/gc_finite_linear_dimension_review_agent.lean` SHA256 `a2c854e0f226d0632c8bd4ecb8c72acad7a160979f38f04124cc6fdbd42028c2`.
- `/tmp/gc_finite_linear_dimension_review_lint.lean` SHA256 `dc1cefcd393b4342c2b91222adc5171d07ed442b1d6ed2c538eafa2cf90f75bc`.
- `/tmp/gc_FiniteLinearDimension_source_independent_read.md` SHA256 `a60872e69919e0c4603b3226f37f35b691f6a1f0d2f78b6d9353f0dbf46459ff`.

## Final explicit-scope rerun

The unchanged mathematical tests were regenerated against the final explicit-ENNReal-scope identity leaf and rerun: normal98282 exit0/empty; selected lint72412 exit0/nine standard-three reports/no findings. Full old/new hash and auxiliary-generator recovery audit: `/tmp/gc_FiniteLinearDimension_scope_repair_source_review.md`. Earlier test evidence is preserved under `_before_scope_repair` paths.


# Independent finite actual-tangent linear dimension review (agent65)

Verdict: PASS. Complete direct read of the three root production bodies (one definition and three theorems) and all five final concrete regression proofs. The generic ConeIsometryDilation production body and source assessment were also read. This is an independent source/API/proof/test READ; no duplicate normal/lint execution is claimed. The authors' separate actual exit0/compiler evidence is bound by their freezes.

## Immutable reviewed snapshots

- `/tmp/gc_TangentLinearDimension_body.lean`: `dde446f44c2c1861bb8de236cffb293160e6c934174891d2d9ee6e1d59264ee8`.
- `/tmp/gc_LinearDimensionIdentity_body.lean`: `89f13e8d5268f8ee61202012c16445f9ca7f6222d3643a6c419cae60f7937ed3`.
- `/tmp/gc_GreatestTangentRank_body.lean`: `119fa72c633ba6f73092a25276ce97d454b3db807b5392513ea9a15568616cd7`.
- `/tmp/gc_finite_linear_dimension_review_extra.lean`: `34ce31682b803136e7807759a993a8639688729cd89fd59c5b56d27967e1224b`.
- `/tmp/gc_FiniteLinearDimension_root_freeze.json`: `cfb0faeb1bd10009ee1df4ba6f89a2b62bb80ca41265d599f47a44a44dfaef75`.
- `/tmp/gc_FiniteLinearDimension_tests_freeze.json`: `0a7c02e078154edf979b436dbf1c8eeb6644e9943a38a800da219ce60ba1f99b`.

## Definition and source conventions

Freshly reopened KLP Lecture6A definition, printed61/PDF63, cached text /tmp/gc140/KLP.txt lines2565–2573: the rank is realized by an arbitrary metric isometric embedding E^k into an actual tangent at some original point. The ENNReal iterated supremum and its forall-point/rank/map least-upper-bound theorem match that convention exactly. No surjectivity, chosen origin or conical property is silently required. The empty family has supremum0 as an explicitly recorded extension.

Freshly reopened AKP7.9, printed/PDF77, cached /tmp/gc125_assessment/AlexanderKapovitchPetrunin303Alexandrov.txt lines3019–3034: its embedding must respect cone multiplication. This is a DISTINCT convention; the second IsGreatest assertion states the actual pointed dilation equation and proves attainment using the separately proved inverse-isometry dilation law. The theorem does not claim every unpointed embedding is itself conical or that the conventions coincide for arbitrary metric spaces with angles. The pinned archive/text identities, retained errata and source-version distinctions are those in /tmp/gc_FiniteLinearDimension_source_assessment.md, freshly read in full. No new remote retrieval is claimed.

## Full proof audit

The upper dimension bound applies to EVERY original point and EVERY actual map, using isometric image Hausdorff dimension and monotonicity into the SAME tangent, then the accepted exact all-point tangent dimension. It needs neither pointing nor onto. The lower bound chooses an actual point only after proving Nonempty X and using the genuine dense Euclidean-tangent theorem. The supplied inverse onto isometry realizes the exact global dimension; no chart-rank surrogate or cone model is substituted. Empty X is handled separately by its actual Hausdorff dimension0 and the bottom inequality, without false attainment.

The greatest-rank theorem keeps ONE m≤n and all nonempty open-region Hausdorff equalities before both realized-rank sets. The SAME regular point and same e.symm attain m in both sets. The upper bound for each set quantifies over every point, rank and map. Nonempty X is essential and explicit, because the Empty-source rank set is empty rather than {0}.

The read generic dilation proof is sound: exact radius norms and distance from x to its nonnegative dilation give the inner product by polarization, then the squared norm of f(cx)−cf(x) vanishes. It requires tip preservation but not onto; the inverse specialization applies to the actual pointed tangent isometry. No positivity of radius or nonempty angular base is needed.

## Five original-input regressions

Real loose upper3 gives actual linear dimension1 and the SAME m1 as greatest element of BOTH rank sets, preserving all nonempty open-region equalities. The translated-plane loose upper4 similarly yields actual2 and both full maxima. PUnit sharp upper0 has genuine attained rank0 at its existing point. Empty has linear dimension0 but its realized metric rank set is empty and has NO greatest element; this tests the nonempty guard. Finally the real all-map upper-bound iff is exercised at the sharp threshold1 and disproved at1/2. None of these tests assumes the dimension equality or a supplied maximum as a premise; all geometry comes from actual original fixtures.

Scope is finite original-global linear/Hausdorff equality and the exact KLP/AKP finite maximum comparison. No TopDim identity, infinite-dimensional converse, linear dimension of a noncomplete open subtype, every-point regularity, or Chapter3–4 completion is asserted. No repository edits or shared builds by this reviewer.


# Milestone137 explicit scope and generator-path repair

Independent source-review PASS on the final repaired identity body. The only difference from the fully reviewed earlier body is the added standalone `open scoped ENNReal` line. Removing exactly that line recovers the original SHA25689f13e8d5268f8ee61202012c16445f9ca7f6222d3643a6c419cae60f7937ed3 byte for byte. No theorem type, proof expression, fixture, or mathematical test changed. New body SHA256420f5c95cca39302a6c5c1802db0f5bed132a92413b61f5c0dfc8132683395c3. The explicit scope fixes isolated canonical-leaf elaboration, which the concatenated author driver had accidentally inherited. Root's repaired canonical leaf normal39336 and root selected-lint30799 both passed, four standard-axiom reports. Root freeze is now ff4fc2d49fc3d39fc210ad071305ca787f5e9858ec66d3abc5ff0a13f60e0ba5.

The author five-test normal and selected-lint drivers were regenerated against this exact final body and rerun: normal98282 exited0 with an empty log; lint72412 exited0 with exactly nine standard-three-axiom reports and no findings. The five-test body remains SHA25634ce31682b803136e7807759a993a8639688729cd89fd59c5b56d27967e1224b. Earlier freezes, drivers and records are preserved under their `_before_scope_repair` paths; they remain historical evidence, not final canonical acceptance claims. The original independent root-body and peer records retain their historical bindings and are complemented by this explicit repair receipt.

A separate temporary generator-path collision was resolved WITHOUT changing its frozen bytes: the original author generator was recovered from the actual local command transcript plus its recorded patch, restoring expected SHA2562a821a95b7c36d202c59b8132fb39015c67d1de797e0343791e147be24d24f0c at `/tmp/gc_make_finite_linear_dimension_review.py`. The canonical-import generator now lives at the distinct `/tmp/gc_make_finite_linear_dimension_canonical_review.py`. No body, fixture or mathematical test was altered by this recovery. The package preflight verifies every upstream frozen file, so this mismatch could not silently pass.

No shared build or repository mutation was performed by this author during either repair. Root handles canonical build, review, receipt copying and publication separately; their fresh results are required before acceptance.


# Independent scope-repair supplement for 137

Reviewer: ac65_same_lines. PASS. This supplements and does not replace `/tmp/gc_FiniteLinearDimension_65_independent_read.md` (SHA256 `02ce9e42d431b6a4878ce31b06d3cf174d159386c080b04dee16aadadf18f7c1`).

The final `LinearDimensionIdentity` body adds the explicit `open scoped ENNReal` needed by its canonical independent leaf. The theorem statement and mathematical proof are unchanged. The new body SHA256 is `420f5c95cca39302a6c5c1802db0f5bed132a92413b61f5c0dfc8132683395c3`; the root freeze is `ff4fc2d49fc3d39fc210ad071305ca787f5e9858ec66d3abc5ff0a13f60e0ba5`. The reviewer read this scope repair and confirmed the previous proof/API verdict remains valid. This is a read supplement, not a new compiler-execution claim. Root owns the actual minimal normal/lint rerun, and source_review owns the unchanged five-test regeneration against the repaired canonical header.


```lean
import DifferentialGeometry.Geometry.Metric.ConeIsometryDilation
import DifferentialGeometry.Geometry.Metric.TangentLinearDimension
import DifferentialGeometry.Geometry.Comparison.LinearDimensionIdentity
import DifferentialGeometry.Geometry.Comparison.GreatestTangentRank
import DifferentialGeometry.Geometry.Comparison.DirectionPackingOpen
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentChart
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentDirections
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalDirections
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Linter

noncomputable section
open Set Metric Filter Topology Real InnerProductGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped NNReal ENNReal Topology MeasureTheory

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

namespace GCDirectionSpaceReview

private theorem chart_real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private theorem chart_real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments chart_real_segments

local instance : LocallyCompactSpace (ball (7 : ℝ) (8 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

private theorem chart_real_intrinsic_local :
    ∀ z : ball (7 : ℝ) (8 * (1 : ℝ)), ∃ Ω : Set (ball (7 : ℝ) (8 * (1 : ℝ))),
      @IsOpen _
        (intrinsicBallMetricSpace chart_real_curves 7 (by norm_num : (0 : ℝ) < 8 * 1)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _
        (intrinsicBallMetricSpace chart_real_curves 7 (by norm_num : (0 : ℝ) < 8 * 1)) 1 Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff chart_real_curves 7
    (by norm_num : (0 : ℝ) < 8 * 1) z).mpr
    ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ _⟩

private theorem chart_real_obstruction (x : ball (7 : ℝ) (1 : ℝ)) :
    AngularObstruction (SpaceOfDirections x.val) 1 (8 * (2 : ℝ))⁻¹ := by
  convert actual_real_direction_obstruction_everywhere x.val using 1
  norm_num

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

theorem actual_real_two_direction_packing_open_and_univ :
    IsOpen {x : ball (7 : ℝ) (1 / 2) | ∃ ξ : Fin 2 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} ∧
    {x : ball (7 : ℝ) (1 / 2) | ∃ ξ : Fin 2 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} = univ := by
  let : LocallyCompactSpace (ball (7 : ℝ) (8 * (1 : ℝ))) := isOpen_ball.locallyCompactSpace
  constructor
  · exact isOpen_direction_packing_of_intrinsic_8_buffer chart_real_curves 7
      (R := 1) (by norm_num) chart_real_intrinsic_local 2
  · ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨σ, τ, _, _, _, hdist⟩ := actual_real_opposite_directions_everywhere x.val
    refine ⟨![σ.direction, τ.direction], ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [dist_comm] <;> linarith [Real.pi_pos]

private theorem singleton_metric_segments (a b : PUnit) :
    ∃ f : unitInterval → PUnit, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  refine ⟨fun _ => a, continuous_const, rfl, Subsingleton.elim _ _, ?_⟩
  intro s t
  have hab : b = a := Subsingleton.elim _ _
  simp [hab]

private theorem singleton_short_curves : ∀ a b : PUnit, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → PUnit, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments singleton_metric_segments

private theorem singleton_comparison : fourPointComparison 1 (univ : Set PUnit) := by
  intro x hx a ha b hb c hc hax
  exact (hax (Subsingleton.elim _ _)).elim

private theorem singleton_intrinsic_local :
    ∀ z : ball (PUnit.unit : PUnit) (8 * (1 : ℝ)),
      ∃ Ω : Set (ball (PUnit.unit : PUnit) (8 * (1 : ℝ))),
      @IsOpen _ (intrinsicBallMetricSpace singleton_short_curves PUnit.unit
        (by norm_num : (0 : ℝ) < 8 * 1)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ (intrinsicBallMetricSpace singleton_short_curves PUnit.unit
        (by norm_num : (0 : ℝ) < 8 * 1)) 1 Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff singleton_short_curves PUnit.unit
    (by norm_num : (0 : ℝ) < 8 * 1) z).mpr
    ⟨univ, isOpen_univ, singleton_comparison, mem_univ _⟩

private instance singleton_angles_everywhere (p : PUnit) : HasAnglesAt p where
  tendsto_angle σ := isEmptyElim σ

theorem actual_singleton_zero_direction_packing_open_and_univ :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit)) ∧
    IsOpen {x : ball (PUnit.unit : PUnit) (1 / 2) | ∃ ξ : Fin 0 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} ∧
    {x : ball (PUnit.unit : PUnit) (1 / 2) | ∃ ξ : Fin 0 → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} = univ := by
  let : LocallyCompactSpace (ball (PUnit.unit : PUnit) (8 * (1 : ℝ))) :=
    isOpen_ball.locallyCompactSpace
  refine ⟨inferInstance, ?_, ?_⟩
  · exact isOpen_direction_packing_of_intrinsic_8_buffer singleton_short_curves PUnit.unit
      (R := 1) (by norm_num) singleton_intrinsic_local 0
  · ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

private theorem real_dim_le_one (U : Set ℝ) : dimH U ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using (dimH_mono (subset_univ U)).trans_eq Real.dimH_univ

private theorem singleton_dim_le_one (U : Set PUnit.{1}) : dimH U ≤ (1 : ℕ) := by
  have hz : dimH U = 0 := dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)
  rw [hz]
  positivity

private theorem original_real_open_local : ∀ z ∈ ball (7 : ℝ) 2,
    ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω := by
  intro z _
  exact ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ _⟩

private theorem original_singleton_open_local : ∀ z ∈ (univ : Set PUnit.{1}),
    ∃ Ω : Set PUnit, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω := by
  intro z _
  exact ⟨univ, isOpen_univ, singleton_comparison, mem_univ _⟩

theorem actual_real_original_uniform_scaled_nets :
    ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, 0 < s → s < S → ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset ℝ,
        T.card ≤ (1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℕ) * Real.sinh 2 / ε⌉₊) ^ (1 : ℕ) ∧
        (T : Set ℝ) ⊆ closedBall (7 : ℝ) s ∧
        ∀ x ∈ closedBall (7 : ℝ) s, ∃ y ∈ T, dist x y < ε * s := by
  exact exists_uniform_small_scale_nets_of_local_comparison_and_dimH chart_real_curves
    isOpen_ball (by norm_num : 1 ≤ (1 : ℕ)) (real_dim_le_one (ball (7 : ℝ) 2))
    original_real_open_local (mem_ball_self (by norm_num))

theorem actual_singleton_original_uniform_scaled_nets :
    ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, 0 < s → s < S → ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset PUnit.{1},
        T.card ≤ (1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℕ) * Real.sinh 2 / ε⌉₊) ^ (1 : ℕ) ∧
        (T : Set PUnit.{1}) ⊆ closedBall (PUnit.unit : PUnit.{1}) s ∧
        ∀ x ∈ closedBall (PUnit.unit : PUnit.{1}) s, ∃ y ∈ T, dist x y < ε * s := by
  exact exists_uniform_small_scale_nets_of_local_comparison_and_dimH singleton_short_curves
    isOpen_univ (by norm_num : 1 ≤ (1 : ℕ)) (singleton_dim_le_one univ)
    original_singleton_open_local (mem_univ PUnit.unit)

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

theorem actual_real_original_compact_directions_proper_tangent :
    CompactSpace (SpaceOfDirections (7 : ℝ)) ∧ ProperSpace (TangentCone (7 : ℝ)) := by
  exact compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    chart_real_curves isOpen_ball (by norm_num : 1 ≤ (1 : ℕ))
    (real_dim_le_one (ball (7 : ℝ) 2)) original_real_open_local
    (mem_ball_self (by norm_num))

theorem actual_real_intrinsic_compact_directions_far_from_center :
    (14 : ℝ) ∈ ball 7 (8 * (1 : ℝ)) ∧ (14 : ℝ) ∉ closedBall 7 (1 / 2) ∧
    CompactSpace (SpaceOfDirections (14 : ℝ)) ∧ ProperSpace (TangentCone (14 : ℝ)) := by
  have hq : (14 : ℝ) ∈ ball 7 (8 * (1 : ℝ)) := by
    norm_num [mem_ball, Real.dist_eq]
  refine ⟨hq, by norm_num [mem_closedBall, Real.dist_eq], ?_⟩
  exact compact_directions_and_proper_tangent_of_intrinsic_eight_comparison_and_dimH
    chart_real_curves 7 (by norm_num : (0 : ℝ) < 1) (by norm_num : 1 ≤ (1 : ℕ))
    (real_dim_le_one (ball (7 : ℝ) (8 * (1 : ℝ)))) chart_real_intrinsic_local hq

theorem actual_singleton_original_compact_empty_directions_proper_tangent :
    IsEmpty (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    CompactSpace (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    ProperSpace (TangentCone (PUnit.unit : PUnit.{1})) ∧
    ∀ x : TangentCone (PUnit.unit : PUnit.{1}), x = EuclideanCone.tip := by
  obtain ⟨hc, hp⟩ := compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    singleton_short_curves isOpen_univ (by norm_num : 1 ≤ (1 : ℕ))
    (singleton_dim_le_one univ) original_singleton_open_local (mem_univ PUnit.unit)
  refine ⟨inferInstance, hc, hp, ?_⟩
  intro x
  rcases EuclideanCone.eq_tip_or_eq_mk x with h | ⟨r, u, _, _⟩
  · exact h
  · exact isEmptyElim u

theorem actual_singleton_intrinsic_compact_directions_proper_tangent :
    CompactSpace (SpaceOfDirections (PUnit.unit : PUnit.{1})) ∧
    ProperSpace (TangentCone (PUnit.unit : PUnit.{1})) := by
  exact compact_directions_and_proper_tangent_of_intrinsic_eight_comparison_and_dimH
    singleton_short_curves PUnit.unit (by norm_num : (0 : ℝ) < 1)
    (by norm_num : 1 ≤ (1 : ℕ))
    (singleton_dim_le_one (ball (PUnit.unit : PUnit.{1}) (8 * (1 : ℝ))))
    singleton_intrinsic_local (mem_ball_self (by norm_num))

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

private instance dense_singleton_angles (q : PUnit.{1}) : HasAnglesAt q :=
  hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1)
    isOpen_univ singleton_comparison (mem_univ q)

theorem original_real_dense_euclidean_tangents_with_exact_common_rank :
    ∃ m : ℕ, m = 1 ∧ m ≤ 3 ∧ dimH (univ : Set ℝ) = m ∧
      (∀ V : Set ℝ, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∃ S : Set ℝ, IsGδ S ∧ Dense S ∧ ∀ q ∈ S,
        ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
  have hdim : dimH (univ : Set ℝ) ≤ (3 : ℕ) := by rw [Real.dimH_univ]; norm_num
  obtain ⟨m, hm, hglobal, hopen, S, hS, hDense, hT⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH chart_real_curves hdim
      (fun p => ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ p⟩)
  have hmone : m = 1 := by exact_mod_cast hglobal.symm.trans Real.dimH_univ
  exact ⟨m, hmone, hm, hglobal, hopen, S, hS, hDense, hT⟩

theorem original_singleton_dense_set_is_all_and_tangents_are_zero_euclidean :
    ∃ m : ℕ, m = 0 ∧ m ≤ 0 ∧ dimH (univ : Set PUnit.{1}) = m ∧
      (∀ V : Set PUnit.{1}, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∃ S : Set PUnit.{1}, S = univ ∧ IsGδ S ∧ Dense S ∧ ∀ q ∈ S,
        ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
  have hdim : dimH (univ : Set PUnit.{1}) ≤ (0 : ℕ) := by
    rw [Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)]
    simp only [Nat.cast_zero, le_refl]
  obtain ⟨m, hm, hglobal, hopen, S, hS, hDense, hT⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH singleton_short_curves hdim
      (fun p => ⟨univ, isOpen_univ, singleton_comparison, mem_univ p⟩)
  have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
  have hSuniv : S = univ := by
    obtain ⟨q, hq⟩ := hDense.nonempty
    apply Set.eq_univ_of_forall
    intro x
    simpa only [Subsingleton.elim x q] using hq
  exact ⟨m, hmzero, hm, hglobal, hopen, S, hSuniv, hS, hDense, hT⟩

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

private instance dense_plane_angles (q : Plane) : HasAnglesAt q :=
  hasAnglesAt_of_local_fourPointComparison_zero isOpen_univ inner_comparison (mem_univ q)

theorem original_plane_dense_euclidean_tangents_with_exact_common_rank :
    ∃ m : ℕ, m = 2 ∧ m ≤ 4 ∧ dimH (univ : Set Plane) = m ∧
      (∀ V : Set Plane, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∃ S : Set Plane, IsGδ S ∧ Dense S ∧ ∀ q ∈ S,
        ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
  have hactual : dimH (univ : Set Plane) = (2 : ENNReal) := by
    rw [Real.dimH_univ_eq_finrank]
    simp [Plane]
  have hdim : dimH (univ : Set Plane) ≤ (4 : ℕ) := by rw [hactual]; norm_num
  obtain ⟨m, hm, hglobal, hopen, S, hS, hDense, hT⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH plane_short_curves hdim
      (fun p => ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num), mem_univ p⟩)
  have hmtwo : m = 2 := by exact_mod_cast hglobal.symm.trans hactual
  exact ⟨m, hmtwo, hm, hglobal, hopen, S, hS, hDense, hT⟩

end GCPlaneDirectionPackingReview

namespace GCDenseEuclideanTangentsReview

private instance dense_empty_angles (q : Empty) : HasAnglesAt q := q.elim

theorem original_empty_dense_euclidean_tangents_without_chosen_point :
    ∃ m : ℕ, m = 0 ∧ m ≤ 0 ∧ dimH (univ : Set Empty) = m ∧
      (∀ V : Set Empty, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∃ S : Set Empty, S = ∅ ∧ IsGδ S ∧ Dense S ∧ ∀ q ∈ S,
        ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
  have hcurves : ∀ a b : Empty, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Empty, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε) := by
    intro a
    exact a.elim
  have hdim : dimH (univ : Set Empty) ≤ (0 : ℕ) := by
    rw [Set.Subsingleton.dimH_zero (fun x _ => x.elim)]
    simp only [Nat.cast_zero, le_refl]
  obtain ⟨m, hm, hglobal, hopen, S, hS, hDense, hT⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH hcurves hdim
      (fun p => p.elim)
  exact ⟨m, Nat.eq_zero_of_le_zero hm, hm, hglobal, hopen, S,
    Set.eq_empty_of_isEmpty S, hS, hDense, hT⟩

end GCDenseEuclideanTangentsReview

open Filter Topology
open scoped NNReal
namespace GCDirectionSpaceReview

private def posRep : GeodesicRepresentative (7 : ℝ) := positiveRepresentative (by norm_num : (0 : ℝ) < 1)
private def negRep : GeodesicRepresentative (7 : ℝ) := negativeRepresentative (by norm_num : (0 : ℝ) < 2)

private theorem pos_neg_angle : posRep.angle negRep = Real.pi :=
  positive_negative_angle (by norm_num [posRep, positiveRepresentative]) (by norm_num [negRep, negativeRepresentative])

private theorem pos_neg_dist : dist posRep.direction negRep.direction = Real.pi :=
  opposite_completed_directions_distance

private theorem neg_pos_dist : dist negRep.direction posRep.direction = Real.pi := by
  rw [dist_comm, pos_neg_dist]

theorem actual_opposite_tangent_distances :
    dist (posRep.tangentVector 2) (negRep.tangentVector 3) = 5 ∧
    dist (posRep.tangentVector 0) (negRep.tangentVector 3) = 3 := by
  rw [GeodesicRepresentative.dist_tangentVector, pos_neg_angle]
  norm_num [GeodesicRepresentative.tangentVector]

theorem original_unequal_speed_opposite_limit :
    Tendsto (fun t : ℝ => dist (posRep.path (2 * t)) (negRep.path (3 * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (5 : ℝ)) := by
  have h := posRep.dist_div_tendsto_tangentVector negRep (2 : ℝ≥0) (3 : ℝ≥0)
  simpa only [NNReal.coe_ofNat, actual_opposite_tangent_distances.1] using h

theorem original_zero_speed_limit :
    Tendsto (fun t : ℝ => dist (posRep.path (0 * t)) (negRep.path (3 * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
  have h := posRep.dist_div_tendsto_tangentVector negRep (0 : ℝ≥0) (3 : ℝ≥0)
  simpa only [NNReal.coe_zero, NNReal.coe_ofNat, actual_opposite_tangent_distances.2] using h

theorem original_equal_speed_same_direction_limit :
    Tendsto (fun t : ℝ => dist (posRep.path (2 * t)) (posRep.path (2 * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  simpa only [dist_self, NNReal.coe_ofNat] using
    posRep.dist_div_tendsto_tangentVector posRep (2 : ℝ≥0) (2 : ℝ≥0)

theorem shortened_original_tangent_vector :
    (posRep.shorten (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num [posRep, positiveRepresentative])).tangentVector 4 = posRep.tangentVector 4 :=
  posRep.tangentVector_shorten _ _ _

theorem singleton_tangent_has_only_apex :
    ∃ z : TangentCone (PUnit.unit : PUnit), ∀ x : TangentCone (PUnit.unit : PUnit), x = z := by
  refine ⟨EuclideanCone.tip, ?_⟩
  intro x
  rcases EuclideanCone.eq_tip_or_eq_mk x with h | ⟨r, u, _, _⟩
  · exact h
  · exact isEmptyElim u

private theorem real_representative_paths (σ : GeodesicRepresentative (7 : ℝ)) :
    (∀ t ∈ Icc (0 : ℝ) σ.length, σ.path t = 7 + t) ∨
    (∀ t ∈ Icc (0 : ℝ) σ.length, σ.path t = 7 - t) := by
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
    have hhigh := le_abs_self (7 - σ.path t)
    linarith
  · left
    intro t ht
    have h := σ.dist_base_path ht
    have hdist := σ.dist_path ht ⟨σ.length_pos.le, le_rfl⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hdist
    rw [Real.dist_eq] at h
    have hlow := neg_le_abs (σ.path t - σ.path σ.length)
    have hhigh := neg_le_abs (7 - σ.path t)
    linarith

private theorem representative_direction_cases (σ : GeodesicRepresentative (7 : ℝ)) :
    σ.direction = posRep.direction ∨ σ.direction = negRep.direction := by
  rcases real_representative_paths σ with hp | hm
  · left
    rw [GeodesicRepresentative.direction_eq_iff]
    change germComparisonAngle 0 σ.path posRep.path = 0
    have h := germComparisonAngle_congr_on (κ := 0) σ.length_pos
      (show 0 < posRep.length by norm_num [posRep, positiveRepresentative])
      (γ := σ.path) (β := posRep.path)
      (γ' := fun t : ℝ => 7 + t) (β' := fun t : ℝ => 7 + t)
      (fun t ht => hp t ⟨ht.1.le, ht.2⟩)
      (fun t ht => positive_path (by norm_num [posRep, positiveRepresentative]) ⟨ht.1.le, ht.2⟩)
    rw [h]
    apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
    intro s _ t _
    rw [Real.dist_eq]
    congr 1
    ring
  · right
    rw [GeodesicRepresentative.direction_eq_iff]
    change germComparisonAngle 0 σ.path negRep.path = 0
    have h := germComparisonAngle_congr_on (κ := 0) σ.length_pos
      (show 0 < negRep.length by norm_num [negRep, negativeRepresentative])
      (γ := σ.path) (β := negRep.path)
      (γ' := fun t : ℝ => 7 - t) (β' := fun t : ℝ => 7 - t)
      (fun t ht => hm t ⟨ht.1.le, ht.2⟩)
      (fun t ht => negative_path (by norm_num [negRep, negativeRepresentative]) ⟨ht.1.le, ht.2⟩)
    rw [h]
    apply germComparisonAngle_self (by norm_num) (by norm_num : (0 : ℝ) < 1)
    intro s _ t _
    rw [Real.dist_eq, show 7 - s - (7 - t) = t - s by ring, abs_sub_comm]

private theorem direction_cases (v : SpaceOfDirections (7 : ℝ)) :
    v = posRep.direction ∨ v = negRep.direction := by
  by_contra hn
  have hp : 0 < dist v posRep.direction := dist_pos.mpr (fun h => hn (Or.inl h))
  have hm : 0 < dist v negRep.direction := dist_pos.mpr (fun h => hn (Or.inr h))
  obtain ⟨σ, hσ⟩ := v.exists_representative_dist_lt (lt_min hp hm)
  rcases representative_direction_cases σ with h | h
  · rw [h] at hσ
    exact (not_lt_of_ge (min_le_left _ _)) hσ
  · rw [h] at hσ
    exact (not_lt_of_ge (min_le_right _ _)) hσ


private theorem opposite_mk_dist (r s : ℝ≥0) :
    dist (EuclideanCone.mk r posRep.direction) (EuclideanCone.mk s negRep.direction) =
      (r : ℝ) + s := by
  rw [EuclideanCone.dist_mk]
  simp only [coneDistance, pos_neg_dist, min_self, Real.cos_pi]
  rw [show (r : ℝ) ^ 2 + (s : ℝ) ^ 2 - 2 * r * s * -1 = ((r : ℝ) + s) ^ 2 by ring]
  exact Real.sqrt_sq (add_nonneg r.property s.property)

private def realVector (t : ℝ) : TangentCone (7 : ℝ) :=
  if ht : 0 ≤ t then EuclideanCone.mk (NNReal.mk t ht) posRep.direction
  else EuclideanCone.mk (NNReal.mk (-t) (le_of_lt (neg_pos.mpr (lt_of_not_ge ht)))) negRep.direction

private theorem realVector_pos (r : ℝ≥0) :
    realVector r = EuclideanCone.mk r posRep.direction := by
  unfold realVector
  split_ifs with h
  · rfl
  · exact (h r.property).elim

private theorem realVector_neg (r : ℝ≥0) :
    realVector (-(r : ℝ)) = EuclideanCone.mk r negRep.direction := by
  by_cases hr : r = 0
  · subst r
    rw [NNReal.coe_zero, neg_zero]
    rw [show realVector (0 : ℝ) = EuclideanCone.mk 0 posRep.direction from realVector_pos 0]
    simp
  · have hp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    unfold realVector
    split_ifs with h
    · linarith
    · congr 1
      exact Subtype.ext (neg_neg _)

private theorem realVector_isometry : Isometry realVector := by
  apply Isometry.of_dist_eq
  intro t s
  by_cases ht : 0 ≤ t
  · by_cases hs : 0 ≤ s
    · have h₁ := realVector_pos (NNReal.mk t ht)
      have h₂ := realVector_pos (NNReal.mk s hs)
      calc
        dist (realVector t) (realVector s) =
            dist (EuclideanCone.mk (NNReal.mk t ht) posRep.direction)
              (EuclideanCone.mk (NNReal.mk s hs) posRep.direction) := congrArg₂ dist h₁ h₂
        _ = dist t s := (EuclideanCone.isometry_mk posRep.direction).dist_eq _ _
    · have hs' : 0 ≤ -s := by linarith
      have h₁ := realVector_pos (NNReal.mk t ht)
      have h₂ : realVector s = EuclideanCone.mk (NNReal.mk (-s) hs') negRep.direction := by
        simpa only [NNReal.coe_mk, neg_neg] using realVector_neg (NNReal.mk (-s) hs')
      calc
        dist (realVector t) (realVector s) =
            dist (EuclideanCone.mk (NNReal.mk t ht) posRep.direction)
              (EuclideanCone.mk (NNReal.mk (-s) hs') negRep.direction) := congrArg₂ dist h₁ h₂
        _ = t + -s := opposite_mk_dist _ _
        _ = dist t s := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; ring
  · by_cases hs : 0 ≤ s
    · have ht' : 0 ≤ -t := by linarith
      have h₁ : realVector t = EuclideanCone.mk (NNReal.mk (-t) ht') negRep.direction := by
        simpa only [NNReal.coe_mk, neg_neg] using realVector_neg (NNReal.mk (-t) ht')
      have h₂ := realVector_pos (NNReal.mk s hs)
      calc
        dist (realVector t) (realVector s) =
            dist (EuclideanCone.mk (NNReal.mk (-t) ht') negRep.direction)
              (EuclideanCone.mk (NNReal.mk s hs) posRep.direction) := congrArg₂ dist h₁ h₂
        _ = s + -t := by rw [dist_comm]; exact opposite_mk_dist _ _
        _ = dist t s := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
    · have ht' : 0 ≤ -t := by linarith
      have hs' : 0 ≤ -s := by linarith
      have h₁ : realVector t = EuclideanCone.mk (NNReal.mk (-t) ht') negRep.direction := by
        simpa only [NNReal.coe_mk, neg_neg] using realVector_neg (NNReal.mk (-t) ht')
      have h₂ : realVector s = EuclideanCone.mk (NNReal.mk (-s) hs') negRep.direction := by
        simpa only [NNReal.coe_mk, neg_neg] using realVector_neg (NNReal.mk (-s) hs')
      calc
        dist (realVector t) (realVector s) =
            dist (EuclideanCone.mk (NNReal.mk (-t) ht') negRep.direction)
              (EuclideanCone.mk (NNReal.mk (-s) hs') negRep.direction) := congrArg₂ dist h₁ h₂
        _ = dist (-t) (-s) := (EuclideanCone.isometry_mk negRep.direction).dist_eq _ _
        _ = dist t s := dist_neg_neg _ _

private theorem realVector_surjective : Function.Surjective realVector := by
  intro x
  rcases EuclideanCone.eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
  · exact ⟨0, (realVector_pos 0).trans (EuclideanCone.mk_zero _)⟩
  · rcases direction_cases u with rfl | rfl
    · exact ⟨r, realVector_pos r⟩
    · exact ⟨-(r : ℝ), realVector_neg r⟩

private def realTangentFromReal : ℝ ≃ᵢ TangentCone (7 : ℝ) where
  toEquiv := Equiv.ofBijective realVector ⟨realVector_isometry.injective, realVector_surjective⟩
  isometry_toFun := realVector_isometry

private def realTangentEquiv : TangentCone (7 : ℝ) ≃ᵢ ℝ := realTangentFromReal.symm

private theorem realTangentEquiv_tip : realTangentEquiv EuclideanCone.tip = 0 := by
  apply realTangentFromReal.injective
  change realTangentFromReal (realTangentFromReal.symm EuclideanCone.tip) = realVector 0
  rw [IsometryEquiv.apply_symm_apply]
  exact ((realVector_pos 0).trans (EuclideanCone.mk_zero _)).symm

theorem actual_real_tangent_pointed_isometry :
    ∃ e : TangentCone (7 : ℝ) ≃ᵢ ℝ,
      e EuclideanCone.tip = 0 ∧
      e (posRep.tangentVector 2) = 2 ∧ e (negRep.tangentVector 3) = -3 := by
  refine ⟨realTangentEquiv, realTangentEquiv_tip, ?_, ?_⟩
  · have h := realTangentFromReal.symm_apply_apply (2 : ℝ)
    change realTangentEquiv (realVector 2) = 2 at h
    simpa only [show realVector 2 = posRep.tangentVector 2 from realVector_pos 2] using h
  · have h := realTangentFromReal.symm_apply_apply (-3 : ℝ)
    change realTangentEquiv (realVector (-3)) = -3 at h
    simpa only [show realVector (-3) = negRep.tangentVector 3 from realVector_neg 3] using h

theorem actual_real_tangent_unit_angle_and_density :
    InnerProductGeometry.angle
      (Metric.TangentCone.unitVector realTangentEquiv realTangentEquiv_tip posRep.direction).val
      (Metric.TangentCone.unitVector realTangentEquiv realTangentEquiv_tip negRep.direction).val =
        Real.pi ∧
    ∀ ε : ℝ, 0 < ε → ∃ σ : GeodesicRepresentative (7 : ℝ),
      InnerProductGeometry.angle (-1 : ℝ)
        (Metric.TangentCone.unitVector realTangentEquiv realTangentEquiv_tip σ.direction).val < ε := by
  constructor
  · rw [Metric.TangentCone.angle_unitVector, pos_neg_dist]
  · intro ε hε
    exact Metric.TangentCone.exists_representative_angle_lt
      realTangentEquiv realTangentEquiv_tip (-1 : ℝ) (by norm_num) hε

end GCDirectionSpaceReview

namespace GCConeIsometryDilationReview

open Metric.EuclideanCone

private theorem radius_isometry : Isometry (radius : EuclideanCone PUnit.{1} → ℝ) := by
  apply Isometry.of_dist_eq
  intro x y
  rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
  · simp [Real.dist_eq, abs_of_nonneg (radius_nonneg y)]
  · rcases eq_tip_or_eq_mk y with rfl | ⟨s, v, _, rfl⟩
    · simp
    · rw [Subsingleton.elim v u, radius_mk, radius_mk, dist_mk,
        coneDistance_same_direction]
      rfl

theorem halfline_pointed_embedding_preserves_all_dilations :
    Isometry (radius : EuclideanCone PUnit.{1} → ℝ) ∧
    (∀ c : ℝ≥0, ∀ x : EuclideanCone PUnit.{1}, radius (dilate c x) = (c : ℝ) • radius x) ∧
    dist (dilate 3 (mk 2 PUnit.unit)) (mk 2 PUnit.unit) = 4 := by
  refine ⟨radius_isometry, ?_, ?_⟩
  · intro c x
    exact map_dilate_of_isometry radius_isometry radius_tip c x
  · rw [dist_dilate_self, radius_mk]
    norm_num

theorem translated_isometry_needs_tip_preservation :
    Isometry (fun x : EuclideanCone PUnit.{1} => radius x + 1) ∧
    ¬ (∀ c : ℝ≥0, ∀ x : EuclideanCone PUnit.{1},
      radius (dilate c x) + 1 = (c : ℝ) • (radius x + 1)) := by
  refine ⟨(isometry_add_right (1 : ℝ)).comp radius_isometry, ?_⟩
  intro h
  have hh := h 0 tip
  norm_num at hh

end GCConeIsometryDilationReview

namespace GCDirectionSpaceReview

theorem actual_real_tangent_isometry_is_a_cone_isomorphism :
    (∀ c : ℝ≥0, ∀ x : TangentCone (7 : ℝ),
      realTangentEquiv (EuclideanCone.dilate c x) = (c : ℝ) • realTangentEquiv x) ∧
    (∀ c : ℝ≥0, ∀ v : ℝ,
      realTangentEquiv.symm ((c : ℝ) • v) = EuclideanCone.dilate c (realTangentEquiv.symm v)) ∧
    realTangentEquiv.symm ((3 : ℝ) • (-2 : ℝ)) =
      EuclideanCone.dilate 3 (realTangentEquiv.symm (-2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact EuclideanCone.map_dilate_of_isometry realTangentEquiv.isometry realTangentEquiv_tip
  · exact EuclideanCone.symm_map_smul_of_isometryEquiv realTangentEquiv realTangentEquiv_tip
  · exact EuclideanCone.symm_map_smul_of_isometryEquiv realTangentEquiv realTangentEquiv_tip 3 (-2)

end GCDirectionSpaceReview

namespace GCConeIsometryDilationReview

open Metric.EuclideanCone

theorem empty_base_zero_dimensional_pointed_embedding :
    Isometry (fun _ : EuclideanCone Empty => (0 : EuclideanSpace ℝ (Fin 0))) ∧
    ∀ c : ℝ≥0, ∀ x : EuclideanCone Empty,
      (fun _ : EuclideanCone Empty => (0 : EuclideanSpace ℝ (Fin 0))) (dilate c x) =
        (c : ℝ) • (0 : EuclideanSpace ℝ (Fin 0)) := by
  have hx (x : EuclideanCone Empty) : x = tip := by
    rcases eq_tip_or_eq_mk x with h | ⟨_, u, _, _⟩
    · exact h
    · exact u.elim
  have hf : Isometry (fun _ : EuclideanCone Empty => (0 : EuclideanSpace ℝ (Fin 0))) := by
    apply Isometry.of_dist_eq
    intro x y
    rw [hx x, hx y, dist_self, dist_self]
  refine ⟨hf, ?_⟩
  exact map_dilate_of_isometry hf rfl

end GCConeIsometryDilationReview

open scoped ENNReal NNReal

namespace GCDirectionSpaceReview

theorem real_linear_dimension_and_both_greatest_ranks :
    Metric.linearDimension ℝ = 1 ∧
    ∃ m : ℕ, m = 1 ∧ m ≤ 3 ∧ dimH (univ : Set ℝ) = m ∧
      (∀ V : Set ℝ, IsOpen V → V.Nonempty → dimH V = m) ∧
      IsGreatest {k : ℕ | ∃ q : ℝ,
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q, Isometry f} m ∧
      IsGreatest {k : ℕ | ∃ q : ℝ,
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
          Isometry f ∧ f 0 = EuclideanCone.tip ∧
            ∀ c : ℝ≥0, ∀ v, f ((c : ℝ) • v) = EuclideanCone.dilate c (f v)} m := by
  have hd : dimH (univ : Set ℝ) ≤ (3 : ℕ) := by rw [Real.dimH_univ]; norm_num
  have hl := linearDimension_eq_dimH_of_local_comparison_and_dimH chart_real_curves hd
    (fun p => ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ p⟩)
  obtain ⟨m, hm, hg, ho, hmetric, hcone⟩ :=
    exists_greatest_euclidean_tangent_rank_of_local_comparison_and_dimH chart_real_curves hd
      (fun p => ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ p⟩)
  have he : m = 1 := by exact_mod_cast hg.symm.trans Real.dimH_univ
  exact ⟨hl.trans Real.dimH_univ, m, he, hm, hg, ho, hmetric, hcone⟩

theorem singleton_linear_dimension_zero_and_attained_zero_ranks :
    Metric.linearDimension PUnit.{1} = 0 ∧
    ∃ m : ℕ, m = 0 ∧ m ≤ 0 ∧ dimH (univ : Set PUnit.{1}) = m ∧
      (∀ V : Set PUnit.{1}, IsOpen V → V.Nonempty → dimH V = m) ∧
      IsGreatest {k : ℕ | ∃ q : PUnit.{1},
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q, Isometry f} m ∧
      IsGreatest {k : ℕ | ∃ q : PUnit.{1},
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
          Isometry f ∧ f 0 = EuclideanCone.tip ∧
            ∀ c : ℝ≥0, ∀ v, f ((c : ℝ) • v) = EuclideanCone.dilate c (f v)} m := by
  have hz : dimH (univ : Set PUnit.{1}) = 0 :=
    Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)
  have hd : dimH (univ : Set PUnit.{1}) ≤ (0 : ℕ) := by rw [hz]; exact zero_le
  have hl := linearDimension_eq_dimH_of_local_comparison_and_dimH singleton_short_curves hd
    (fun p => ⟨univ, isOpen_univ, singleton_comparison, mem_univ p⟩)
  obtain ⟨m, hm, hg, ho, hmetric, hcone⟩ :=
    exists_greatest_euclidean_tangent_rank_of_local_comparison_and_dimH singleton_short_curves hd
      (fun p => ⟨univ, isOpen_univ, singleton_comparison, mem_univ p⟩)
  exact ⟨hl.trans hz, m, Nat.eq_zero_of_le_zero hm, hm, hg, ho, hmetric, hcone⟩

theorem actual_real_rank_bound_iff_has_sharp_threshold :
    (∀ q : ℝ, ∀ k : ℕ, ∀ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
      Isometry f → (k : ENNReal) ≤ 1) ∧
    ¬ (∀ q : ℝ, ∀ k : ℕ, ∀ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
      Isometry f → (k : ENNReal) ≤ 1 / 2) := by
  have hd := real_linear_dimension_and_both_greatest_ranks.1
  constructor
  · exact Metric.linearDimension_le_iff.mp hd.le
  · intro h
    have hh := Metric.linearDimension_le_iff.mpr h
    rw [hd] at hh
    norm_num at hh

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

theorem plane_linear_dimension_and_both_greatest_ranks :
    Metric.linearDimension Plane = 2 ∧
    ∃ m : ℕ, m = 2 ∧ m ≤ 4 ∧ dimH (univ : Set Plane) = m ∧
      (∀ V : Set Plane, IsOpen V → V.Nonempty → dimH V = m) ∧
      IsGreatest {k : ℕ | ∃ q : Plane,
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q, Isometry f} m ∧
      IsGreatest {k : ℕ | ∃ q : Plane,
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
          Isometry f ∧ f 0 = EuclideanCone.tip ∧
            ∀ c : ℝ≥0, ∀ v, f ((c : ℝ) • v) = EuclideanCone.dilate c (f v)} m := by
  have he : dimH (univ : Set Plane) = (2 : ENNReal) := by
    rw [Real.dimH_univ_eq_finrank]
    simp [Plane]
  have hd : dimH (univ : Set Plane) ≤ (4 : ℕ) := by rw [he]; norm_num
  have hl := linearDimension_eq_dimH_of_local_comparison_and_dimH plane_short_curves hd
    (fun p => ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num), mem_univ p⟩)
  obtain ⟨m, hm, hg, ho, hmetric, hcone⟩ :=
    exists_greatest_euclidean_tangent_rank_of_local_comparison_and_dimH plane_short_curves hd
      (fun p => ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num), mem_univ p⟩)
  have hmtwo : m = 2 := by exact_mod_cast hg.symm.trans he
  exact ⟨hl.trans he, m, hmtwo, hm, hg, ho, hmetric, hcone⟩

end GCPlaneDirectionPackingReview

namespace GCDenseEuclideanTangentsReview

theorem empty_linear_dimension_zero_without_attained_rank :
    Metric.linearDimension Empty = 0 ∧
    {k : ℕ | ∃ q : Empty, ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
      Isometry f} = ∅ ∧
    ¬ ∃ m : ℕ, IsGreatest {k : ℕ | ∃ q : Empty,
      ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q, Isometry f} m := by
  have hcurves : ∀ a b : Empty, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Empty, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε) := by
    intro a
    exact a.elim
  have hz : dimH (univ : Set Empty) = 0 := Set.Subsingleton.dimH_zero (fun x _ => x.elim)
  have hd : dimH (univ : Set Empty) ≤ (0 : ℕ) := by rw [hz]; exact zero_le
  have hl := linearDimension_eq_dimH_of_local_comparison_and_dimH hcurves hd (fun p => p.elim)
  refine ⟨hl.trans hz, ?_, ?_⟩
  · ext k
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
    intro q
    exact q.elim
  · rintro ⟨m, ⟨q, _, _⟩, _⟩
    exact q.elim

end GCDenseEuclideanTangentsReview

#lint- only unusedArguments simpNF synTaut
#print axioms Metric.EuclideanCone.dist_dilate_self
#print axioms Metric.EuclideanCone.map_dilate_of_isometry
#print axioms Metric.EuclideanCone.symm_map_smul_of_isometryEquiv
#print axioms Metric.linearDimension
#print axioms Metric.linearDimension_le_iff
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.linearDimension_eq_dimH_of_local_comparison_and_dimH
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_greatest_euclidean_tangent_rank_of_local_comparison_and_dimH
#print axioms GCConeIsometryDilationReview.halfline_pointed_embedding_preserves_all_dilations
#print axioms GCConeIsometryDilationReview.translated_isometry_needs_tip_preservation
#print axioms GCDirectionSpaceReview.actual_real_tangent_isometry_is_a_cone_isomorphism
#print axioms GCConeIsometryDilationReview.empty_base_zero_dimensional_pointed_embedding
#print axioms GCDirectionSpaceReview.real_linear_dimension_and_both_greatest_ranks
#print axioms GCDirectionSpaceReview.singleton_linear_dimension_zero_and_attained_zero_ranks
#print axioms GCDirectionSpaceReview.actual_real_rank_bound_iff_has_sharp_threshold
#print axioms GCPlaneDirectionPackingReview.plane_linear_dimension_and_both_greatest_ranks
#print axioms GCDenseEuclideanTangentsReview.empty_linear_dimension_zero_without_attained_rank
```

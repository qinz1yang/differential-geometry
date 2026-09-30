# Local integer Hausdorff dimension acceptance

The 457-module shared gate checks 2,191 owned declarations in 3,295 jobs. Its observed increment is 13 owned declarations: four public theorems and 9 compiler-generated declarations. Nine new concrete regressions and thirteen canonical-import standard-axiom reports pass with silent selected lint. The separate unchanged blueprint static audit remains pending; no static pass is claimed.

Every owned transitive closure is restricted to propext, Classical.choice and Quot.sound. All four new production declarations and nine new tests appear in the thirteen explicit reports; inherited fixtures are re-elaborated once and not counted as new. Counts are observed relative to the actual milestone129 receipt, not predicted. No new admission, mathematical axiom, instance, private production helper or resource-limit increase was introduced. Earlier mathematical leaves are unchanged. No full migrated-root, PDF, Overleaf or human-approval claim is made.

# Local integer Hausdorff dimension

Four public theorems in three leaves prove original local Hausdorff dimension propagation and a common integer dimension. Complete metric sources with arbitrarily short continuous endpoint curves and intrinsic local comparison parameter1 on the original open8R ball are retained. With `dimH(ball(p,8R)) <= n` for ANY natural n, the final theorem returns ONE integer m<=n such that `dimH(closedBall(p,R))=m` and EVERY nonempty ambient-open V contained in ball(p,R/2) has `dimH V=m`. Local compactness is derived from the original finite-dimensional hypotheses. The original metric, balls, integer and quantifier order are preserved, including n0 and singleton geometry.

The first leaf transfers the dimension of the original closed ball to every positive-radius original ball centered in the half-ball. Its local compactness input is explicit and no dimension bound is needed. The actual radial contraction has an Antilipschitz bound, so Hausdorff dimension transfers without assuming continuity or compactness of its image. The two nearby-chart producers retain the actual rank and a positive-radius ball with dimension exactly that rank. They use the established onto homeomorphism to a nonempty OPEN Euclidean image and both metric estimates; the chart is not an isometry. A loose original upper bound is never silently equated with the actual rank.

The source route is the Hausdorff portion of KLP6.18 and6.19 (printed69/PDF71), with the complete6.19 semisolution (printed137-138/PDF139-140) and the already checked6.13/6.14 radial inequalities. The stronger linear/topological dimension identity and the semisolution's compact-subset wording are not claimed. Nonempty open subsets are explicitly required; the source's displayed open-subset statement cannot literally include an empty set in positive dimension. Archived source, accepted paired-chart/BGP correction records and exact dependencies remain distinct in the source receipt. Parameter1 means curvature lower bound-1; the open buffer is not assumed complete.



# Local integer dimension and homogeneity: source/API assessment

This assessment was requested read-only and completed before proposing the following bounded consumer. Root separately authorized its temporary implementation after agreeing the interfaces. No accepted source, theorem or repository file is modified.

## Source passages actually reread

KLP archived v1 July14,2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`:6.18/6.19 full statement/proof printed69/PDF71, plus6.19 full semisolution printed137–138/PDF139–140. The source proves equality of LINEAR, topological and Hausdorff dimension using right inverse6.8, Bishop–Gromov6.13/14, properness6.15 and Szpilrajn. Its6.19 semisolution moves a compact set of a given dimension into any open ball by the radial map and invokes the6.18 argument. The accepted GC chart and metric contraction results already supply a different sufficient dependency route for the Hausdorff-only finite-dimensional assertion here. This does not prove equality with linear/topological dimension or reproduce the volume/gradient arguments.

The exact KLP6.13/6.14 contraction passages and normalization were freshly reread in the preceding actual-log assessment:6.13 printed66–67/PDF68–69;6.14 printed67–68/PDF69–70 and semisolution137/PDF139. Curvature parameter1 in GC means lower curvature bound-1. Existing archived/source/errata qualifications remain unchanged; no new external correction lookup is claimed.

The source's additional compact-subset wording is NOT inferred from an arbitrary chosen radial map. The accepted radial map need not be continuous; the dimension inequality only needs its Antilipschitz property. We use image containment and the Hausdorff dimension inequality, never compactness of its image.

## Existing exact APIs read

* `Comparison.CenteredPairedChart.exists_centered_distance_chart_in_open_set`: for nontrivial X with actual near-short curves, comparison on Omega, local complete balls, nonempty open O inside Omega, and finite upper bound n>=1, returns an actual rank1<=m<=n, q in O, positive r, ball(q,r) inside O, OPEN W in EuclideanSpace(Fin m), and a HOMEOMORPHISM e:ball(q,r)≃ₜW with explicit two-sided metric bounds. It is not an isometry. W is nonempty because e is defined at q. Those bounds prove both Lipschitz directions, so Hausdorff dimension of the actual chart ball is exactly m.
* `NearbyPairedChart.exists_centered_chart_near_of_local_comparison`: constructs V=Omega∩(U∩ball(p,epsilon)), invokes the above exact chart, but its public conclusion drops W/e and keeps the coordinate map and both bounds. Recovering W by calling the existing centered producer is legitimate; modifying the old theorem is unnecessary.
* `EightFiniteDimensionalCovering.exists_closedBall_net_of_local_eight_comparison_and_dimH`: its proof already retains m temporarily, applies `EightChartCovering.exists_closedBall_net_of_intrinsic_8_comparison_and_chart` at m, then weakens m to n using `chart_net_bound_mono_dimension`. This gives an alternative exponent-retention route, but it is unnecessary for the shorter dimension proof below.
* `EightRadialContraction.exists_radial_contraction_of_intrinsic_8_buffer`: actual complete X and near-short curves, local compactness of OPEN8R, intrinsic local comparison1 there, q in ball(p,R/2), and0<delta<R give an actual map h:closedBall(p,R)->X with image in ball(q,delta), and lower bound `(delta/sinh(2R))*dist(x,y)<=dist(hx,hy)` on the entire original source ball. No continuity is included.
* `FiniteDimensionalLocalCompactness.locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH` derives precisely the required local compactness from the original open-ball finite upper bound and local comparison.
* Mathlib `AntilipschitzWith.le_dimH_image`, `LipschitzWith.dimH_image_le`, `Isometry.dimH_image`, `Real.dimH_of_nonempty_interior`/`Real.dimH_of_mem_nhds`, and `dimH_mono` supply the dimension comparisons. No new measure/gradient/Baire theory is needed for these local Hausdorff statements.

## Bounded precise conclusion

Original hypotheses: complete ambient metric X, global arbitrarily short continuous endpoint curves, R>0, original intrinsic local comparison parameter1 on ball(p,8R), and `dimH(ball(p,8R))<=n` for an arbitrary natural n. No supplied local compactness, positive dimension, compact directions or Euclidean tangent is needed.

Proposed conclusion:

`exists m:Nat, m<=n and dimH(closedBall(p,R))=m and
 forall V:Set X, IsOpen V -> V.Nonempty -> V subset ball(p,R/2) -> dimH V=m`.

ONE integer m is chosen before every V. The actual original ball and source metric are preserved. Singleton/empty-direction geometry takes m0. The conclusion does not assert the same dimension for points outside the controlled half-ball or for an arbitrary disconnected open region.

## Proof route and quantifiers

1. Derive local compactness of the original open8R ball.
2. If X is subsingleton, every set has Hausdorff dimension0 and choose m0.
3. Otherwise use the nearby actual-chart-dimension producer ONCE at the original center p, with epsilon=R/2, to obtain q0 in the half-ball, positive r0 and actual chart ball contained in that half-ball, with dimension m. To support n0 uniformly, call the producer with upper bound n+1 (which is positive), then derive m<=n below from the original bound. This introduces no new geometric premise or direction at an isolated point.
4. The independently implemented radial dimension transfer with delta=min(R,r0)/2 gives `dimH(closedBall(p,R))<=dimH(ball(q0,r0))=m`. Inclusion gives the reverse. Because closedBall(p,R) is inside openBall(p,8R), its original upper bound now gives m<=n.
5. For ANY nonempty ambient open V contained in the half-ball, choose q in V and r>0 with ball(q,r) inside V. Radial dimension transfer sends the fixed original closed ball into that ball, proving m<=dimH V. The inclusion V subset closedBall(p,R) gives dimH V<=m. No net/cardinality limit, compact image, or continuity of the chosen radial family is required.

Root's new nearby producer must retain exactly q/r/m, chart-ball containment and its exact Hausdorff dimension; returning anchors or the entire chart is unnecessary for this consumer. Agent65's radial transfer has no finite-dimensional premise and works for EVERY positive target radius. Its exact original8R/half-ball domain is what makes both uses valid.

## Further scope, not yet implemented here

The conclusion directly supplies a fixed integer local lower bound on every small inner ball. Combining it with the actual-log lower inequality and the existing same-point tangent upper theorem on the half-ball can yield automatic tangent dimension=m at every original inner point; this no longer needs a separately assumed local lower bound. If m>1, the already proved exact-line dichotomy then gives all-pair geodesicity of the actual directions. This is a further consumer, not automatic nearby Euclidean tangent production.

For complete global geometry with finite Hausdorff upper bound and local comparison everywhere, the same method is plausible without new gradient theory: compare all balls about one center by the radial transfer, use a countable increasing exhaustion to identify dimH X, and transfer into every nonempty open set. For a general merely local open region, disconnected components need not have equal dimension; propagating the locally constant rank across a connected region and identifying the dimension of an uncountable union require the relevant connectedness/countable-exhaustion evidence. The bounded original half-ball conclusion avoids those additional assertions. No dimension homogeneity outside its domain or linear/topological dimension identity is claimed.

Only current GC-owned APIs and fixed mathlib were inspected. No changing PC snapshot was probed.


# Local Hausdorff dimension propagation through original radial contraction

One new public theorem, no definitions or private helpers, in temporary `/tmp/gc_LocalDimensionPropagation_body.lean`. Suggested canonical leaf: `DifferentialGeometry.Geometry.Comparison.LocalDimensionPropagation`. Minimal imports are accepted `Comparison.EightRadialContraction` and `Mathlib.Topology.MetricSpace.HausdorffDimension`.

## Exact contract

`Toponogov.dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer hcurves p hR hlocal hq hr` states

`dimH(closedBall(p,R)) <= dimH(ball(q,r))`

for EVERY q in B(p,R/2) and EVERY r>0. Its original inputs are complete ambient metric X, globally arbitrarily short continuous endpoint curves, R>0, local compactness of the original OPEN8R ball in its ambient subtype topology, and actual intrinsic local four-point comparison parameter1 on that ball. The latter is the curvature -1 convention. There is NO finite-dimensional premise, no properness assumption, no compactness or dimension bound on directions, and no tangent or chart premise.

The target ball is the original ambient ball at the SAME q and requested radiusr. Radiusr need not be small and the full target ball need not be contained in the original buffer. The proof maps into a smaller original ball contained in it. The original closed source ball is unchanged.

## Proof and dependency check

Choose delta=min(R,r)/2. It is strictly positive, strictly smaller than R and at most r. The accepted ORIGINAL radial contraction produces a map f from closedBall(p,R) into ball(q,delta) with

`(delta/sinh(2R))*dist(x,y) <= dist(f(x),f(y))`.

Since R and delta are positive, multiplying by sinh(2R)/delta gives the actual Antilipschitz bound. The original map and target values are retained. Its image lies in the SAME ball(q,r). Mathlib's `AntilipschitzWith.le_dimH_image` and Hausdorff-dimension monotonicity give the inequality; the actual subtype-coercion isometry identifies the dimension of the source subtype with the original ambient closed ball. This last step is proved directly with `Isometry.dimH_image`, requiring no additional custom dimension import.

No continuity of f is assumed or inferred. In particular this theorem does not claim that the image of a compact set under an arbitrary chosen radial map is compact. The AntiLipschitz dimension argument is valid without forward continuity. Extended Hausdorff dimensions, including infinity, are permitted by the statement.

The full accepted `EightRadialContraction` body was read before fixing this contract. Its existence theorem chooses actual endpoint segments once; its underlying chosen-family theorem retains those same paths, including zero arms, original endpoints and actual intrinsic8R comparison. The new proof does not change this producer, shorten its buffer or reprove comparison.

## Source checked and scope retained

KLP, *Lectures on Alexandrov spaces with curvature bounded below*, archived v1 July14 2026, PDF SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`:

- Exercise6.19 and its surrounding6.18/6.20 statements, printed69/PDF71, were freshly read. The source's full conclusion identifies linear, topological and Hausdorff dimensions of open subsets.
- The COMPLETE6.19 semisolution, printed137-138/PDF139-140, was freshly read. It directs the reader to radial maps from6.13/6.14 to propagate dimension into arbitrary open balls, with an additional compact-subset conclusion, then reuse6.18.
- The full6.13 chosen-geodesic proof, printed66-67/PDF68-69, and6.14's exact comparison inequalities in the semisolution printed137/PDF139 were read in the preceding actual-log task and reused unchanged here.

This theorem proves the bounded local Hausdorff-dimension propagation step directly. It does NOT claim compact image sets, global dimension homogeneity, linear/topological/Hausdorff dimension equality, an integer dimension, or automatic nearby Euclidean tangents. Those require their own precise producers. Source/version/errata distinctions are retained; no new external errata retrieval is claimed. References and the existing blueprint remain unchanged.

## Peer review

The source-review agent checked the proposed exact contract and route before implementation and is using this ABI in a separate integer-dimension consumer. Root independently read the entire new proof and reported PASS: positive delta, actual radial map, exact AntiLipschitz constant, original image inclusion and subtype isometry are all sound, with no hidden finite-dimensional premise. Final review is bound to the frozen body hash below.

## Concrete regressions and compiler evidence

Three new tests use original complete real/PUnit geometry, with actual short curves and intrinsic comparison already proved in four unchanged fixtures:

1. Real p7,R1,q29/4: for EVERY positive radiusr the original-input propagation theorem is applied. Both the source closed-ball and actual target open-ball dimensions are independently calculated as1 from Euclidean interior. This includes arbitrarily small radii and large target balls; q is off-center.
2. Original singleton source: for EVERY positive radiusr the original theorem is applied, and both actual dimensions are0. It requires no nontrivial direction or positive-dimensional source.
3. A genuine negative control: the real source closed ball has dimension1, while the target radius0 open ball is empty and has dimension0. Thus the proposed inequality is false without the positive-radius condition.

The minimal production and combined normal/lint checks are recorded below when completed. No Mathlib.Tactic umbrella or resource-limit override is used. Temporary source evidence is not a canonical build or shared-gate claim. All work here is in temporary files; no repository, reference, blueprint, accepted mathematical file or migration interface was written.

Final checks: minimal TWO-import production compile ACTUAL EXIT0 with empty log; complete three-test normal compile ACTUAL EXIT0 with empty log; selected lint ACTUAL EXIT0, no findings, exactly four ordered transitive reports, each using only propext, Classical.choice and Quot.sound. Root's full independent proof-read PASS is bound to the final body below. No canonical or shared build was run by this author.

Frozen evidence:
- `/tmp/gc_LocalDimensionPropagation_body.lean` SHA256 `30d84954ceb3b593a06db2c6ef00b9fc5f9d4bcca23b82963f3c4a4b8958ebca`
- `/tmp/gc_local_dimension_propagation_review_extra.lean` SHA256 `04cc5209acd7087606cdb1967363d411bb748962d561a36dfa73b46eb4137f02`
- `/tmp/gc_LocalDimensionPropagation_agent.lean` SHA256 `4e84d6cbe41571375e4b5b19aa402576aed559990b8bc8e9ec8d5a5ba65742db`
- `/tmp/gc_LocalDimensionPropagation_agent.log` SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `/tmp/gc_local_dimension_propagation_review_agent.lean` SHA256 `74e99a42ec8880aa9b399eb377c0eb61bd017149244f58520d6fec105d21981c`
- `/tmp/gc_local_dimension_propagation_review_agent.log` SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `/tmp/gc_local_dimension_propagation_review_lint.lean` SHA256 `bb006e4165fe33cccb3d5c47e74114dd11a1a76ba7c5b441feb793e870feac58`
- `/tmp/gc_local_dimension_propagation_review_lint.log` SHA256 `ccd72b4c6eee20ede005d765d939450bf6a7fd6d5588fcf5b7ec50c2c171dade`

Canonical review fixture order: direction_space_review_body; real_direction_obstruction_review_extra; actual_direction_chart_review_scaffold; direction_packing_open_review_extra; local_dimension_propagation_review_extra. Every file has `/tmp/gc_` prefix and `.lean` suffix, and occurs once. The four earlier fixture bodies are not new tests. Review-only imports add DirectionPackingOpen, EuclideanTangentChart, Topology.MetricSpace.SegmentCurves, and targeted Mathlib.Tactic.FinCases/Linter. Keep open Set Metric Filter Topology; open DifferentialGeometry.Geometry.Comparison.Toponogov; open scoped NNReal Topology.


# Nearby actual source balls with exact integer Hausdorff dimension

Two public theorems in Comparison.NearbyIntegerDimension retain the original complete, nontrivial metric source with arbitrarily short continuous curves, open U with dimH U<=n, n>=1, original point p in U, and an actual local four-point comparison neighborhood at p. For every epsilon>0 they produce ONE integer1<=m<=n, q in U intersect ball(p,epsilon), and r>0 such that ball(q,r) lies in that same set and its actual ambient Hausdorff dimension equals m. The intrinsic consumer transfers local comparison at the ORIGINAL center o of the constructed intrinsic ball B(o,L) through the accepted local metric equivalence. Its original ambient dimension bound and proximity epsilon are retained. No open intrinsic ball is assumed complete.

The entire accepted CenteredPairedChart and NearbyPairedChart proofs were reopened. This proof localizes exactly as NearbyPairedChart does, but retains CenteredPairedChart's open image W and onto HOMEOMORPHISM e with quantitative two-sided bounds. The chart is not an isometry. For F(z)=e(z) in Euclidean m-space, the given upper bound is LipschitzWith D and the positive inverse lower bound is AntilipschitzWith D, D=pairedChartDistortion n. The two Hausdorff image inequalities and the actual identity F''univ=W give dimH(ball(q,r))=dimH W. W contains e(q), and its openness gives dimH W=m by Mathlib Real.dimH_of_mem_nhds. Merely embedding into Euclidean m-space would not justify the lower bound; the retained open image and surjectivity are essential. No dimension conclusion is smuggled into a hypothesis, and no chart rank is equated with the original upper bound n.

## Source check and scope

The unchanged accepted centered_paired_chart.md and finite_local_structure.md records were read. They retain blueprint207A AC28 full lines3442-3515 and AC29 lines3508-3535 with remarks3537-3544, BGP1992 Remark6.9 printed22/PDF23, and the existing BBI/BGP correction qualifications. The current proof reuses those audited exact charts; it neither replaces their constants with a source citation nor changes their contracts. The mathematical references remain read-only.

KLP archived v1 July14 2026 SHA2563dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67: the complete6.18 proof and6.19/6.20 statements, printed69/PDF71, and complete6.19 semisolution printed137-138/PDF139-140 were freshly read from retained text /tmp/gc140/KLP.txt lines2933-2977 and5793-5800. The source's full linear/topological/Hausdorff identification is stronger. These two declarations extract exact local Hausdorff dimension from already proved actual charts. The separate radial-dimension theorem combines them into local Hausdorff homogeneity; it does not justify importing the remaining linear/topological conclusions. No fresh external errata retrieval is claimed; retained source-version and correction distinctions remain in force.

The exact Mathlib Hausdorff APIs were inspected at pinned revisionc55e6e786f49471c72fbddbec5415808896aec1e: LipschitzWith.dimH_image_le, AntilipschitzWith.le_dimH_image, Isometry.dimH_image for the source subtype, and Real.dimH_of_mem_nhds for the actual nonempty open Euclidean image. Root read both final production proofs in full. The independent full read passed and is recorded separately.

## Compiler and actual-input tests

Minimal normal production compilation actually exited0 with an empty log(session84113). Selected unusedArguments/simpNF/synTaut lint actually exited0(session27614), giving exactly two standard-three axiom reports and no diagnostics. An earlier proof draft needed an explicit scalar coercion in the Antilipschitz calculation; its contract never changed.

Three regressions apply the actual source producers:
1. Complete real source, unbounded U=(13,infinity), p14 and epsilon1/100, upper bound n2. The returned actual positive-radius ball is proved to have m=1, preserving its containment and original witnesses. Thus a loose upper bound does not become a false rank equality.
2. Original intrinsic real ball with center7, L8 and epsilon1/1000, again upper bound n2. The actual local comparison producer at the original center yields the returned ball with m=1 and all original containment data.
3. Original translated Euclidean plane, actual base distinct from center, U=B(center,16), epsilon1/100 and upper bound n3. The returned ball has m=2, preserving q,r and both containment conditions. The exact rank is checked independently by its Euclidean nonempty interior.

The final three-test normal compilation actually exited0 with an empty log(session27189). Selected lint actually exited0(session30692), giving exactly five ordered standard-three reports (two production, three new tests), without findings. Earlier test-only attempts required explicit intrinsic radius normalization8*1 and8*2; no production premise or proof changed. Eight inherited geometry fixture bodies occur exactly once and are not counted as new tests. No blanket Mathlib.Tactic import or resource override is used.

Only two public theorems are added; no definitions, private production helper, instance, admission, opaque declaration or new mathematical axiom. Frozen hashes and logs are in the accompanying freeze. No canonical registration/shared gate, blueprint pass, full migrated-root build or chapter completion is claimed by this temporary author record. Blueprint207, earlier mathematical leaves and migration interfaces remain unchanged.


# Independent review: nearby integer Hausdorff dimension

Verdict: PASS for both complete statements and proofs at the frozen body hash below. No mathematical or API defect found. This is a read-only independent review; I did not compile this leaf or execute its root-authored tests. The author supplied actual successful normal/lint runs. I inspected the current selected-lint log, which contains exactly the two public standard-three axiom reports and no diagnostics; this inspection does not replace an independent compiler run.

## Exact contract and proof

The ambient theorem retains the original complete, nontrivial metric space, actual global continuous almost-short curves, an open U with dimH U <= n and n >= 1, p in U, just one local curvature-minus-one four-point neighborhood at p, and arbitrary epsilon > 0. It produces 1 <= m <= n, q in U intersect B(p,epsilon), a positive radius r, containment of the entire original ambient B(q,r) in that intersection, and dimH B(q,r) = m. Neither the rank nor a chart, local compactness, Euclidean tangent, or integer-dimension conclusion is supplied as an input.

The proof intersects the actual comparison neighborhood with U and B(p,epsilon). Openness, nonemptiness, curvature restriction, and the dimension bound are all preserved. Original ambient completeness supplies precisely the complete closed-ball buffers required by the accepted CenteredPairedChart theorem; no completeness of the open intersection is introduced. The chosen chart's actual open target W and onto homeomorphism e are retained, unlike the deliberately weaker NearbyPairedChart output.

The chart map F = Subtype.val composed with e has Lipschitz and antilipschitz constants equal to the positive pairedChartDistortion n. The inverse estimate multiplies the accepted reciprocal lower bound by that positive constant; the subtype distances are the original ambient distances. Surjectivity identifies F(univ) with the entire W. The subtype inclusion is an isometry, so dimH(univ : Set B(q,r)) equals the ambient dimH B(q,r). The two actual metric inequalities give equality with dimH W. Finally W is an open neighborhood of e(q), since r > 0, so Real.dimH_of_mem_nhds gives the actual Euclidean rank m. A mere embedding or topological dimension invariance would not suffice; neither is being substituted here.

The intrinsic theorem assumes a local comparison neighborhood at the original center in the explicitly constructed intrinsic metric of B(o,L). The accepted local equivalence transfers precisely that local comparison premise to the original ambient metric, and the ambient theorem is applied with U = B(o,L), p = o. The resulting point, ball containment, and Hausdorff dimension remain ambient. There is no intrinsic open-ball completeness or global intrinsic curvature assumption.

No uniform positive chart radius, fixed rank shared by different choices, pointwise dimension equality at p, global dimension homogeneity, tangent Euclideanity, or exact source/tangent dimension equality is claimed. Nontriviality and n >= 1 are explicit; this leaf does not purport to handle singleton n = 0 by producing a positive rank.

## Sources and accepted dependencies actually read

Read both new bodies completely; reread the complete accepted CenteredPairedChart, NearbyPairedChart, and IntrinsicLocalComparison leaves. CenteredPairedChart retains the actual open Euclidean image and both metric bounds. IntrinsicLocalComparison proves its equivalence using the actual intrinsic-ball open embedding and equality of distances on a sufficiently small inner closed ball. Mathlib HausdorffDimension.lean lines 463-475 were reread: Real.dimH_of_mem_nhds reduces via a finite-dimensional linear equivalence and an actual contained positive-radius ball. Pinned Mathlib revision: c55e6e786f49471c72fbddbec5415808896aec1e.

Reread the accepted project records finite_local_structure.md, centered_paired_chart.md, and finite_local_structure_sources.json. These retain the blueprint207A AC07/AC29 and AC28 source checks, BGP1992 Remark6.9 printed22/PDF23, and the previous BBI/BGP/AKP source and errata distinctions. This leaf is a metric-dimension consumer of that proved chart; it introduces no new curvature comparison formula or stronger version of a source chart theorem.

Freshly reread the archived KLP extracted body /tmp/gc140/KLP.txt, Lecture6 sectionsF-G, Theorem6.18 and Exercise6.19 at printed68-69/PDF70-71, plus the 6.19 semisolution printed137-138/PDF139-140. The source distinguishes Hausdorff/linear/topological dimensions and treats equality across all nonempty open sets separately. The current leaf proves the nearby integer-dimensional-ball step from the accepted chart, not all of Theorem6.18 or Exercise6.19. Archived KLP identity reused from the retained source record: Kapovitch-Lebedeva-Petrunin, v1 July14,2026, PDF SHA256 3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67. No fresh raw-PDF hash or remote errata query is claimed. Existing source-version and correction qualifications remain unchanged.

## Frozen body and read dependency hashes

{
  "/tmp/gc_NearbyIntegerDimension_body.lean": "ac5e66e2f80ae1760f0e9a775e0d051cee89f1b2454afc34acf643a44e8c9088",
  "/Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_CHAPTER3_435_RC3/DifferentialGeometry/Geometry/Comparison/CenteredPairedChart.lean": "522416413b1803e86958e50fd6822a58d9e7fd110e8a0057302757893a29ae9f",
  "/Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_CHAPTER3_435_RC3/DifferentialGeometry/Geometry/Comparison/NearbyPairedChart.lean": "8a499a146f7b6f6b0aec004c4107b5f9894d23562f21e46d35aa8d6a9afab963",
  "/Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_CHAPTER3_435_RC3/DifferentialGeometry/Geometry/Comparison/IntrinsicLocalComparison.lean": "f2d75a6f7bc8f06da9a61f151a82fcf366d565e6b50639c5bfd637d62389bcef",
  "/Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_CHAPTER3_435_RC3/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean": "2399f41ce6460bd368c3bf6ad052d0c57e43472a93e02855a87c05f28b800abf"
}

## Independent original-input regression read

Read all three tests in `/tmp/gc_nearby_integer_dimension_review_extra.lean` completely. The real ambient fixture uses the unbounded original U=(13,infinity), p=14 and epsilon=1/100 with a deliberately loose n=2; the original intrinsic fixture uses p=7, L=8 and epsilon=1/1000; the plane fixture uses the actual translated plane, original comparison transported from the supplied intrinsic geometry, and a loose n=3. Each invokes the headline from actual geometry, retains the existential original q/r and containment, and independently identifies the produced integer by the dimension of a nonempty Euclidean open ball. Thus they do not assume the desired integer-dimension conclusion. The source bounds are independently proved by ambient Euclidean dimension. No test assumes a chart or tangent realization. All three full-read verdicts PASS. Root reported normal exit0 with empty log (session27189) and selected-lint exit0 with five standard-three reports (session30692); this remains author compiler evidence, not my independent execution.

Frozen regression SHA256: `220e8e28ad196beec99336b47609ebedee81fe553118b83cd81b07d4334c5180`.


# Original local integer Hausdorff dimension

One new public theorem in proposed Comparison.LocalIntegerDimension, with no definition, private helper, instance, admission or new mathematical axiom. Production body `/tmp/gc_LocalIntegerDimension_body.lean` SHA256 `99bf3c75e4d6ef80a07c98934ea3dfee2780bbc3817f0bd3f3e145d5b8f18fe7` is frozen. Minimal canonical imports are the new NearbyIntegerDimension and LocalDimensionPropagation leaves and accepted FiniteDimensionalLocalCompactness.

## Exact contract and proof

`exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH hcurves p hR hdim hlocal` uses the original complete metric source X, arbitrarily short continuous endpoint curves, R>0, Hausdorff upper bound `dimH(ball(p,8R))<=n` for ANY natural n, and actual intrinsic local comparison parameter1 throughout that open8R ball. It returns ONE natural m<=n with `dimH(closedBall(p,R))=m`, followed by the universal assertion that EVERY nonempty ambient-open V contained in ball(p,R/2) has `dimH V=m`. The actual source, ball and integer are retained; m is selected before V. No local compactness, dimension lower bound, tangent or direction hypothesis is supplied.

For a subsingleton source choose m0. Otherwise derive local compactness of the original open8R ball from the accepted finite-dimensional local comparison producer. Call the exact nearby chart-dimension producer with positive upper bound n+1 at the original center and epsilonR/2. This avoids imposing n>=1; the returned actual chart ball is inside the half-ball and has dimension m. The original radial-dimension transfer maps the fixed closed source ball into that chart ball, giving its dimension at most m. Inclusion of the chart ball into the original closed ball gives equality. Inclusion of the latter into the original open8R ball then proves m<=the ORIGINAL n. For any subsequent nonempty ambient-open V in the half-ball, select a point and a positive-radius ball contained in V, apply the same radial transfer, and use inclusion for the opposite dimension inequality.

The source chart is an onto homeomorphism with two-sided metric estimates, not an isometry. The proof needs its nonempty OPEN Euclidean image for equality of dimension. No continuity or compactness of the radial image is inferred. No finite-net limiting argument, dimension homogeneity premise or unproved local lower bound is used. In the nontrivial n0 case the actual chart/upper-bound facts provide the necessary incompatibility without manufacturing a direction on a singleton.

## Source and independent review

The full source assessment is `/tmp/gc_LocalIntegerDimension_source_assessment.md`: KLP archived v1 July14 2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`,6.18 full proof and6.19 statement printed69/PDF71, complete6.19 semisolution printed137-138/PDF139-140; exact6.13/6.14 radial route and normalization reused from the immediately preceding checked logarithm work. The stronger source linear/topological/Hausdorff identity and its additional compact-subset wording are not claimed. Existing accepted centered-chart/BGP correction records remain the source binding for the actual charts. Parameter1 means lower curvature bound-1. No reference, blueprint, migration interface or earlier mathematical file changed.

Root independently read the full final theorem and proof and found no issue. Agent65 independently read this body and its three full-output tests, plus the root nearby producer and its three tests, and recorded PASS at `/tmp/gc_LocalIntegerDimension_independent_read.md`. That record accurately claims read review only, not a duplicate compiler run. I independently read the entire propagation body and its real/PUnit/zero-radius regressions: the delta=min(R,r)/2 positivity and source/image domain checks are correct, the exact sinh factor gives the required AntiLip inequality, and the actual subtype-coercion isometry supplies the dimension identification. No issue found.

## Actual compiler and regression evidence

Final minimal combined source driver `/tmp/gc_LocalIntegerDimension_agent.lean` actually exited0 with an empty log (session96927). It concatenates the frozen new dependencies solely because canonical registration is pending. Selected unusedArguments/simpNF/synTaut lint `/tmp/gc_LocalIntegerDimension_lint.lean` actually exited0 (session84331), without findings and with exactly four standard-three axiom reports for all new source declarations. An earlier lint-driver command had invalid multi-name syntax; this was corrected to the project's usual selected lint command. The first dependency-copy run had a deprecated alias already corrected by its author; final drivers use the frozen current alias. Neither correction changes a mathematical contract.

Three concrete regressions invoke the full original-input theorem and retain its entire universal open-set conclusion:

1. Complete real source p7,R1 with loose original upper bound n2; the same returned m is identified as1 using the genuine closed-ball Hausdorff dimension. Every eligible original nonempty open V still receives this same m.
2. Original singleton PUnit, R1 and the sharp upper bound n0; the same returned m is0. No nontrivial direction or positive chart is assumed.
3. Original translated Euclidean plane, R2 and loose upper bound n3; the same returned m is identified as2 using its actual nonempty closed-ball interior, with the full universal V conclusion retained.

The final three-test normal driver `/tmp/gc_local_integer_dimension_review_agent.lean` actually exited0 with an empty log (session84032). Its selected lint driver actually exited0 (session44449), with no findings and exactly four standard-three reports (one new source theorem, three new tests). The test-only n0 coercion was normalized with norm_num before these final runs. The final test body SHA256 is `1db57bae946957ae9048067e02fb5c6e4f560a483d3ae7488b43c67a044c2379`. Eight inherited geometry fixtures appear once and are not counted as new tests. All explicit/transitive reports contain only propext, Classical.choice and Quot.sound. No blanket Mathlib.Tactic import or resource override is used.

Only temporary files and individual temporary Lean drivers were used. This record does not claim canonical registration, a shared gate, a blueprint audit, a full migrated-root/PDF/Overleaf build, global dimension homogeneity, automatic Euclidean tangents or completed Chapters3-4.


# Independent nearby-chart and local integer-dimension proof review

The reviewer read both complete production bodies and all six concrete test bodies. No production code or tests were edited or compiled independently by this reviewer. This is a mathematical/API/source/quantifier review; compiler and lint evidence for these two leaves belongs to their authors. The reviewer's separate local-propagation implementation and checks are bound in gc_LocalDimensionPropagation_freeze.json.

Final production-read verdict: PASS, no defects found.

## Nearby chart ball with actual integer Hausdorff dimension

The ambient theorem takes actual complete, nontrivial X, original global near-short curves, openU with dimH<=n for n>=1, a pointp inU, actual comparison in one open neighborhood ofp, and an arbitrary positiveepsilon. It intersects that actual comparison neighborhood with U and B(p,epsilon) and applies the accepted original centered paired-chart producer there.

Crucially the result retains the actual chart homeomorphism ONTO an actual open Euclidean setW, with both quantitative metric bounds. The proof defines the same map as an ambient Euclidean-valued map and proves that its full image is exactlyW by the actual homeomorphism's surjectivity. The upper Lipschitz bound and lower Antilipschitz bound give both Hausdorff-dimension inequalities. The source subtype dimension is identified by the actual inclusion isometry, and W has the Euclidean rankm dimension because it is open and contains the actual image of the chart center. Thus the original ball has dimH=m, with all original containment, positive-radius, and rank bounds retained.

No Euclidean tangent, integer dimension, desired chart-image dimension or full dimension equality is assumed as an auxiliary package. The Euclidean dimension calculation is a direct existing mathlib theorem applied to the ACTUAL nonempty open image. The intrinsic wrapper transfers only the original local comparison at the same center through the accepted intrinsic/ambient neighborhood equivalence and retains the original ball and arbitrarily small requested neighborhood.

## One integer for every original inner open set

The full original intrinsic8R consumer has complete X, near-short curves, R>0, dimH(B(p,8R))<=n for arbitrary n, and original intrinsic local comparison. It does not ask for local compactness separately: that instance is derived from accepted finite-dimensional comparison.

The subsingleton branch chooses m0 and handles all sets directly, including n0. In the nontrivial branch the nearby chart producer is called with upper bound n+1 solely to satisfy its positive-rank input. The chart ball lies inside the SAME original half-radius ball. The actual local-propagation theorem sends the entire original closedBall(p,R) into that chart ball without dimension loss; reverse inclusion gives the converse inequality. This yields one m equal to dimH(closedBall(p,R)). Its upper bound is then proved against the ORIGINAL n using the actual inclusion closedBall(p,R) into B(p,8R); n+1 is not leaked into the public conclusion.

That SAME m is selected before the universal quantifier overV. For every nonempty AMBIENT-open V contained in B(p,R/2), choose an original z inV and a positive-radius original ball insideV. The propagation theorem gives the dimension lower bound into that ball and then intoV. The upper bound is ordinary inclusion into the original closed ball. No m, source metric, chart or target is reselected depending onV. Nonemptiness is necessary for positive m since Hausdorff dimension of the empty set is0.

## Source comparison and remaining scope

KLP archived v1 July14 2026, SHA2563dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67: Exercise6.19 and surrounding6.18/6.20 at printed69/PDF71, full6.19 semisolution printed137-138/PDF139-140 were freshly read for the propagation task. The source uses radial dimension transfer and additional compact-subset/global dimension arguments. This development instead combines the already proved actual open-image chart with radial Hausdorff-dimension transfer. It proves bounded local integer Hausdorff dimension and its constancy on every specified inner open set. It does not claim global homogeneity, linear/topological dimension identification, compactness of an arbitrarily chosen radial image, or an automatic Euclidean tangent. No continuity of the chosen radial map is used. Source/version/errata distinctions remain unchanged; no new external source or errata check is claimed.

## Concrete test read

The three nearby-chart tests use original unbounded realU=(13,infinity), intrinsic real geometry near7, and translated plane geometry. All retain the chosen original point, positive radius, full ball containment and dimension conclusion, and identify actual rank1 or2 using Euclidean open-ball dimension. The supplied upper bounds2 or3 are intentionally loose, so no equality to the chosen bound is assumed.

The three local-integer tests apply the FULL source theorem to real upper bound2, plane upper bound3, and singleton upper bound0. They identify m1, m2 or m0 from the actual closed-ball dimension (or the actual zero upper bound) while retaining the SAME existential witness and ENTIRE universal nonempty-open-set output. None substitutes a selected V for the universal conclusion, fabricates a lower bound, or claims an upper bound implies actual dimension. These are genuine original-source applications.

Frozen read snapshots:
- `/tmp/gc_NearbyIntegerDimension_body.lean` SHA256 `ac5e66e2f80ae1760f0e9a775e0d051cee89f1b2454afc34acf643a44e8c9088`
- `/tmp/gc_LocalIntegerDimension_body.lean` SHA256 `99bf3c75e4d6ef80a07c98934ea3dfee2780bbc3817f0bd3f3e145d5b8f18fe7`
- `/tmp/gc_nearby_integer_dimension_review_extra.lean` SHA256 `220e8e28ad196beec99336b47609ebedee81fe553118b83cd81b07d4334c5180`
- `/tmp/gc_local_integer_dimension_review_extra.lean` SHA256 `1db57bae946957ae9048067e02fb5c6e4f560a483d3ae7488b43c67a044c2379`

No compiler/lint run for these two leaves is claimed by this independent read record. The authors' final normal/lint receipts remain separate. No repository file, accepted mathematical leaf, source reference, blueprint or migration interface was modified.


```lean
import DifferentialGeometry.Geometry.Comparison.LocalDimensionPropagation
import DifferentialGeometry.Geometry.Comparison.NearbyIntegerDimension
import DifferentialGeometry.Geometry.Comparison.LocalIntegerDimension
import DifferentialGeometry.Geometry.Comparison.DirectionPackingOpen
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentChart
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalDirections
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linter

open Set Metric Filter Topology InnerProductGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped NNReal Topology

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

local instance : LocallyCompactSpace (ball (7 : ℝ) (8 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

theorem original_real_dimension_propagation_every_positive_radius {r : ℝ} (hr : 0 < r) :
    dimH (closedBall (7 : ℝ) 1) ≤ dimH (ball (29 / 4 : ℝ) r) ∧
    dimH (closedBall (7 : ℝ) 1) = 1 ∧ dimH (ball (29 / 4 : ℝ) r) = 1 := by
  refine ⟨dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer chart_real_curves 7
    (R := 1) (by norm_num) chart_real_intrinsic_local
    (by norm_num [mem_ball, Real.dist_eq] : (29 / 4 : ℝ) ∈ ball 7 (1 / 2)) hr, ?_, ?_⟩
  · rw [Real.dimH_of_mem_nhds (closedBall_mem_nhds (7 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    simp
  · rw [Real.dimH_of_mem_nhds (ball_mem_nhds (29 / 4 : ℝ) hr)]
    simp

theorem original_singleton_dimension_propagation_every_positive_radius {r : ℝ} (hr : 0 < r) :
    dimH (closedBall (PUnit.unit : PUnit.{1}) 1) ≤ dimH (ball (PUnit.unit : PUnit.{1}) r) ∧
    dimH (closedBall (PUnit.unit : PUnit.{1}) 1) = 0 ∧
    dimH (ball (PUnit.unit : PUnit.{1}) r) = 0 := by
  refine ⟨dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer singleton_short_curves
    PUnit.unit (R := 1) (by norm_num) singleton_intrinsic_local
    (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)) hr, ?_, ?_⟩
  · exact Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)
  · exact Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)

theorem zero_radius_dimension_propagation_fails :
    ¬ dimH (closedBall (7 : ℝ) 1) ≤ dimH (ball (29 / 4 : ℝ) 0) := by
  have hdim : dimH (closedBall (7 : ℝ) 1) = 1 := by
    rw [Real.dimH_of_mem_nhds (closedBall_mem_nhds (7 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    simp
  rw [hdim, ball_zero, dimH_empty]
  norm_num

end GCDirectionSpaceReview

namespace GCDirectionSpaceReview

theorem actual_unbounded_real_nearby_integer_dimension :
    ∃ m : ℕ, m = 1 ∧ m ≤ 2 ∧ ∃ q ∈ Ioi (13 : ℝ) ∩ ball (14 : ℝ) (1 / 100),
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ Ioi (13 : ℝ) ∩ ball 14 (1 / 100) ∧
        dimH (ball q r) = m := by
  have hdim : dimH (Ioi (13 : ℝ)) ≤ (2 : ℕ) :=
    (real_dim_le_one _).trans (by norm_num)
  obtain ⟨m, hm, hmn, q, hq, r, hr, hsub, hd⟩ :=
    exists_ball_dimH_eq_nat_near_of_local_comparison chart_real_curves isOpen_Ioi
      (n := 2) (by norm_num) hdim (p := 14) (by norm_num)
      ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ _⟩
      (ε := 1 / 100) (by norm_num)
  have hmone : m = 1 := by
    have h := Real.dimH_of_mem_nhds (ball_mem_nhds q hr)
    have heq : (m : ENNReal) = 1 := hd.symm.trans (by simpa using h)
    exact_mod_cast heq
  exact ⟨m, hmone, hmn, q, hq, r, hr, hsub, hd⟩

theorem actual_real_intrinsic_nearby_integer_dimension :
    ∃ m : ℕ, m = 1 ∧ m ≤ 2 ∧ ∃ q ∈ ball (7 : ℝ) 8 ∩ ball 7 (1 / 1000),
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ ball 7 8 ∩ ball 7 (1 / 1000) ∧
        dimH (ball q r) = m := by
  have hdim : dimH (ball (7 : ℝ) 8) ≤ (2 : ℕ) :=
    (real_dim_le_one _).trans (by norm_num)
  obtain ⟨m, _, hmn, q, hq, r, hr, hsub, hd⟩ :=
    exists_ball_dimH_eq_nat_near_of_intrinsic_local_comparison chart_real_curves 7
      (L := 8 * 1) (ε := 1 / 1000) (by norm_num) (by norm_num)
      (n := 2) (by norm_num) (by simpa only [mul_one] using hdim)
      (chart_real_intrinsic_local ⟨7, mem_ball_self (by norm_num)⟩)
  have hmone : m = 1 := by
    have h := Real.dimH_of_mem_nhds (ball_mem_nhds q hr)
    have heq : (m : ENNReal) = 1 := hd.symm.trans (by simpa using h)
    exact_mod_cast heq
  exact ⟨m, hmone, hmn, q, by simpa only [mul_one] using hq, r, hr,
    by simpa only [mul_one] using hsub, hd⟩

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

theorem actual_plane_nearby_integer_dimension :
    ∃ m : ℕ, m = 2 ∧ m ≤ 3 ∧ ∃ q ∈ ball center 16 ∩ ball base (1 / 100),
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ ball center 16 ∩ ball base (1 / 100) ∧
        dimH (ball q r) = m := by
  have hdim : dimH (ball center 16) ≤ (3 : ℕ) := by
    have h := dimH_mono (subset_univ (ball center 16))
    rw [Real.dimH_univ_eq_finrank] at h
    have hh : dimH (ball center 16) ≤ (2 : ENNReal) := by simpa [Plane] using h
    exact hh.trans (by norm_num)
  have hbase : base ∈ ball center 16 := by
    change dist base center < 16
    rw [base_center_dist]
    norm_num
  have hlocal := (exists_local_fourPointComparison_intrinsicBall_iff plane_short_curves
    center (by norm_num : (0 : ℝ) < 8 * 2) ⟨base, by norm_num at *; exact hbase⟩).mp
    (plane_intrinsic_local ⟨base, by norm_num at *; exact hbase⟩)
  obtain ⟨m, _, hmn, q, hq, r, hr, hsub, hd⟩ :=
    exists_ball_dimH_eq_nat_near_of_local_comparison plane_short_curves isOpen_ball
      (n := 3) (by norm_num) hdim hbase hlocal (ε := 1 / 100) (by norm_num)
  have hmtwo : m = 2 := by
    have h := Real.dimH_of_mem_nhds (ball_mem_nhds q hr)
    have heq : (m : ENNReal) = 2 := hd.symm.trans (by simpa [Plane] using h)
    exact_mod_cast heq
  exact ⟨m, hmtwo, hmn, q, hq, r, hr, hsub, hd⟩

end GCPlaneDirectionPackingReview

namespace GCDirectionSpaceReview

theorem original_real_one_integer_for_all_inner_open_sets :
    ∃ m : ℕ, m = 1 ∧ m ≤ 2 ∧ dimH (closedBall (7 : ℝ) 1) = m ∧
      ∀ V : Set ℝ, IsOpen V → V.Nonempty → V ⊆ ball 7 (1 / 2) → dimH V = m := by
  have hdim : dimH (ball (7 : ℝ) (8 * 1)) ≤ (2 : ℕ) :=
    (real_dim_le_one _).trans (by norm_num)
  obtain ⟨m, hm, hclosed, hV⟩ :=
    exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH
      chart_real_curves 7 (R := 1) (by norm_num) hdim chart_real_intrinsic_local
  have hactual : dimH (closedBall (7 : ℝ) 1) = 1 := by
    rw [Real.dimH_of_mem_nhds (closedBall_mem_nhds (7 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    simp
  have hmone : m = 1 := by exact_mod_cast hclosed.symm.trans hactual
  exact ⟨m, hmone, hm, hclosed, hV⟩

theorem original_singleton_zero_integer_for_all_inner_open_sets :
    ∃ m : ℕ, m = 0 ∧ m ≤ 0 ∧ dimH (closedBall (PUnit.unit : PUnit.{1}) 1) = m ∧
      ∀ V : Set PUnit.{1}, IsOpen V → V.Nonempty →
        V ⊆ ball PUnit.unit (1 / 2) → dimH V = m := by
  have hdim : dimH (ball (PUnit.unit : PUnit.{1}) (8 * 1)) ≤ (0 : ℕ) := by
    rw [Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)]
    norm_num
  obtain ⟨m, hm, hclosed, hV⟩ :=
    exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH
      singleton_short_curves PUnit.unit (R := 1) (by norm_num) hdim singleton_intrinsic_local
  exact ⟨m, Nat.eq_zero_of_le_zero hm, hm, hclosed, hV⟩

end GCDirectionSpaceReview

namespace GCPlaneDirectionPackingReview

theorem original_plane_one_integer_for_all_inner_open_sets :
    ∃ m : ℕ, m = 2 ∧ m ≤ 3 ∧ dimH (closedBall center 2) = m ∧
      ∀ V : Set Plane, IsOpen V → V.Nonempty → V ⊆ ball center (2 / 2) → dimH V = m := by
  have hdim : dimH (ball center (8 * 2)) ≤ (3 : ℕ) := by
    have h := dimH_mono (subset_univ (ball center (8 * 2)))
    rw [Real.dimH_univ_eq_finrank] at h
    have hh : dimH (ball center (8 * 2)) ≤ (2 : ENNReal) := by simpa [Plane] using h
    exact hh.trans (by norm_num)
  obtain ⟨m, hm, hclosed, hV⟩ :=
    exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH
      plane_short_curves center (R := 2) (by norm_num) hdim plane_intrinsic_local
  have hactual : dimH (closedBall center 2) = 2 := by
    simpa [Plane] using
      Real.dimH_of_mem_nhds (closedBall_mem_nhds center (by norm_num : (0 : ℝ) < 2))
  have hmtwo : m = 2 := by exact_mod_cast hclosed.symm.trans hactual
  exact ⟨m, hmtwo, hm, hclosed, hV⟩

end GCPlaneDirectionPackingReview

#lint- only unusedArguments simpNF synTaut
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_ball_dimH_eq_nat_near_of_local_comparison
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_ball_dimH_eq_nat_near_of_intrinsic_local_comparison
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH
#print axioms GCDirectionSpaceReview.original_real_dimension_propagation_every_positive_radius
#print axioms GCDirectionSpaceReview.original_singleton_dimension_propagation_every_positive_radius
#print axioms GCDirectionSpaceReview.zero_radius_dimension_propagation_fails
#print axioms GCDirectionSpaceReview.actual_unbounded_real_nearby_integer_dimension
#print axioms GCDirectionSpaceReview.actual_real_intrinsic_nearby_integer_dimension
#print axioms GCPlaneDirectionPackingReview.actual_plane_nearby_integer_dimension
#print axioms GCDirectionSpaceReview.original_real_one_integer_for_all_inner_open_sets
#print axioms GCDirectionSpaceReview.original_singleton_zero_integer_for_all_inner_open_sets
#print axioms GCPlaneDirectionPackingReview.original_plane_one_integer_for_all_inner_open_sets
```

# Original8R contraction, covering, actual hinges and conditional chart

Six public theorems in four leaves consume the full original8R comparison. Original AC03 keeps the SAME supplied radial family and exact delta/sinh(2R) coefficient. Original AC04 has the exact ceiling bound independent of chart radius. Actual canonical hinge comparison is proved for the SAME supplied hinge, including zero-arm model-side cases. The source-facing conditional AC12 chart now derives the comparison it needs from actual intrinsic8R geometry; tangent/direction compatibility and the angular obstruction remain explicit inputs. A smaller neighborhood of q keeps every used hinge center inside the proved domain. No claim of nearby tangent or obstruction production is made. Earlier mathematical leaves and blueprint207 remain unchanged.

# Original eight-radius AC03 and AC04

Three public theorems, no new definitions or private lemmas. These are new source-facing original-radius leaves, leaving all accepted scalar, contraction, comparison and net statements unchanged.

## Source and exact contract

Fresh reading of frozen207A AC03 lines2193–2230 and AC04 lines2232–2269, including the full coefficient calculation and exact packing constant. Blueprint SHA256277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b. Full originalAC02 and its actual intrinsic-domain clause were reread and independently reviewed immediately before this consumer; see `/tmp/gc_OriginalEightNestedRadial_independent_review_record.md` for all four frozen source-body hashes and proof-scope review.

The BBI10.6.2 comparison, printed370/PDF385, and retained general-curvature normalization qualification are reused from accepted RadialContraction/LocalChartCovering source records. The present estimate is proved at curvature-1, exactly as blueprintAC03. No statement for arbitrary negative curvature is inferred by forgetting the sqrt(kappa) scaling. No new remote errata check is claimed; original KL§3.3/AKP retained-source and errata checks are those attached to the new originalAC02 proof.

Accepted bodies read in full: RadialContractionEstimate, FiniteRadialComparison, RadialModel, RadialContraction, LocalChartCovering, RadialChartNet, RadialBall, SegmentConcatenation. The scalar half-angle/cosh contraction and finite-box/greedy net proof are reused, not duplicated or assumed under new labels.

Inputs are complete ambient metric X, actual arbitrarily short curves, local compactness ONLY of openB(o,8R), R>0, and local four-point comparison at curvature-1 in its ACTUAL intrinsic metric. Source finite-dimensionality is not used once those assumptions and the chart are supplied, so it is validly omitted. No global comparison on2R, larger256R source region, properness of X, or completeness of the open ball is substituted.

## Same-path AC03

`radial_contraction_of_chosen_isometries_intrinsic_8_buffer` takes ANY supplied original isometric family gamma_x:[0,d(q,x)]→X, for x in the original closedR-ball, with exactly endpointsq,x. The conclusion uses the literal map

h(x)=gamma_x((delta/(2R))*d(q,x)), 0<delta<R, q in openB(o,R/2).

The public let-expression records the exact map and its actual interval arguments. It proves h(x) in openB(q,delta) and

d(h(x),h(y)) >= (delta/sinh(2R))*d(x,y).

Zero original arms q=x or q=y are handled first by the exact original radial identities and delta/sinh(2R)<=delta/(2R). For positive arms, the full same-path originalAC02 model-side theorem applies at both fractionally shortened original parameters. The actual large triangle satisfies the model-side inverse identity, and both model triangles satisfy the accepted exact hyperbolic cosine law. The scalar `Real.radial_side_lower_of_cosine_laws` then gives precisely delta/sinh(2R). No continuity of the chosen family or its contraction is needed or asserted; individual supplied paths are actual isometries.

`exists_radial_contraction_of_intrinsic_8_buffer` obtains actual original endpoint geodesics from accepted localized compactness/short curves and normalizes them using the actual segment conversion theorem, including coincident endpoints. It applies the preceding same-path theorem. Source global properness is not needed.

## Exact AC04

`exists_closedBall_net_of_intrinsic_8_comparison_and_chart` retains the original supplied centered chart phi:B(q,delta0)→Eucl(Fin n), with n>0, L>=1, arbitrarydelta0>0, and both ambient distance bounds. It chooses delta=min(R,delta0)/2, obtains the original8R contraction, and applies the already proved radial-chart net core. The resulting finset lies in the original closedR-ball and covers it with STRICT distance<epsilon. Its exact bound is

(1+Nat.ceil(4*L^2*sqrt(n)*sinh(2R)/epsilon))^n.

There is no chart-radius term, volume/noncollapse assumption, implicit continuity, or target compactness. The singleton/n=0 branch belongs to the existing separate package; this original AC04 statement explicitly requires n>0.

## Frozen production and checks

- `/tmp/gc_OriginalEightRadialContraction_body.lean` SHA256 `a956121bfb4c02d5566bc18afb9fb6787bfde3ff6b6084034b6a03806f6077e4`.
- `/tmp/gc_OriginalEightChartCovering_body.lean` SHA256 `28d2184ebf72eec3380aa873c8b3e84804efdf16f5bf94e0d1eea8b91d06d1bc`.
- `/tmp/gc_OriginalEightChartCovering_agent.lean` SHA256 `7c1bef19669fb4733bc933fc53de59d904fe10b9f033a3619387c36d5d0fcbc2`.

The minimal combined production driver compiled exit0 with empty log. The final lint driver `/tmp/gc_OriginalEightChartCovering_lint.lean` compiled exit0; `unusedArguments simpNF synTaut` is silent and all three public theorems have exactly propext, Classical.choice, Quot.sound. No admissions, extra axioms, resource-limit changes or conclusion-shaped hypothesis packages were introduced. Lean4.35.0-rc3; Mathlib c55e6e786f49471c72fbddbec5415808896aec1e.

Natural canonical imports: the contraction leaf imports new originalEightNestedRadial, accepted Analysis.SpecialFunctions.Trigonometric.RadialModel, MetricSpace.RadialBall and MetricSpace.SegmentConcatenation. The chart-covering leaf imports this new contraction and accepted MetricSpace.RadialChartNet. Root selects final natural module names at integration.

Half_angle independently read both complete bodies and reported proof/scope pass. Frozen concrete regression body `/tmp/gc_original_eight_contraction_review_body.lean` SHA256 `5c6be964d9456c8d31c45244d9e4be1efef3433d5d569253fb00132d70acecfb`; combined driver `/tmp/gc_original_eight_contraction_review_agent.lean` SHA256 `b4b9ab1fbf4e15bdcbf68c4d57a5b3e3dd1db1e412e884d0e8a05ed932dd7c4d`. All FOUR regression theorems compile/lint exit0, with no warnings and only the standard three axioms.

The actual source is complete real line, center0,R1,q1/4; local comparison in the actual intrinsic open(-8,8) metric is proved from explicit real short curves and literal0/pi comparison angles. The supplied original path to each x in[-1,1] is gamma_x(s)=q+s if x>=q, gamma_x(s)=q-s otherwise. Isometry and both exact endpoints are proved for every original x, includingx=q. The theorem is applied atdelta1/2 and its SAME returned expression is shown to be exactly h(x)=1/4+(x-1/4)/4 for everyx. A separate test retains the zero original arm h(q)=q.

The net test applies the full original8R theorem for EVERY delta0>0 and epsilon>0 to the actual original centered rank1 chart phi(u)=single0(u-1/4). Its exact distance preservation is proved. It returns an internal net of[-1,1] with exact cardinal bound1+ceil(4*sinh2/epsilon), with no delta0 anywhere in the conclusion. No synthetic conclusion or unproved original geometric premise is supplied.

The real-geometry fixture is reused verbatim from the previously independently checked original8 midpoint test up to its actual-local-comparison helper; all new contraction/chart tests are separate. Repository, blueprint, source archive, and shared build artifacts remain unchanged by this subtask.

# Original8R comparison for the same canonical minimizing hinge

Two public theorems, no private declarations or definitions, in `/tmp/gc_IntrinsicEightHingeComparison_body.lean` (SHA256 edae3d79d48ef256e6f7efe4bdd410df225f0050e58435eb4bc125ce7b03bc4c). Namespace Metric.MinimizingHinge. Proposed minimal canonical imports: DifferentialGeometry.Geometry.Comparison.OriginalEightNestedRadial and DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison. The former already transitively provides HingeModel and CanonicalLocalAngle through the actual midpoint comparison forest.

`H.comparisonAngle_le_of_intrinsic_8_buffer hcurves o hκ hR hlocal hcenter hp hq ha hb` proves the original endpoint comparison angle is at most H.germAngle κ. X is complete with actual arbitrarily short curves; R,κ>0; only original open ball(o,8R) is locally compact and has local comparison in its actual intrinsic metric. The supplied actual H has center in open ball(o,R/2), both original endpoints in closedBall(o,R), and positive arms for this angle statement. It is the SAME H, with its actual left/right isometries and original canonical germ angle, not a replacement hinge.

`H.modelSide_ge_dist_of_intrinsic_8_buffer hcurves o hκ hR hlocal hcenter hp hq` proves dist(p,q)≤H.modelSide κ without any positive-arm hypotheses. If the center is either endpoint, the accepted exact zero-arm model identities discharge the result. Otherwise the positive-arm equivalence between angle and model-side comparison applies.

The proof derives an actual ambient open comparison neighborhood at H.center from the original intrinsic local-comparison premise via IntrinsicLocalComparison's established local metric equality. CanonicalLocalAngle then gives the genuine TWO-parameter right-hand limit of the actual comparison angles of IccExtend H.left and H.right to the canonical germ angle. Full original8R nested radial comparison applies to these same arms for all sufficiently small positive parameters. Passing its lower inequality to that limit yields the result. This uses a true local angle limit, not an assumed calibration or an arbitrary chosen angle; no global comparison is claimed for the incomplete open ball. Domain endpoint equality and all Icc extension evaluations are exact. Curvature normalization is −κ, with κ>0; κ=1 is the original application.

Fresh source reading: frozen blueprint207A AC02 full2142–2190, AC09 full2470–2508, AC11/12 full2600–2692. AC09 explicitly requires comparison for the actual controlled hinge; AC12 requires the same comparison at chart points for its actual anchors/points. The new theorem produces that comparison where its stated original-radius placement conditions hold, while tangent/direction identification and angular obstruction remain separate inputs. Root's chart wrapper will restrict its domain before applying this theorem; no claim of comparison for arbitrary ballR centers is made.

Pinned AKP vol1 commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, `defs-CBB.tex` freshly read307–378, especially `thm:defs_of_alex` / `angle` and the point-on-side→angle proof365–372, and418–447 (`cor:monoton`, `cor:monoton:2-sides`, `cor:monoton:sup`). The source identifies the angle as the supremum/limit of monotonically increasing shortened comparisons and states equivalence with model-side comparison. Its global theorem is not invoked on an incomplete region; the full original8R radial theorem and accepted local canonical-limit theorem implement the needed localized argument. Source SHA256 b80b54fafc6e30cbac121880c1b80265ee62afcd90d8a3ab77c0deef1a0e1f9c. Blueprint SHA256 277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b. Previously retained AKP/KL definitions/errata checks from original_eight_comparison.md are reused; no new external freshness claim.

Actual Lean definitions and proofs inspected: MinimizingHinge structure and radial/dist fields; HingeModel.germAngle and modelSide, zero-arm identities and comparisonAngle_le_iff_dist_le_modelSide; CanonicalGermAngle's actual product-filter limsup; CanonicalLocalAngle.tendsto_germComparisonAngle_of_local_fourPointComparison; LocalGermAngle.exists_local_comparisonAngle_limit; and IntrinsicLocalComparison.exists_local_fourPointComparison_intrinsicBall_iff. This fixes the representation and metric conventions explicitly.

Combined driver `/tmp/gc_IntrinsicEightHingeComparison_agent.lean` SHA256 d427cdb2c7861a538f9d23fc7c7175ae9c64f5a309817bd1105e4423d6ab5965 compiled silently exit0. Final `/tmp/gc_IntrinsicEightHingeComparison_lint.lean` compiled exit0 with silent unusedArguments/simpNF/synTaut, and both public theorems have only propext, Classical.choice, Quot.sound. Half_angle independently read the full same-H proof and reported it sound, including the actual joint germ limit and both zero-arm branches. Concrete independent same-H/degenerate applications are being added by half_angle after its full02 regression; no such application is claimed complete in this record yet. No repository changes, shared build, source changes, or migration probes were made by this subagent.

Peer regression completion: half_angle subsequently froze four actual same-H tests at `/tmp/gc_original_eight_hinge_review_body.lean` SHA256 ed7847320a9777f93a15ca25fc0ec1d48d470e7c882d3f4e423b9d56d7f8a9f7; combined driver SHA256 340897d32cc016a53ccd4aa8b17b3806ed36f14ebe41fb39df8d28b11b3e1717. Reported production-plus-tests compile/lint exit0 with standard3 axiom closures. Independent details are in `/tmp/gc_OriginalEightHinge_independent_review_record.md`; root received the freeze directly. This supersedes the pending-test status above.

# Original intrinsic8R conditional uniform strut chart

One public theorem, no definitions, binds the existing conditional chart assembly to actual geometric comparison from the original intrinsic8R source. Inputs retain complete ambient X, actual arbitrarily short curves, local compactness of the original open ball(p,8R), and local four-point comparison in its actual intrinsic metric. The given Euclidean dense direction/representative family and comparison-angle limits, local angular obstruction at the actual dimension m, and actual canonical-germ compatibility of chosen directions/hinges remain explicit. The earlier additional model-side comparison premise is removed and proved for each hinge actually used.

Root freshly read blueprint207A AC09–12 full2469–2690, especially cor:alexandrov-uniform-chart-part2640–2688 and the remaining-structural-work paragraph. Source SHA256277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b. Root read the full accepted UniformStrutChart and SimplexStrutNeighborhood proof bodies and the new same-H intrinsic8R producer, whose source record is separate. The previously checked AKP15.10/15.12 printed/PDF233–235 and KLP corresponding proof/semisolution are reused unchanged: actual tangent production and the localized obstruction remain genuine inputs, not consequences fabricated from dimH alone. No new external or errata retrieval is claimed.

The previous conditional metric assembly requests comparison for every triple in its control ball. Applying it directly to ball(p,R) would exceed the actual new producer's center-in-ball(p,R/2) scope. Instead let delta=min(R/2,R/2-dist(q,p))>0. Every point of ball(q,delta) lies in the original ball(p,R/2), hence also ball(p,R). Restrict the original dependent direction family and the chosen directions through the literal subtype inclusion. For each supplied actual hinge in this smaller ball, the new source-geometric theorem proves model comparison using its original center/endpoints/paths. The old chart assembly is then invoked with center q and control radius delta. Its resulting s<delta/8<=R/8 and radius rho keep the exact original selected family, common endpoints, centered ordered distance vector and Euclidean padding E. All original-region containment and exact L(n)=max(sqrt(n),2/sin(1/(8n))) bounds, basepoint zero, and homeomorphism to the same range are preserved.

This is source-facing conditional AC12 given the explicitly exposed tangent/direction compatibility and angular obstruction. It neither constructs the tangent objects nor proves the original source-dimensional obstruction. The smaller radius can depend on q as the original conclusion permits. No change to blueprint207, earlier mathematical leaves or migration interfaces is made.

Minimal canonical imports: Comparison.IntrinsicEightHingeComparison and Comparison.UniformStrutChart. The combined temporary driver with the frozen hinge body compiled exit0 with an empty log. Independent review/regression and lint evidence are added after freezing.

Frozen body SHA256 503cd4a5e2d451da4ca5b5ac34fe2b857d54d401e76fdf3962d60b7602d10696. Combined driver SHA256 58abba3667c4060887470100a270252f45f8a2f2fb8aafb02e4ee57c7c514317. Final selected lint driver exited0, with silent unusedArguments/simpNF/synTaut and exactly propext, Classical.choice, Quot.sound. Independent full source/body review by same_lines passes; original-input regression is being finalized separately.


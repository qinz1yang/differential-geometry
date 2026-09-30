# Full AC87: uniform overlapping-cone splitting

Two public theorems in two leaves prove vanishing-KL stability of pointed convergence and the full uniform splitting conclusion from the ORIGINAL two cone approximations. The tolerance is chosen for n and delta before all spaces, points, models and maps. The original source needs only a metric. Only the FIRST cone model requires complete nonnegative length geometry and dimension at most n; the second needs only its metric and actual cone maps. This stronger statement includes every hypothesis of written AC87 by specialization. Its final factor lives in the source universe and the returned whole-source KL splitting has its own target coverage.

The proof extracts only the first geometric model sequence. Actual first KL maps transfer convergence to the original sources. Moving the marked points inside that SAME proper limit retains separation one. Actual second KL maps transfer convergence of the second cone models directly to this SAME newly pointed space, where AC85 supplies the second cone. AC84's actual line and the accepted aligned product split this space; exact-limit transfer contradicts failure of delta splitting on the original sources. Thus the written second extraction/isometric-identification route is replaced explicitly without replacing the target or weakening the conclusion. No strainer theorem, compatibility theorem, explicit modulus or tolerance monotonicity is used.

The candidate source/contract audit follows. Final canonical-leaf acceptance and original-input tests are recorded separately. Blueprint207 and migration interfaces are unchanged.

# AC87 uniform overlapping-cone splitting: temporary acceptance record

## Frozen implementations

- `/tmp/gc_VaryingKleinerLottConvergence_body.lean`, SHA256 `dde4b9fdc28bd0dab4398dac990fc52b7ede27ab4e6c743a78759e65bf865dee`: one public theorem `GC.MetricGeometry.pointedGHConverges_iff_of_kleinerLott_sequence` and one private composition helper.
- `/tmp/gc_OverlappingConeSplitting_body.lean`, SHA256 `8efb2086df4629e2a596514f2266954128074dea26f1e2e9c811122eb5abbf6d`: one public theorem `GC.MetricGeometry.exists_overlapping_cone_splitting_parameter` (111 lines).
- `/tmp/gc_OverlappingConeSplitting_agent.lean`, SHA256 `be528d96071058a21fb0f4f567ea7b34670a15a941f87066ada8e78076b15537`, compiles with an empty log, actual exit 0, without a Mathlib.Tactic umbrella import.
- `/tmp/gc_OverlappingConeSplitting_lint.lean` compiles with both public declarations depending only on `[propext, Classical.choice, Quot.sound]`; no `unusedArguments simpNF synTaut` diagnostics; actual exit 0.
- The separate varying-convergence production driver also compiles silently, actual exit 0.

Suggested minimal headers: VaryingKleinerLottConvergence imports only existing `DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence`; OverlappingConeSplitting imports the new varying-convergence leaf, `DifferentialGeometry.Geometry.Comparison.TwoConeSplitting`, and existing `Approximation.NonnegativeConeCompactness`, `Approximation.ExactLimitApproximation`, `Approximation.MovingPointedLimit`. These suffice without the umbrella tactic module. The combined driver presently concatenates the new varying-convergence body and imports its dependency directly.

## Exact public contracts

The metric transfer theorem accepts actual whole-source KL maps from a varying family X_i at p_i to another varying family Y_i at q_i, with errors tending to zero. It proves equivalence of MC06 pointed convergence of those two families to the SAME specified Z/z. The three metric-space universes are independent. No completeness/properness/curvature/length hypothesis is added on either varying family or the target; target completeness belongs to the given MC06 convergence on either side and is preserved.

The uniform theorem says: for n≥1 and 0<δ<1, there exists 0<ε<1, uniform over all spaces, marked points, models, and supplied maps. Let original Z:Type u be metric; first model C:Type v be complete metric with actual arbitrarily short continuous curves, global dimH≤n, global fourPointComparison 0, and actual radial cone data at o. Let second model D:Type w be ANY metric space with actual radial cone data at v. Given p,q in Z with dist(p,q)=1, and the two ORIGINAL whole-source KL ε maps Z,p→C,o and Z,q→D,v, there exists a metric factor W:Type u and a∈W and an actual whole-source pointed KL δ map Z,q→EuclideanSpace R(Fin1)×₂W based at(0,a). Its own distortion and own target coverage are in the returned structure. No explicit modulus or monotonicity is asserted.

This is a deliberately stronger theorem than the written AC87/source statement: completeness and length on original Z, and completeness/length/nonnegative curvature/dimension on D, are unnecessary for this proof. The entire written contract follows immediately by specialization; no separate redundant public wrapper with unused hypotheses is added. The first model retains all its geometric compactness hypotheses. The parent and independent source reviewer approved this strengthening after checking the alternate proof below. The three input universes and output factor universe are explicit.

## Source versions and actual reading

Frozen `GEOMETRIZATION_BLUEPRINT/master207A.tex`, SHA256 `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`: AC87 `thm:alexandrov-overlapping-cone-splitting`, lines 6521-6589, full statement, proof, and convention paragraph read. The preceding AC85/86 and AC81 were also checked as the actual dependencies.

Kleiner--Lott, *Locally collapsed 3-manifolds*, Asterisque 365 (2014), archived `KleinerLottAsterisqueLocalCollapse.pdf`, SHA256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`: section4.5, Lemma4.20 and proof, printed pp.33-34 / PDF pp.28-29, plus the immediately preceding definition and Lemma4.19. The extracted actual text lines1427-1471 was reread. The source uses pointed-GH closeness; the formal theorem uses actual normalized KL witnesses, through the existing MC06/MC11 convention. It does not assert equality of numerical closeness conventions or an explicit tolerance formula.

Retained May15,2015 author corrections `GEOMETRIZATION_BLUEPRINT/references/chapter13_2026-09-26/KL_corrections.pdf`, SHA256 `b5849571508231ce7328ef842eaa0a8a74e34804de7741dab548c406dea11e19`, have no correction to the selected statements. This is the previously checked retained snapshot, not a new current-web errata claim. Source model/limit constructions use the already accepted comparison and line-splitting APIs; no migration interface or new axiom was assumed.

Mathlib revision is `c55e6e786f49471c72fbddbec5415808896aec1e`, Lean4.35.0-rc3. Existing PBA comp/restriction/quasiInverse and KL toClosedBall bodies were reread before fixing the stability contract. Existing ExactLimitApproximation's small-factor exclusion and explicit ULift factor transport were reread before the final universe-sensitive contradiction.

## Alternate proof route and domain checks

The implementation does NOT repeat the blueprint's two separate cone-model extractions and proper-limit identification. It extracts only the first C_i model sequence using AC86. Vanishing actual KL errors transfer convergence to the ORIGINAL Z_i,p_i. One diagonal choice of actual growing-radius PBA maps, followed by AC81, gives a further common subsequence and q∞ in that SAME proper limit, with dist(q∞,p∞)=1 and original Z_i,q_i→X,q∞. The exact index is α composed with β composed with χ, and both original KL map sequences are reindexed by that same composition.

The second ORIGINAL KL maps imply D_i,v_i→X,q∞ directly through the reverse direction of the metric transfer theorem. AC85 therefore produces a second cone structure on this SAME X at q∞; no properness or completeness of D_i is needed and no second unidentified copy of the limit is introduced. AC84 plus the accepted pointed two-apex product theorem gives the normalized exact product at q∞. The existing ExactLimitApproximation theorem transfers it back to original source KL δ splittings. Its inspected ULift construction moves the Type-valued factor to Type u, exactly matching the counterexample exclusion. The counterexample errors are 1/(i+2), with positivity, strict <1, and convergence proved; there is no assumed monotonicity of the requested modulus.

The generic stability proof first converts actual KL maps to arbitrary fixed-radius/error PBAs eventually, using 3ε_i<η and R<ε_i⁻¹, with the original open-ball and non-strict coverage convention retained. For reverse maps, it takes original PBAs at radius R+η,errorη/4 and applies the actual quasiInverse, obtaining radiusR,errorη. Composition compares at radius2R+2,errorη/8 and restricts to the required R-ball; the image-domain margin R+η/8≤2R+2 and the output error bounds are proved explicitly. All coverage is the approximation structures' own coverage, not source-image-only coverage.

Parent independently read both complete frozen bodies and reported no proof/scope issue. The independent reviewer also approved the strengthened one-model route before implementation. The full original-input uniform application is accepted in overlapping_cones_review.md with compiler and axiom evidence.

## Compiled incomplete-source metric regression

`/tmp/gc_varying_kl_incomplete_review_extra.lean`, SHA256 `11cef84e4627a4af9fa0c9ba1033a31d5fdc3cc6d6aba50029443bf125e2ce45`; combined `/tmp/gc_varying_kl_incomplete_review_agent.lean`, SHA256 `64b1821b135447a5d44ccb64d7f10d4483ab2fe9aa785beb8aca07c7f2c35348`. Actual compile exit 0, no warnings, lint clean, standard three axioms only.

This reuses the actual incomplete dense union of rays S={(x,y)∈R² | x≠0 or y=0}, whose incompleteness is formally proved. Actual inclusion PBAs give whole-source KL maps of error1/(i+2); the maps are proved to agree with the original inclusion on every tested open source ball. Both directions of the NEW metric stability iff are applied to these actual maps, preserving the SAME Euclidean-plane limit. Thus neither completeness of the varying source nor arbitrary supplied approximation hypotheses is hiding the result.

No repository edits, shared builds, admissions, custom axioms, or source-archive mutations were made by this subtask. These are temporary candidates for parent integration, not a chapter-completion claim.

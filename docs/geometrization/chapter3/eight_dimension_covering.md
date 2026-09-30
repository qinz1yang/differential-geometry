# Original8R finite-dimensional covering, including bounded curvature

Four public theorems in two leaves produce exact internal nets from original8R local curvature and ambient Hausdorff dimension alone. Neither charts nor local compactness are assumed: the established paired-configuration and local-compactness producers supply them before original AC04 is applied. Ambient and actual-intrinsic inputs are supported, at curvature−1 and at−kappa for0≤kappa≤1. The SAME original closedR-ball has the exact dimension-only ceiling bound with strict epsilon coverage. Earlier mathematical leaves and blueprint207 remain unchanged.

# Original eight-radius covering from local geometry and finite dimension

Four public theorems in two new leaves, with no definitions or private lemmas, close the original8R finite-dimension/local-curvature-to-covering consumer. Both ambient and actual-intrinsic local comparison inputs are supported, first at curvature-1 and then at curvature-kappa for0<=kappa<=1. All retain the ORIGINAL closedR-ball, its ambient distances, and the exact net bound

(1+Nat.ceil(4*pairedChartDistortion(n)^2*sqrt(n)*sinh(2R)/epsilon))^n.

The finite net is internal and covers with strict distance<epsilon. Ambientcomplete metric, actual arbitrarily short curves, original open8R local comparison and ambientdimH<=n (integern>=1) are the only geometric inputs. No chart, local compactness, properness, minimizing segments, finite net or limit is supplied. No statement about the completeness of the open controlled ball is assumed or inferred.

## Source reading and actual dependencies

Fresh complete reading: frozen207A AC04 lines2232–2269 and note2271–2277, AC07 lines2357–2377, AC08 lines2401–2418 plus its intrinsic-dimension clarification, AC29 lines3508–3535 and subsequent alternate-route qualification, AC33 lines3723–3785, ALG07 lines7582–7617. Blueprint SHA256277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b.

The complete accepted bodies read: NearbyPairedChart, CenteredPairedChart, FiniteDimensionalLocalCompactness, FiniteDimensionalCovering, VaryingCurvatureCovering, VaryingLocalGeometry; the relevant exact rescale and net-bound calls were checked. Newly frozen full originalAC02 and original8R AC03/04 proof bodies and source records are the actual comparison/contraction inputs. Their constants/domains are preserved rather than relabeling the old256R theorem.

Retained BBI10.8.13–23 (printed385–389/PDF400–404), BGP6.3 (printed20/PDF21), and local-length/source errata comparisons are those already checked for the accepted paired-configuration/local-compactness hierarchy. The original chart argument is the project's proved negative-curvature adaptation, not an unqualified reuse of BBI's simplified curvature-zero500m constant. The scalar hyperbolic contraction/BBI10.6.2 normalization checks remain those recorded in `/tmp/gc_OriginalEightChartCovering_record.md`; actual intrinsic comparison and new retained-budget/midpoint source checks are in the originalAC02 record. No new moving-source or remote-errata retrieval is claimed.

## Proof and non-circularity

The curvature-1 ambient theorem handles a singleton by the actual finset{o}, with exact internality and strict epsilon coverage. In the nontrivial branch, the EXISTING arbitrary-open-region producer constructs local compactness onB(o,8R) from all original local comparison neighborhoods and ambientdimH. The existing nearby chart producer needs only the basepoint's common comparison neighborhood, and chooses an ACTUAL q inB(o,R/2), rank1<=m<=n, actual anchor family, positive chart radius, and centered distance-coordinate chart with pairedChartDistortion(n). Neither producer assumes minimizing paths or the covering result being proved here.

Every original ambient comparison neighborhood is transported to the actual intrinsic8R metric by the accepted local equivalence. New original8R AC04 then supplies its exact rank-m net. The accepted chart_net_bound_mono_dimension enlarges that literal natural-ceiling bound tom<=n; no synthetic Euclidean padding or chart-radius term appears. All source points/net centers stay in the original metric and original closedR-ball. The intrinsic-input companion uses exact neighborhood equivalence in the reverse direction, and keeps the ambient dimension premise as required by AC29; no assumed intrinsic global dimension or completeness is introduced.

For boundedkappa, kappa0 is handled by accepted zero-to-one comparison weakening. For0<kappa<=1 letc=sqrt(kappa),0<c<=1 and use the ACTUAL scaled metric d'=c*d. Source completeness, actual short curves, open topology, local curvature1 and Hausdorff dimension are transported through accepted exact rescale lemmas. The controlled region is literally B_d'(o,8cR)=B_d(o,8R). Apply the new curvature-1 theorem at radiuscR and errorcepsilon, then use accepted chart_net_bound_rescale_le to retain the same fixedcurvature-1 numeric bound. The produced finset itself is unchanged, B_d'(o,cR)=B_d(o,R), and dividing strict coverage by positivec gives the original strictepsilon coverage. No unproved general monotonicity of four-point comparison in kappa is used. The intrinsic companion translates the ORIGINAL intrinsic8R neighborhood data before this actual scaling proof.

This fills a genuine source-radius assembly. The already proved full original MC18/AC41 growing-region extraction remains untouched; its eventual256R windows were already available under the same growing-region hypothesis, so no extraction or same-limit construction is rerun merely to improve a tail.

## Frozen files and verification

- `/tmp/gc_EightFiniteDimensionalCovering_body.lean` SHA256 `a7b5e0737fab628dbedd0235032be03d950f7485a712a43258ed6da5c39a7cef`.
- `/tmp/gc_EightVaryingCurvatureCovering_body.lean` SHA256 `091a96a9441513ace78a4859ac7bdc90d8597c6a851e4431b008000b9e62f797`.
- `/tmp/gc_EightVaryingCurvatureCovering_agent.lean` SHA256 `c19b2c4f2d1aaae75d5cf7b7b7fd3a839520428442ec27497b3bc19dad2824ba`.
- `/tmp/gc_eight_dimension_covering_review_body.lean` SHA256 `3f7160e14dc070672f5e861ed16903e768e0e80aac2c198e64745caa52be0d8e`.
- `/tmp/gc_eight_dimension_covering_review_agent.lean` SHA256 `2aadb13d5092529cb7a070bdc761ffc5f66b0615be2d58318b5e2c791fd53076`.

Natural canonical imports for EightFiniteDimensionalCovering: accepted Comparison.FiniteDimensionalLocalCompactness, Comparison.NearbyPairedChart, MetricSpace.ChartNetBound, and the new original8R chart-covering leaf. For EightVaryingCurvatureCovering: the preceding new fixed-curvature leaf, accepted Comparison.RescaleComparison, Comparison.CurvatureWeakening, Geometry.Metric.Scaling.RescaleLength, and MetricSpace.RescaleNetBound.

Minimal combined production compile exit0 with empty log. `/tmp/gc_EightVaryingCurvatureCovering_lint.lean` and log: exit0, silent unusedArguments/simpNF/synTaut, all four public declarations have exactly propext, Classical.choice, Quot.sound. No admissions, extra axioms, resource-limit changes or conclusion-shaped premise structures. Lean4.35.0-rc3, Mathlibc55e6e786f49471c72fbddbec5415808896aec1e.

Five actual original-input regressions also compile/lint exit0 with no warnings and standard-three closures. Four tests apply each public theorem on complete real line, radius1, actual proved near-short curves and localcomparison, ambientdimH<=1 proved via Real.dimH_univ. The intrinsic cases use the actual constructed(-8,8) intrinsic metric; all0<=kappa<=1 are allowed in the bounded tests, retaining the SAME exact epsilon bound for everyepsilon>0. No chart or compactness premise is supplied. The fifth test uses the actual singletonPUnit, radius2, all0<=kappa<=1, arbitraryepsilon>0, actual constant segments/curves, actual zero Hausdorff dimension and literal vacuous localcomparison. This exercises the singleton and both curvature branches. Real fixture geometry is reused verbatim from the previously checked original8 midpoint tests up to the actual-local helper.

Independent full source/statement/proof review by same_lines passed; root completed canonical integration and gates. All work here is temporary. No repository, blueprint, source archive or shared build mutation was performed.

## Canonical accepted-import verification

- `/tmp/gc_EightVaryingCurvatureCovering_canonical_agent.lean` SHA256 `a0a6febfd046c936bc75d0b36fcabe2e173c05b61c451f12f3b1b0fa207e8483`.
- `/tmp/gc_EightVaryingCurvatureCovering_canonical_lint.lean` SHA256 `f63c33129f1039b21e1ec59a329f32fa955d26bdaa4f1ecd2be3faeca9123df3`.
- `/tmp/gc_eight_dimension_covering_canonical_review.lean` SHA256 `795f0261e45a2b03ad8306c929d4826e73f2320677455d463fd3ba4b9677038d`.

After root accepted the original8R consumers, both the new minimal canonical-import production/lint driver and the canonical-import five-test regression compiled exit0. They import accepted EightChartCovering and only the named accepted producer/scaling dependencies before the two new frozen bodies; no temp comparison forest is recopied. Both logs contain only the expected standard-three axiom reports and no warnings or lint findings. Frozen proof-body and regression-body hashes above are unchanged.

## Canonical accepted-import verification

- `/tmp/gc_EightVaryingCurvatureCovering_canonical_agent.lean` SHA256 `a0a6febfd046c936bc75d0b36fcabe2e173c05b61c451f12f3b1b0fa207e8483`.
- `/tmp/gc_EightVaryingCurvatureCovering_canonical_lint.lean` SHA256 `f63c33129f1039b21e1ec59a329f32fa955d26bdaa4f1ecd2be3faeca9123df3`.
- `/tmp/gc_eight_dimension_covering_canonical_review.lean` SHA256 `795f0261e45a2b03ad8306c929d4826e73f2320677455d463fd3ba4b9677038d`.

After root accepted the original8R consumers, both the new minimal canonical-import production/lint driver and the canonical-import five-test regression compiled exit0. They import accepted EightChartCovering and only the named accepted producer/scaling dependencies before the two new frozen bodies; no temp comparison forest is recopied. Both logs contain only the expected standard-three axiom reports and no warnings or lint findings. Frozen proof-body and regression-body hashes above are unchanged.

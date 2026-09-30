# Chapters 3–4: verified metric frontier and remaining release bindings

**Final frontier report with an accepted145 delivery supplement.** This report reconciles Chapter 3, *Metric geometry and pointed limits*, and Chapter 4, *Alexandrov geometry and local models*, against frozen blueprint 207A. It lives in the existing `docs/geometrization/chapter3` evidence area because that area already contains the shared metric and Alexandrov dependency forest. It does not replace or revise the one-file blueprint.

The bounded contract review identified **no remaining required migration-independent mathematical producer** among MC01–24, AC01–87, ALG01–08, ALS01–05 and ALR01–05. The independent search of these frozen obligations is exhausted at this snapshot. This means no specific uncovered producer was found after the checks below; it does not mean all possible Alexandrov geometry, every auxiliary sentence, either full chapter, or the migrated GC root is complete.

The remaining concrete mathematical integration work is the inherited smooth interface binding described below. The repository explicitly pauses that work until the completed PC release or an explicitly stabilized interface is available. A newly discovered mismatch with an exact frozen contract would reopen the affected independent producer.

## Accepted audit snapshot and delivery supplement

| Item | Status bound by this report |
|---|---|
| Frozen blueprint | `GEOMETRIZATION_BLUEPRINT/master207A.tex`, SHA256 `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b` |
| Accepted audit baseline | Milestone 144, commit `9f5f8d2c624110d0bc79d3ddebfb655112d57100` |
| Accepted manifest | 509 modules; SHA256 `b9ea39d42c058ac4e8fa5c88df6dedc2d26bf9ea31c8daca1ddde3905a9c01a2`; `full_chapter_complete: false` |
| Completed selected Lean gate | 2351 owned declarations and 3347 build jobs; shared verification SHA256 `734f1d29dca08c5b5d22b538d3bbe1a2a47d6401da2321623d75b50d4d09d4f2`; build and axiom audit exit0 |
| Milestone 144 receipt | SHA256 `ae6d483cacc67bf5439d8948c08f6eed913720db80cff16b8c3b34b1e4a429a5` |
| Milestone 145 acceptance | Accepted and remotely verified at `45111b9d91f50111658f0497be2320e750325ca6`; observed 513 modules, 2362 owned declarations and 3351 jobs. The supplemental receipts below are separate from the accepted144 audit snapshot. |
| Full migrated root | Not built; this audit makes no full-root or whole-project completion claim. |
| Blueprint static audit at accepted144 | **Failed**, exit1, on the historical missing archive path `BooksPapers/MatveevBook2ndEd.pdf`. This is neither a Lean proof failure nor a static pass. |

The toolchain is Lean4.35.0-rc3 with Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`. The shared receipt's `git_head_at_check` is the preceding commit, as recorded by the acceptance workflow; the receipt and exact source hashes are retained in accepted 144. This report does not misidentify that field as the publishing commit.

The [accepted manifest](evidence/chapter34_frontier_146/accepted144_manifest.json), [shared verification](evidence/chapter34_frontier_146/accepted144_shared_verification.json) and [milestone receipt](evidence/chapter34_frontier_146/accepted144_milestone_verification.json) are preserved separately from the moving live evidence paths. The [evidence index](evidence/chapter34_frontier_146/index.json) maps original temporary paths to the copied, hash-checked files below. Temporary path spellings inside unchanged peer records are provenance; the index resolves their current authoritative copies. External reference archives are identified by hash and are not recopied. Superseded metadata-history paths are not prerequisites for this current assessment. The index also records the actual accepted145 delivery evidence below. This supplement does not change the accepted144 audit baseline; the immutable peer reports preserve their original assessment dates and pending145 statements as historical evidence.

## What was checked

Three complementary reviews were performed:

- The [MC review](evidence/chapter34_frontier_146/metric_frontier_assessment.md) read the full frozen metric contract/proof text at master207A 655–1992, checked all 24 MC nodes and surrounding unnumbered assertions, and inspected the principal current implementations and library interfaces.
- The [AC/ALG/ALS/ALR review](evidence/chapter34_frontier_146/alexandrov_frontier_assessment.md) read all 95 AC/ALG statements, the ALS/ALR statements and relevant proofs, and reconciled their actual domains, hypotheses and conclusions with accepted producers.
- The [independent challenge](evidence/chapter34_frontier_146/independent_frontier_assessment.md) challenged both conclusions against the actual blueprint and selected full current proof bodies. It particularly rechecked the unnumbered compact-target net statement, all nested original-path 8R comparisons, original-input growing-limit extraction and automatic original-input distance charts.

The [AC source binding](evidence/chapter34_frontier_146/alexandrov_receipt_binding.json) matches all 475 associated source files to the successful accepted 144 shared receipt; 465 additionally match individual milestone source maps. The ten initial baseline files are covered by the shared receipt rather than new-format individual receipts. The [MC source check](evidence/chapter34_frontier_146/metric_source_hash_check.json) matches 56 owned files; inherited `PointedBallApproximation` is the separately recorded 57th baseline file. These are source counts, not counts of independent mathematical obligations. The independent reviewer rechecked these hash reconciliations.

These reviews reuse prior full source/proof/axiom records where the exact bytes and contracts are unchanged. They are not new line-by-line audits of all 509 modules, nor fresh executions of all accepted builds. The [independent evidence record](evidence/chapter34_frontier_146/independent_frontier_evidence.json) identifies the additional complete proof reads and distinguishes them from static matching and previously accepted compiler evidence.

The [root review](evidence/chapter34_frontier_146/root_frontier_review.md) records the complete final assessment reads and the additional demand for an actual compiled export, then confirms the bounded classification and the corrected commit provenance.

## Contract coverage and preserved mathematical scope

| Contract family | What the accepted producers supply |
|---|---|
| MC01–05, MC19; unnumbered metric foundations | Actual cumulative-length parametrization preserving the original curve and exact subinterval variation; lower semicontinuity and compact curve extraction; near-short-curve Hopf–Rinow; finite packing/nets; compact GH correspondence/map bounds; the positive Lipschitz-envelope criterion. Smooth realizations are not silently included. |
| MC06–16, MC21–24 | Original-map pointed approximations with explicit radius/error guards; restriction, composition, inverse, recentering and scaling; actual open/closed/KL convergence translations with slack; one coherent subsequence and target; complete-limit length and proper-limit segment/uniqueness results; closed-ball and product-collapse conclusions. Properness is assumed only in the interfaces that require it. |
| MC18, AC34–41 | Original complete metric sources with near-short curves, growing controlled regions, local comparison and dimension bounds produce eventual internal nets and one strict subsequence with the same complete proper pointed limit. Comparison0, dimension bounds, actual minimizing segments and quantitative nets are proved on that target. The theorem does not ask for an already supplied target, global comparison or the required nets. The intrinsic-source version preserves its actual intrinsic-to-ambient metric interpretation. |
| AC01–04, AC13, AC36, AC64, ALG01–07 | Actual local completeness/geodesic construction, germ limits, quantitative hinge enlargement and nonpositive-curvature globalization/buffer comparison. Original 8R nested comparison preserves both chosen paths, all four parameters 0<s≤u and 0<t≤v, and exact original intrinsic lifts/cross-distances; the model-side version includes zero arms. Original 16R and larger buffer consumers retain their own stated domains. No complete-open-ball assumption is inserted. |
| AC07–12, AC14–33 | Original-input local compactness, rank/chart and covering producers, followed by actual completed directions/tangent constructions, relative dense Euclidean tangent points and same-rank angular obstruction. The automatic chart theorem selects one rank before the dense set and its points, and returns the original common anchors and literal distance coordinates with the displayed L(n). Historical supplied-chart, supplied-LC or abstract direction-compatibility premises are no longer the endpoint. |
| AC42–48, ALS01–05, ALR01–05 | Actual aligned onto line splitting, factor geometry/dimension and pointed recognition of singleton, line, ray, interval and length-circle models, with original basepoints and parameter exclusions. One-dimensional exclusion uses Hausdorff dimension directly. |
| AC49–81 | Same-target product limits, original coordinates and marked points, full factor/source coverage, exact strainer/axis/compatibility constants, common subsequences and approximations, and uniform parameter theorems. The arbitrary-radius/tail quantifier order and original endpoints are retained. |
| AC82–87 | Actual cone formulas and two-ray/two-apex geometry, same-target cone closure, original cone compactness and overlapping-cone splitting, with the original metric and map coverage. |

The full agent reports contain the node-level table and exact declaration names. The old frozen prose describing local Toponogov, arclength, chart regularity, splitting or growing-limit geometry as missing is historical; it is not current evidence of an open producer when later accepted, hash-bound declarations discharge the same contract.

The comparison API usesκ≥0 to encode the lower bound−κ. In particular, its parameter 1 is local curvature at least−1. No general positive-curvature globalization is inferred from that normalization. Nor does dimension-free tangent comparison imply tangent geodesicity: KLP 3.3 explicitly separates those assertions.

## Unnumbered compact-target export check

The blueprint lemma `lem:alexandrov-model-packing`, master207A 2044–2066, has no AC number. It was checked explicitly rather than omitted from a tag inventory.

For the original distance-expanding map Φ:A→K, injectivity follows from the distance inequality. A finite η-separated source set has an equally large η-separated image. Its image cardinality is bounded by the supplied η/3 target net using `Metric.card_le_card_of_separated_net`, since 2η/3<η. Applying `Metric.exists_finset_net_card_le_of_packing` then returns an internal **strict** η-net with at most N points. Compactness and source nonemptiness are unnecessary once the target net is supplied; an unnamed application nevertheless checks the literal original assumptions. Continuity and surjectivity are never assumed.

This exact composition and an actual expanding-map regression were compiled in temporary files:

- [Export proof](evidence/chapter34_frontier_146/compact_target_net_export.lean), SHA256 `46bddbb6e6b52bb0074f0348d20fe163e02c535be3d0b666c446abcb4d773d20`.
- [Original-object example](evidence/chapter34_frontier_146/compact_target_net_example.lean), SHA256 `2251200b2eab316863c64b7fc26690e557eb9a468b411c0ec095156e0c419289`:Φ(x)=2x from (0,1) into [0,2], with the actual two-endpoint target net and an internal source net.
- [Combined normal driver](evidence/chapter34_frontier_146/compact_target_net_review.lean) and [empty log](evidence/chapter34_frontier_146/compact_target_net_review.log): actual session 22358 exit0.
- [Selected-lint driver](evidence/chapter34_frontier_146/compact_target_net_lint.lean) and [log](evidence/chapter34_frontier_146/compact_target_net_lint.log): actual session 67423 exit0, no findings, exactly two axiom reports using only `propext`, `Classical.choice`, `Quot.sound`.

The independent reviewer read both complete proofs and checked the retained logs. This is export verification of existing kernels, not a new registered production theorem, manifest entry or mathematical milestone.

## Remaining inherited smooth bindings

| Binding | Exact requirement still to attach to the accepted release |
|---|---|
| MC17 | Produce ambient ball-distance inequalities **and** target-ball coverage from the accepted smooth convergence/exhaustion interface. Tensor bounds first give lengths and intrinsic domain distances; an actual exit/no-shortcut or convexity argument must justify ambient distances. `PointedBallApprox.ofBilipschitz` already proves the metric implication. |
| MC20 and scaling normalization | Match KL Definition 3.4/Lemma 3.5 with complete C^(K+2) sources, K≥10, one fixed family function A(R), noncollapse and all stated derivative bounds. Its GH condition is part of the source definition, not a consequence supplied by citing it. Tensor scaling by c changes metric distances by √c. Bind inherited compactness/normalization rather than rebuilding it. |
| AC05 | Supply the inherited smooth coordinate, tangent-norm, curve-length and Riemannian-distance interfaces for the written exit-path proof of an **ambient** chart with exactly L=2. A generic L(n) metric chart is not the same constant. |
| AC06 | From original complete connected smooth n-manifolds, sectional curvature ≥−cᵢ, cᵢ→0 and growing radii, supply the inherited curvature-to-local-comparison interface and AC05 chart. Preserve the exact uniform N(n,2,R,ε) bound and one extracted pointed limit. No uniform positive chart radius is required. |
| ALG 08 applications in LC12/LC78 | Bind the original smooth curvature and first-order distance/angle interpretations with the specified buffers and order of choices. Preserve the same chosen minimizing hinges and actual Riemannian angles; pure metric globalization alone does not perform this smooth translation. |

These are requirements for integration, not findings that the user's inherited results are absent. No changing PC snapshot was searched to manufacture an absence claim. No theorem source needs to be weakened, and no foundational geometry should be rebuilt to evade the release boundary.

The governing instruction is preserved in the [project-instruction snapshot](evidence/chapter34_frontier_146/project_instructions_snapshot.txt), “Preserve the PC reuse boundary”: **“Pause expansion of adapters and declaration probes tied to that changing snapshot until the completed release or an explicitly stabilized interface is available.”** The historical source is the parent workspace's `AGENTS.md`, outside the GC repository; the exact bytes are copied as `.txt` to preserve provenance without introducing a nested instruction file. The read authority has SHA256 `f309791e5507990a4ab5b7e6de8fdae27e1d02a9bb8b1e57de8767045c7aa650`. That specific boundary justifies the migration stop for these tasks. It does not prohibit independent work in other chapters or reopen this scope merely because stronger optional theorems exist.

The final [targeted MC17/AC05 challenge](evidence/chapter34_frontier_146/metric_exit_coverage_challenge.md) confirms that the accepted `FirstExit` producer preserves the same original curve prefix and `IntrinsicBall.intrinsicEDist_eq_edist_on_inner_closedBall` supplies the buffered intrinsic-to-ambient equality. These are the existing pure kernels. The actual smooth length, exhaustion and two-domain coverage assembly remains unbound; a conditional wrapper that assumes those inputs would not produce them. No additional independent metric producer is recommended.

## Sources, corrections and deliberate limits

The source archive is read-only. Source versions and exact identities are retained in the agent records; no blanket whole-book or new remote-errata audit is claimed.

| Source / locator actually used in the review | Role and qualification |
|---|---|
| Frozen master207A 637–1992,2010–7687; especially1817–1893,2044–2066,2282–2354,2677–2694,7218,7262–7263 and 7643–7670 | Actual selected obligations, explicit smooth bindings, unnumbered export, original chart constants and local/global scope. Chapter 4's worksheet expressly selects necessary consumers rather than every Alexandrov theorem. |
| BBI 2.5.9 printed 46/PDF 61;2.5.22–23 printed 49–50/PDF 64–65;8.1.9–10 printed 274–275/PDF 289–290 | Cumulative-length/Hopf–Rinow and pointed compactness source checks by the MC reviewer; the stronger eventual-net producer is proved in the accepted library, not attributed literally to BBI. |
| BBI 5.1.13–16 printed 146–147/PDF 161–162 | Actual near-Euclidean discussion is two-dimensional and leaves basic proofs as exercises. The blueprint supplies its own arbitrary-dimensional exit-path adapter. Retained July 6, 2024 errata correct printed 146 line 11 fromR³ toR²; this is preserved rather than silently upgrading the archived statement. |
| Kleiner–Lott, *Locally collapsed 3-manifolds*, Asterisque 365, §3.2 Definition 3.4/Lemma 3.5 printed 22/PDF 17 and §3.3 through Lemma 3.10 printed 22–24/PDF 17–19 | Smooth compactness qualifications and the selected metric limit consumer. The May 15, 2015 corrections and earlier source checks are reused. |
| KLP 3A/B–3.3 printed 35–37/PDF 37–39;6.18–6.20 printed 69/PDF 71; semisolution137–138/PDF 139–140 | Actual completed directions/tangent conventions, nonnegative tangent comparison versus geodesicity, and dimension/source limits. Full TopDim or infinite-dimensional statements exceed the selected frozen obligations. |
| Pinned AKP vol1 `ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`; prior accepted source records for BBI 10.5/10.8, BGP6.2–6.3 and KL 4.2–4.5 | Unchanged detailed comparison, splitting, strainer and globalization source records reused by the AC audit. No re-audit of all those books is claimed here. |

Archive identities: BBI SHA256 `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`; KLP `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`. Retained source text/errata hashes and the exact targeted reading boundaries are in the copied reviews.

Topological-dimension equality, curved-model siblings of KLP's finite Euclidean comparison, infinite comparison families, general positive-curvature globalization and stronger dimension-free tangent structure are not newly identified missing frozen obligations. ALR 05 uses Hausdorff dimension directly; ALG explicitly selects only nonpositive curvature. Milestone 145 proves an additional global guarded spherical predicate on actual directions by a cone argument. It does not establish arbitrary positive-curvature globalization. Its now-verified delivery remains a separate supplement, not retroactive accepted144 evidence.

The source audit corrected a commit transcription typo to the actual 40-character accepted 144 commit shown above. Its snapshots and proof/log bytes were unchanged. The independent review's earlier snapshot already used the correct commit; its final peer-record hashes were rebound. This was a provenance correction, not a mathematical repair.

The truthful frontier is therefore: the reviewed independent metric contracts have accepted producers, no additional required independent producer was found, and the enumerated smooth release bindings remain open. The failed historical static audit and unbuilt migrated root remain visible. Neither registration counts nor this assessment justify a whole-chapter or whole-project completion claim.

## Accepted145 delivery supplement

The following facts were read from the successful committed receipts and hash-bound logs, not predicted from registration. The publishing commit is `45111b9d91f50111658f0497be2320e750325ca6`. Root's explicit remote record confirms the same commit at `refs/heads/codex/geometrization-shared-interfaces-435rc3` on `origin`; the finalizer checked the configured remote URL and current local publishing branch. It performed no new push or network verification.

| Supplemental evidence | Observed result |
|---|---|
| [Milestone receipt](evidence/chapter34_frontier_146/accepted145_milestone_receipt.json) | Success; SHA256 `5f6cbd87451d207b696ca7b525b057ce481b1a9f31caa3f6a747ea89f1168954` |
| [Shared receipt](evidence/chapter34_frontier_146/accepted145_shared_receipt.json) | Build and axiom audit exit0; SHA256 `71a06c6bd0b7d40ffa94403fa3985d21a8e5d597b89aa95c80db02c2e2f04820` |
| [Committed manifest](evidence/chapter34_frontier_146/accepted145_manifest.json) | 513 sources, agreeing exactly with the shared receipt |
| [Build log](evidence/chapter34_frontier_146/accepted145_build_log.log) and [axiom log](evidence/chapter34_frontier_146/accepted145_axioms_log.log) | 3351 jobs and 2362 owned declarations, parsed from their actual completion markers |
| [Canonical checks](evidence/chapter34_frontier_146/accepted145_canonical_checks.json), [review](evidence/chapter34_frontier_146/accepted145_canonical_review_log.log) and [lint](evidence/chapter34_frontier_146/accepted145_canonical_lint_log.log) | 19 standard-axiom reports; silent selected lint; receipt records 11 new regressions |
| [Root remote-verification record](evidence/chapter34_frontier_146/accepted145_remote_verification.json) | Exact recorded remote commit matches `45111b9d91f50111658f0497be2320e750325ca6` |
| Separate145 blueprint static status | failed; latest completed exit 1. Historical source path is missing: /Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/MatveevBook2ndEd.pdf |

The earlier accepted144 static failure remains part of the historical audit. A fresh static audit after the eventual frontier document/inventory delivery requires a separate146 record; this bundle does not infer a pass from an empty-output invocation or overwrite the historical144/145 statuses. The full migrated root is still not built, and no whole-chapter completion is asserted. The specific inherited smooth-interface stop and all original mathematical scope qualifications remain unchanged.

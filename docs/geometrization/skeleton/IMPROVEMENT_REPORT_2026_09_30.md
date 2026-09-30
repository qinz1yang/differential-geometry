# Blueprint 207 skeleton improvement — September 30, 2026 (UTC)

This is a **partial implementation of the requested improvement**, with a passing admission-aware unified-environment gate. Task 5’s full mixed/good-block and local-collapse decomposition and the finite-C cusp realization remain incomplete. The endpoint is unchanged and still depends on `sorryAx`.

## Environment and executed gates

- Checkout: `/Users/bennettchow/Documents/Documents - Unknown/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT`.
- Branch: `codex/geometrization-blueprint-skeleton-207`; comparison HEAD `3167083409cd58f39742a7872dab504a65d24b56` is the protected foundation, while the improvement diff starts at `b456fb0eab29f8e61795123bf7df5dc5b3a824c8`.
- Toolchain: `leanprover/lean4:v4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. One checkout, one foundation; no 4.35 migration.
- `python3 tools/gc/check_skeleton.py --full-root --fresh-audit`: passed, 48 mathematical modules, 214 authored / 1008 elaborated declarations. Audit build status **replayed**, audit evidence **fresh-elaboration**. [Receipt](evidence/verification.json), [build](evidence/build.log), [fresh audit](evidence/fresh_audit.log).
- All 155 protected baseline modules byte-identical; the three Blueprint 207 hashes match. `check.py`, `module_layout.py`, toolchain and Lake manifest are unchanged.
- Fresh direct source elaboration of all 48 mathematical modules passed with exact project Lean options. All 35 proof-only modules were silent. The 13 admitted leaves emitted their registered sorry diagnostics. [Per-module logs and hashes](evidence/improvement/leaf_builds.json).
- The five requested linters were run per module, not per namespace. The initially unused IsManifold binder on disk reparametrization was removed. [Final lint output](evidence/improvement/lint.log).
- Literal silent-root/zero-diagnostic acceptance is not met: registered sorry warnings and unchanged foundation style warnings appear in the root log; the audit intentionally prints evidence. None is suppressed. The compiler gate’s success is admission-aware, not a claim of warning-free or axiom-clean Geometrization.
- File-provider stalls required exact-hash hydration of existing source and Git objects. Sources and dependency revisions were not migrated. A bare Git object cache in /tmp was used only to recover identical bytes, not as a second Lean foundation. [Hydration evidence](evidence/task0) and the build receipts retain the checked state.

## Admission inventory

**direct_sorry_count = 22**, previously 17. Five original admissions were proved; the original closed threshold, selected-flow, graph-prime, and nonnegative-presentation conclusions are now proved corollaries of more explicit admitted dependencies. The net increase reflects decomposition, not newly claimed mathematical proofs. The endpoint reaches 14 direct admissions; 8 others are prepared off the endpoint path.

Proved without sorryAx:

- `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_shift`.
- `DifferentialGeometry.Geometry.Collapse.curvatureRadius_pos`.
- `DifferentialGeometry.Geometry.Collapse.curvatureRadius_eq_top_iff`.
- `DifferentialGeometry.Geometry.Collapse.exists_common_curvature_derivative_bound`.
- `DifferentialGeometry.Geometry.MinimalSurface.continuousOn_leastExteriorDiskArea_of_local_disk_comparisons`.

Original conclusions now proved by composition, still conditional on registered admissions:

- `DifferentialGeometry.Geometry.Collapse.exists_closed_graph_threshold`.
- `GC.LongTime.exists_surgery_with_late_sequence_tests`.
- `GC.GraphManifold.exists_prime_decomposition_of_rawGraphPresentation`.
- `DifferentialGeometry.Geometry.Collapse.exists_rawGraphPresentation_of_nonnegative`.

The exact current direct list follows. Each label, label line, reading range and TeX SHA256 is in the named crosswalk entry. Primary-context reading does not mean the exact stronger Lean adapter has been proved.

| Direct admission | Blueprint locator | Source locator / checking scope | Endpoint path |
| --- | --- | --- | --- |
| `DifferentialGeometry.CheegerGromovCompactness.exists_bilinear_form_limit_subsequence_of_bounded_derivatives` | master207A.tex:25870 `thm:collapse-finite-consumer-compactness` [25869–26085] | Blueprint-only exact adapter. Blueprint-only exact contract: master207A.tex:25870 thm:collapse-finite-consumer-compactness; reading [25869, 26085] | no |
| `DifferentialGeometry.Geometry.Collapse.exists_boundary_graph_threshold` | master207B.tex:10278 `thm:fibration-closed-static-collapse-threshold` [10277–10339]; master207B.tex:10593 `thm:fibration-boundary-static-collapse-threshold` [10592–10651]; master207B.tex:10774 `thm:fibration-written-static-goal-completion` [10773–10848] | Blueprint-only exact adapter. KL Notes Theorem92.3 primary context, printed2824–2825/PDF238–239. KL14 Theorem16.1 is Blueprint-only via A:19797–19832, as requested.; Blueprint B:BBR03, 10592–10651; intrinsic-boundary and external-label adapter remains admitted. | yes |
| `DifferentialGeometry.Geometry.Collapse.exists_closed_graph_threshold_of_finite_scales` | master207B.tex:10278 `thm:fibration-closed-static-collapse-threshold` [10277–10339] | Blueprint-only exact adapter. Perelman, second paper §7.3–7.4, GrishaPerelman2.tex lines 1091–1181; Kleiner–Lott Notes (2008), Theorem 92.3 / Remarks 92.2–92.6 and printed 2827. KL14 definitions/16.1 are used only through the unchanged Blueprint record A:19751–19832. | yes |
| `DifferentialGeometry.Geometry.Hyperbolic.cusp_constant_sectional_curvature` | master207B.tex:7578 `sec:fibration-boundary-scale-adapter` [7577–7590] | Blueprint-only exact adapter. Blueprint boundary cusp metric record master207B.tex:7577–7590; KL14 Section16 is not newly read. | no |
| `DifferentialGeometry.Geometry.Hyperbolic.has_hyperbolic_atlas_of_curvature_neg_one` | master207A.tex:10648 `lem:hyp-rescaling` [10647–10667]; master207A.tex:18881 `lem:hyp-whole-interior` [18880–18898]; master207A.tex:18900 `thm:hyp-thick-certificate` [18899–18915] | Blueprint-only exact adapter. Blueprint-only exact contract: master207A.tex:10648 lem:hyp-rescaling; reading [10647, 10667]; Blueprint-only exact contract: master207A.tex:18881 lem:hyp-whole-interior; reading [18880, 18898]; Blueprint-only exact contract: master207A.tex:18900 thm:hyp-thick-certificate; reading [18899, 18915] | no |
| `DifferentialGeometry.Geometry.Hyperbolic.mostow_prasad` | master207A.tex:12497 `found:hyp-mostow-prasad` [12496–12547]; master207A.tex:15393 `thm:mostow-full-marked-producer` [15392–15423] | Blueprint-only exact adapter. Blueprint-only exact contract: master207A.tex:12497 found:hyp-mostow-prasad; reading [12496, 12547]; Blueprint-only exact contract: master207A.tex:15393 thm:mostow-full-marked-producer; reading [15392, 15423] | no |
| `DifferentialGeometry.Geometry.exists_pullback_metric_of_finite_diffeomorph` | master207A.tex:24827 `lem:collapse-finite-derivative-ledger` [24826–24861] | Blueprint-only exact adapter. Blueprint-only exact contract: master207A.tex:24827 lem:collapse-finite-derivative-ledger; reading [24826, 24861] | no |
| `GC.Geometry.closed_nonnegative_sectional_classification` | master207A.tex:29440 `thm:collapse-compact-finite-classification` [29439–29530] | Primary context checked; exact adapter remains admitted. Blueprint 207 A:LFR53, 29439–29530; Chow–Lu–Ni, Hamilton’s Ricci Flow (GSM77), source label seac 3-manifolds with nonnegative curvature, TeX 18472–18708. | yes |
| `GC.GraphManifold.exists_geometric_decomposition_of_prime_rawGraphPresentation` | master207A.tex:9468 `thm:graph-actual-relative-good-blocks` [9467–9540]; master207A.tex:9543 `cor:graph-terminal-seifert-list` [9542–9579]; master207A.tex:10379 `thm:graph-marked-geometric-endpoint` [10378–10431] | Blueprint-only exact adapter. Blueprint-only exact contract: master207A.tex:9468 thm:graph-actual-relative-good-blocks; reading [9467, 9540]; Blueprint-only exact contract: master207A.tex:9543 cor:graph-terminal-seifert-list; reading [9542, 9579]; Blueprint-only exact contract: master207A.tex:10379 thm:graph-marked-geometric-endpoint; reading [10378, 10431] | no |
| `GC.GraphManifold.exists_prime_geometric_decomposition_of_hyperbolicOrGraph` | master207B.tex:11896 `found:transport-relative-primes` [11895–11906]; master207B.tex:11970 `found:transport-good-blocks` [11969–11979]; master207B.tex:11990 `prop:transport-essential-late-tori` [11989–12010]; master207B.tex:12011 `prop:transport-prime-late-factors` [12010–12036]; master207B.tex:12460 `cor:graph-audited-late-binding` [12459–12497] | Blueprint-only exact adapter. Blueprint-only exact contract: master207B.tex:11896 found:transport-relative-primes; reading [11895, 11906]; Blueprint-only exact contract: master207B.tex:11970 found:transport-good-blocks; reading [11969, 11979]; Blueprint-only exact contract: master207B.tex:11990 prop:transport-essential-late-tori; reading [11989, 12010]; Blueprint-only exact contract: master207B.tex:12011 prop:transport-prime-late-factors; reading [12010, 12036]; Blueprint-only exact contract: master207B.tex:12460 cor:graph-audited-late-binding; reading [12459, 12497] | yes |
| `GC.GraphManifold.rawGraphPresentation_of_flat` | master207B.tex:7477 `found:fibration-topological-closure` [7476–7508] | Blueprint-only exact adapter. Blueprint 207 B:FC41, 7476–7508 | yes |
| `GC.GraphManifold.rawGraphPresentation_of_sphere_summand` | master207A.tex:9468 `thm:graph-actual-relative-good-blocks` [9467–9540] | Primary context checked; exact adapter remains admitted. Matveev2007 Definition2.4.1/Propositions2.4.2–2.4.3, printed84–85/PDF96–97, freshly read; Blueprint RG05 A:9467–9540 and R07 A:8379–8387. | no |
| `GC.GraphManifold.rawGraphPresentation_of_sphericalProduct` | master207B.tex:7477 `found:fibration-topological-closure` [7476–7508] | Blueprint-only exact adapter. Blueprint 207 B:FC41, 7476–7508 | yes |
| `GC.GraphManifold.rawGraphPresentation_of_sphericalSpaceForm` | master207B.tex:7477 `found:fibration-topological-closure` [7476–7508] | Blueprint-only exact adapter. Blueprint 207 B:FC41, 7476–7508 | yes |
| `GC.GraphManifold.sphere_split_of_rawGraphPresentation` | master207A.tex:9468 `thm:graph-actual-relative-good-blocks` [9467–9540] | Primary context checked; exact adapter remains admitted. Blueprint 207 A:8277–8387, R02/R07; A:9467–9540, RG05.; Hatcher archived 61-page notes, Theorem 1.5, printed 5–8 / PDF 6–9; splitting definitions printed 3–4 / PDF 4–5. | no |
| `GC.LongTime.exists_attained_leastExteriorDiskArea` | master207A.tex:18306 `lem:ambient-fixed-boundary-minimizer` [18305–18348] | Primary context checked; exact adapter remains admitted. Blueprint207 master207A.tex:18306 lem:ambient-fixed-boundary-minimizer; reading [18305, 18348]; Meeks–Yau1982 MathZ Theorems1–2, printed153–158/PDF4–9, visually read. Exact evolving-exterior/fixed-parameter application remains admitted. | yes |
| `GC.LongTime.exists_late_cut_family` | master207A.tex:17981 `thm:hyp-actual-persistent-family-producer` [17980–18028]; master207A.tex:31561 `lem:collapse-actual-slow-cusp-truncations` [31560–31636]; master207A.tex:31638 `lem:collapse-intrinsic-ambient-scale-equality` [31637–31677]; master207A.tex:31679 `lem:collapse-boundary-near-all-radii` [31678–31714]; master207A.tex:31716 `lem:collapse-actual-large-radius-exclusion` [31715–31756]; master207A.tex:31758 `prop:collapse-actual-carrier-whole-ball-estimates` [31757–31800]; master207A.tex:31802 `thm:collapse-actual-late-thin-graph-carriers` [31801–31845] | Blueprint-only exact adapter. Blueprint207 master207A.tex:17981 thm:hyp-actual-persistent-family-producer; reading [17980, 18028]; Blueprint207 master207A.tex:31561 lem:collapse-actual-slow-cusp-truncations; reading [31560, 31636]; Blueprint207 master207A.tex:31638 lem:collapse-intrinsic-ambient-scale-equality; reading [31637, 31677]; Blueprint207 master207A.tex:31679 lem:collapse-boundary-near-all-radii; reading [31678, 31714]; Blueprint207 master207A.tex:31716 lem:collapse-actual-large-radius-exclusion; reading [31715, 31756]; Blueprint207 master207A.tex:31758 prop:collapse-actual-carrier-whole-ball-estimates; reading [31757, 31800]; Blueprint207 master207A.tex:31802 thm:collapse-actual-late-thin-graph-carriers; reading [31801, 31845]; Perelman II sections7.3–7.4 TeX1091–1181; KL Theorem92.3 and Remarks92.2–92.6 printed2824–2825/PDF238–239. Concrete persistence/truncation/cut identification contract is Blueprint-only. | yes |
| `GC.LongTime.exists_local_upper_barrier_of_exteriorDiskArea` | master207A.tex:18561 `lem:ambient-area-upper-barriers` [18560–18610] | Blueprint-only exact adapter. Blueprint207 master207A.tex:18561 lem:ambient-area-upper-barriers; reading [18560, 18610]; Perelman II TeX1128–1130 (post-surgery least-area persistence); Hamilton1999 sections11–12 printed716–728/PDF22–34 supply related normalized free-boundary context. Exact IMS fixed-boundary same-flow contract is Blueprint-only. | yes |
| `GC.LongTime.exists_primitive_meridian_of_compressible_seam` | master207A.tex:17981 `thm:hyp-actual-persistent-family-producer` [17980–18028]; master207A.tex:18203 `lem:ambient-exterior-kernels` [18202–18253]; master207A.tex:18255 `lem:ambient-prescribed-meridian` [18254–18304] | Blueprint-only exact adapter. Blueprint207 master207A.tex:17981 thm:hyp-actual-persistent-family-producer; reading [17980, 18028]; Blueprint207 master207A.tex:18203 lem:ambient-exterior-kernels; reading [18202, 18253]; Blueprint207 master207A.tex:18255 lem:ambient-prescribed-meridian; reading [18254, 18304]; Perelman II TeX1128–1130 (post-surgery least-area persistence); Hamilton1999 sections11–12 printed716–728/PDF22–34 supply related normalized free-boundary context. Exact IMS fixed-boundary same-flow contract is Blueprint-only. | yes |
| `GC.LongTime.exists_surgery_with_decaying_accuracy` | master207A.tex:18726 `lem:ambient-audit-profile-carrier` [18725–18793] | Primary context checked; exact adapter remains admitted. Blueprint207 master207A.tex:18726 lem:ambient-audit-profile-carrier; reading [18725, 18793]; KL Definition77.1/Proposition77.2 and section80: printed2770–2771,2784–2787/PDF184–185,198–201; Proposition85.1 and diagonal convention printed2795,2799–2800/PDF209,213–214; Remark86.9 printed2804/PDF218. | yes |
| `GC.LongTime.late_derivative_tests_of_flow` | master207A.tex:31314 `lem:collapse-macroscopic-whole-ball` [31313–31378]; master207A.tex:31380 `lem:collapse-microscopic-whole-ball` [31379–31427]; master207A.tex:31429 `prop:collapse-ambient-whole-ball-derivatives` [31428–31492]; master207A.tex:31494 `cor:collapse-normalized-whole-ball` [31493–31559]; master207A.tex:31679 `lem:collapse-boundary-near-all-radii` [31678–31714]; master207A.tex:31716 `lem:collapse-actual-large-radius-exclusion` [31715–31756]; master207A.tex:31758 `prop:collapse-actual-carrier-whole-ball-estimates` [31757–31800] | Primary context checked; exact adapter remains admitted. Blueprint207 master207A.tex:31314 lem:collapse-macroscopic-whole-ball; reading [31313, 31378]; Blueprint207 master207A.tex:31380 lem:collapse-microscopic-whole-ball; reading [31379, 31427]; Blueprint207 master207A.tex:31429 prop:collapse-ambient-whole-ball-derivatives; reading [31428, 31492]; Blueprint207 master207A.tex:31494 cor:collapse-normalized-whole-ball; reading [31493, 31559]; Blueprint207 master207A.tex:31679 lem:collapse-boundary-near-all-radii; reading [31678, 31714]; Blueprint207 master207A.tex:31716 lem:collapse-actual-large-radius-exclusion; reading [31715, 31756]; Blueprint207 master207A.tex:31758 prop:collapse-actual-carrier-whole-ball-estimates; reading [31757, 31800]; KL Lemma70.1 proof and Lemma70.2 statement printed2751/PDF165; Corollary81.3/Propositions84.1–84.2 printed2788–2794/PDF202–208; Lemma92.13 printed2827–2828/PDF241–242. Whole-ball and all-radius promotion remain WBD/TCF adapters. | yes |
| `GC.LongTime.local_disk_comparisons_of_cusp_exterior` | master207A.tex:18482 `lem:ambient-common-disk-carrier` [18481–18533]; master207A.tex:18535 `lem:ambient-area-continuity` [18534–18559] | Blueprint-only exact adapter. Blueprint207 master207A.tex:18482 lem:ambient-common-disk-carrier; reading [18481, 18533]; Blueprint207 master207A.tex:18535 lem:ambient-area-continuity; reading [18534, 18559]; Perelman II TeX1128–1130 (post-surgery least-area persistence); Hamilton1999 sections11–12 printed716–728/PDF22–34 supply related normalized free-boundary context. Exact IMS fixed-boundary same-flow contract is Blueprint-only. | yes |

Source-file hashes and read limits are in [source_checks_2026_09_29.json](evidence/source_checks_2026_09_29.json) and individual crosswalk `source_checks` fields. KL14 Theorem 16.1 is **Blueprint-only**, never represented as a fresh primary reading. The citation typo around A:31783–31792 is corrected; those lines are in TCF05, despite the task’s TCF06 parenthetical.

## Per-task result

| Task | Status | Delivered / remaining |
| --- | --- | --- |
| 0 environment/gate | proved tooling checks; literal silence not met | 4.33.1 root verified before proof replacement; parameter pins, independent admission registry, checked authored/generated types and axiom closures, exact locator validation, fresh-audit path, all negative fixtures and positive application markers installed. |
| 1 barrier | proved | General upper-support logarithmic contradiction; shifted adapter; redundant unconsumed variants removed. |
| 2.1–2.5, 2.7 | proved | Curvature radius positive/infinite characterization, LC89, disk-area continuity, boundary/vacuity lemmas; intermediate count12 verified. |
| 2.6 optional compactness | not-started | Finite-order coefficient compactness proof and optional binder weakening were not installed; original admission retained. |
| 3.1–3.8 | proved / conditional / admitted as appropriate | Unused atlas/radius assumptions removed, finite-scale threshold introduced, obstruction/attainment separated, matching proved, binder style unified, hyperbolic builder renamed. Finite-regularity optional changes excluded. |
| 3.9 records | proved consistency checks | Exact label/title/range/hash validator passes; current source conventions and irreducibility obligation recorded. |
| 4.1 admissible flow | admitted; primary KL context checked | User-approved analytic profile includes the missing KL85/86.9 controls. Construction and arbitrary-metric rescaling/retained-history adapter remain admitted. |
| 4.2 persistent geometry | definition + admitted producer; Blueprint-only exact adapter | Actual models, finite disjoint persistent embeddings, exhausting cores, speed/unscathed transport, exact truncations and seam-image matching. |
| 4.3–4.4 derivatives/cuts | conditional composition + admitted analytic producer | Compact bounds and finite-family LC89 selection proved; actual whole-ball/all-radius analytic promotion remains WBD/TCF admission. |
| 4.5 disk chain | definitions / proved glue / four admissions | Exact persistent exterior and primitive meridian; attained disks, comparisons, barriers separated; smooth disk reparametrization proved. Some compressible port is selected, not falsely identified with the original failed seam. |
| 4.6 selected flow and endpoint | conditional | Primary admissible theorem and old compatibility form proved. K/flow/sequence/A/tolerance order and endpoint preserved. |
| 5.1 transport and T6 | proved transport / conditional T6 | Raw and geometric transport, injection cancellation, closed sphere-summand record and two-admission prime split installed. |
| 5.1 full mixed/T7 split | attempted-and-failed to complete interfaces | No complete relative sphere/cap/port + good Seifert block API was obtained. Mixed/T7 coarse admissions remain. Irreducibility prototype stayed in scratch; no unused admission or conclusion-shaped good-block alias installed. |
| 5.2 | proved compact bound; local-fibration split not-started | Compact norm bound is consumed by LC89; genuine LC87 zero/edge/slim/circle packets and compatible cloud assembly are not represented, so the finite-scale threshold remains admitted. |
| 5.3 | not-started beyond preserved contract and matching | Thin-collar/local-fibration boundary producer decomposition not installed. Intrinsic geometry, one-sided derivatives and actual external labels retained. |
| 5.4 | conditional + four explicit admissions | Complete nonnegative model classification and spherical/spherical-product/flat graph suppliers installed; original theorem is a proved corollary. A general torus-bundle presentation API is not installed. |
| 6.1,6.2,6.4–6.6,6.8–6.10 | proved/definition/documentation | Dimension-specific volume name, topology namespace, constants, generic compact manifold, NoCuts decomposition, removed unused threshold wrapper, capstone move and current reviews. Torus cylinder lemma placed in a NEW adjacent leaf because the requested TorusCylinder file is protected baseline. |
| 6.3 | proved norm/iteration API; finite-C realization not-started | Four requested norm/iteration bridges and continuity/compact bounds proved; finite-C cusp-error regularity needs a finite-order tensor derivative bridge. |
| 6.7 optional names | not-started intentionally | Existing HyperbolicOrCollapsed and late-test names retained; no obligatory semantic repair depends on those contested renames. |
| 7 evidence/delivery | see receipt and delivery record | Public axiom transcript, per-module fresh builds/lint, negative fixtures, manifest diff, source locators, statement comparison, and branch delivery recorded below. |

The exact per-public-declaration proved/conditional/admitted table is [DECLARATION_STATUS_2026_09_30.md](DECLARATION_STATUS_2026_09_30.md). It includes definitions separately. Scratch attempts are not counted as installed proofs.

## Quantifiers, actual witnesses and source distinctions

The endpoint and its 155-module basis are byte-preserved. ONE flow is chosen after K; ANY cofinal sequence of nonempty regular slices is tested; ONE A is chosen for that sequence before w and N. The thin metric is induced by the actual normalized cut map, and tests stay at Perelman’s curvature radius and on the whole uncapped ball. Nonnegative closed components retain a separate branch. Physical areas use the same flow’s postStage/postMetric, including event times; scalar shift c is positive.

The minimal obstruction predicate is proved equivalent to actual ambient incompressibility. It remains a consequence interface, while the separated geometric producers retain the exact persistent exterior and a fixed primitive meridian. IMS01–02 permit choosing another compressible port in the same persistent family. Local comparisons and barriers remain admitted at surgery times; post-event notation alone does not prove them.

Primary reading actually used: Perelman II TeX1091–1181; KL archived2013-02-20 profile/existence passages, 85.1/86.9, local curvature estimates and 92.3/92.13; Meeks–Yau1982 fixed-boundary Theorems1–2; Hamilton1999 §§11–12 as normalized free-boundary context; Hatcher1.5/1.6; Matveev2007 Definition2.4.1/Propositions2.4.2–3; GSM77’s closed nonnegative classification section. Exact page/line/hash and bounded errata/reuse limits are in the source record. Mostow and the geometric mixed/local-collapse adapters are not claimed to have fresh complete primary proofs here.

## Crosswalk, fixtures and statement comparison

Crosswalk output: `Crosswalk locator validator: 214 entries, zero failures.`
Negative fixtures: `SKELETON_NEGATIVE_TESTS_PASS: 11 cases`. All required error paths and valid controls passed. The skipKernelTC fixture compiles and passes the environment-only check; the hardened source layer rejects its forbidden option. This layer distinction is retained in the evidence.

```text
standard: PASS
unchecked-name: PASS (Unchecked declaration)
axiom: PASS (Unexpected axiom or unsafe declaration)
unsafe: PASS (Unexpected axiom or unsafe declaration)
type-admission: PASS (Admission in declaration type)
external-axiom: PASS (Unexpected axiom ExternalSeed.seed)
unregistered: PASS (Unregistered direct admission)
registered: PASS
count: PASS (Expected 1 direct admissions)
empty: PASS (Empty skeleton audit)
skip-kernel: PASS (compiled fixture rejected by static set_option gate)
SKELETON_NEGATIVE_TESTS_PASS: 11 cases
```

[Interface receipt](evidence/interfaces/verification.json): three actual application markers, standard-axiom checks, and definitional equality of the old area contract and proved replacement. [Manifest diff](evidence/improvement/manifest.diff) gives the hand-reviewed registered set and input hashes. [Statement changes](STATEMENT_CHANGES_2026_09_30.md) quotes every changed/new public type and changed definition body side by side. The report does not treat type-preserving API renames as new mathematical theorems.

## Not performed / preserved authorization boundary

- Full Task 5 mixed relative good-block/Seifert/metric/gluing decomposition, LC87 local packets, boundary-collar incorporation, and general torus-bundle supplier remain incomplete. Correct intermediate witnesses were not replaced by endpoint aliases.
- The finite-C cusp-error realization and optional finite-order compactness proof remain open. Existing smooth-only connection/curvature APIs are not silently applied to finite-C tensors.
- No removal of TorusGluing.torusOrientation; no baseline factorization TorusGluing/TorusPairing or GeometricDecomposition/TorusDecomposition; no baseline boundary-reversal or full-boundary-component field changes.
- No PC-side profile-retaining global producer change, no finite-order generalization of leviCivitaConnectionOfMetric/metricRm04At/riemannianEDistOf, and no edits to protected check.py/module_layout.py. These need the additional baseline authorization identified in the request.
- No Blueprint revision. Proposed future text: add an explicit hyperbolic-core irreducibility supplier behind AT16, retain the G10 E1-to-JSJ adapter with T²×I Euclidean, and cite Perelman §7.4 for the separate nonnegative branch. These are documentation proposals only.
- No PDF/Overleaf build is claimed. The outer Blueprint consistency audit completed with exit 0 and BLUEPRINT_STATIC_OK; see [its exact outcome](evidence/improvement/blueprint_audit_status.json). It is not a Lean check.
- `git diff --check` source/document checks are recorded separately from raw compiler logs; unmodified compiler trailing spaces in evidence are preserved verbatim.

## Public axiom transcript

The following is copied verbatim from the final `#print axioms` driver. It covers every public authored skeleton declaration, hence every added/changed public API, plus the endpoint explicitly. Subsets of the three ordinary axioms are normal; `sorryAx` marks conditional/admitted closure.

```text
'DifferentialGeometry.CheegerGromovCompactness.exists_bilinear_form_limit_subsequence_of_bounded_derivatives' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Analysis.hasLocalSmoothUpperBarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Analysis.not_nonnegative_of_upper_barriers_div_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_pi_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Analysis.false_of_area_upper_barriers' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_radius_bound_of_volume_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.ballVolume' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.euclideanThreeUnitBallVolume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.volumeCollapsedAtCurvatureScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureDerivativesControlled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureRadius_eq_top_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureDerivativesControlled_mono_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.volumeCollapsedAtCurvatureScale_of_curvatureRadius_eq_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureDerivativesControlled_mono_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.curvatureDerivativesControlled_anti_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.volumeCollapsedAtCurvatureScale_iff_toReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.cuspMetricError' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.cuspMetricErrorBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.CuspEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.NearlyCuspidalBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.distanceToBoundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.boundaryVolumeCollapsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.CuspEmbedding.weaken' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.NearlyCuspidalBoundary.weaken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.distanceToBoundary_eq_top_of_boundary_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.CuspEmbedding.restrictOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.NearlyCuspidalBoundary.restrictOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.closedCollapseHypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.boundaryCollapseHypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.staticCollapseHypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.volumeCollapsedAtCurvatureScale_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.closedCollapseHypotheses_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.boundaryCollapseHypotheses_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.not_boundaryCollapseHypotheses_of_boundary_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.staticCollapseHypotheses_exclusive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_rawGraphPresentation_of_nonnegative' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_closed_graph_threshold_of_finite_scales' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_closed_graph_threshold' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.RawGraphPresentation.external_matching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_boundary_graph_threshold' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_graph_threshold' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.cutPieceMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.isInducedCutMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Collapse.HyperbolicOrCollapsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.geometrizes_of_hyperbolicOrCollapsed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.boundaryBufferDistance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.staticDerivativeOrder' does not depend on any axioms
'DifferentialGeometry.Geometry.Collapse.exists_common_curvature_derivative_bound_for_families' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_common_curvature_derivative_bound_of_volume_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_common_curvature_derivative_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Collapse.exists_common_curvature_derivative_bound_of_eventual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Riemannian.gInner_sq_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Connection.metricCovariantDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Connection.iteratedMetricCovariantDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.curvatureDerivativeNorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.curvatureDerivativeNorm_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.curvatureDerivativeNorm_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.curvatureDerivativeNorm_sq_eq_normSq0S' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.iteratedCurvatureTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.iteratedMetricCovariantDerivative_rm04_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.continuous_curvatureDerivativeNorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Curvature.exists_bound_curvatureDerivativeNorm_of_compactSpace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GC.LongTime.hasCommonNeckAccuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasCommonNeckAccuracy.bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasSmallParabolicCurvature' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.AnalyticSurgeryProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasAnalyticAdmissibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.AnalyticSurgeryProfile.commonNeckAccuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.AnalyticSurgeryProfile.largerBallAccuracy_on_late_half_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GC.LongTime.exists_surgery_with_decaying_accuracy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.LongTime.PersistentCuspExterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.PersistentCuspExterior.region' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.PrescribedCuspMeridian' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.PrescribedCuspMeridian.loopAfter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.exists_primitive_meridian_of_compressible_seam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.exists_attained_leastExteriorDiskArea' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.LongTime.local_disk_comparisons_of_cusp_exterior' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.exists_local_upper_barrier_of_exteriorDiskArea' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.incompressible_of_shifted_area_barriers' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasExteriorDiskComparisonsAfter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.continuousOn_exteriorDiskArea_of_local_comparisons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GC.LongTime.postStage' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.postMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.postStage_regularSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.postMetric_regularSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.exteriorDiskArea' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.exteriorDiskArea_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.exteriorDiskArea_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasExteriorDiskMinimizersAfter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Endpoint.geometrization' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.Endpoint.geometrization_conjecture' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.Endpoint.smooth_geometrization_conjecture' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.componentMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasThinVolumeGeometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.HyperbolicOrThin' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.LateCutFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.LateCutFamily.thinIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.LateCutFamily.hasEventualDerivativeBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.LateCutFamily.exists_common_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasThinVolumeGeometry.collapseHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.HyperbolicOrThin.toHyperbolicOrCollapsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.LateCutFamily.exists_late_tests_of_derivative_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GC.LongTime.exists_late_cut_family' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.LongTime.late_derivative_tests_of_flow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.LongTime.hasExteriorAreaObstructionAfter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasAttainedExteriorAreaObstructionAfter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasAttainedExteriorAreaObstructionAfter.toObstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GC.LongTime.hasExteriorAreaObstructionAfter_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasLateSequenceTests' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasExteriorAreaObstructionAfter_of_producers' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.hasLateSequenceTests_of_thick_thin_and_obstruction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.exists_admissible_surgery_with_late_sequence_tests' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.exists_surgery_with_late_sequence_tests' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.components_geometrize_of_late_sequence_tests' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.LongTime.geometrizes_of_metric' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.LongTime.lateDerivativeOrder' does not depend on any axioms
'GC.LongTime.staticDerivativeOrder_le_lateDerivativeOrder' does not depend on any axioms
'GC.LongTime.PersistentModelPatch' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.PersistentHyperbolicCores' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasPersistentHyperbolicCores' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.history' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.metric' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.normalizedMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.curvatureOneMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.RegularSlice.initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.hasArbitrarilyLateNonemptySlices' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.exists_regular_slice_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.empty_slice_or_arbitrarily_late' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.exists_common_late_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.LongTime.geometrizes_of_late_slice_supply' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.CuspHalfSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.cuspDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.cuspDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.cusp_constant_sectional_curvature' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.has_hyperbolic_atlas_of_curvature_neg_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.hyperbolicGeometricStructure' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.hyperbolicGeometricStructure_model' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.hasConstantSectionalCurvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.mostow_prasad' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.exists_riemannianBallOf_subset_of_mem_nhds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.exists_pullback_metric_of_finite_diffeomorph' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.exists_pullback_metric_of_diffeomorph_one_order_higher' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.exists_pullback_metric_of_diffeomorph_three_orders_lower' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.isExteriorSpanningDisk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.exteriorDiskAreaOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.exteriorDiskAreaOn_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.continuousOn_leastExteriorDiskArea_of_local_disk_comparisons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea_eq_zero_of_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.exists_smooth_disk_reparametrization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.isExteriorSpanningDisk.comp_smooth_disk_reparametrization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.MinimalSurface.isExteriorSpanningDisk.area_comp_reparametrization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.rawGraphPresentation_of_sphericalSpaceForm' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.rawGraphPresentation_of_sphericalProduct' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.rawGraphPresentation_of_flat' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.Geometry.closed_nonnegative_sectional_classification' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Topology.connected_subset_finite_closed_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Topology.finite_connected_partitions_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ContinuousMap.fundamentalGroup_map_injective_of_area_obstructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Topology.ModelBoundaryKind' does not depend on any axioms
'DifferentialGeometry.Topology.ModelBoundaryKind.Space' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Topology.ModelBoundaryKind.model' depends on axioms: [propext, Classical.choice, Quot.sound]
'DifferentialGeometry.Topology.CompactModelManifold' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.SphereSummand' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.SphereSummand.ofPrimeDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Endpoint.SmoothAssembly.Incompressible.toPiece' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Endpoint.GeometricDecomposition.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.SurfaceModel' does not depend on any axioms
'GC.GraphManifold.SurfaceModel.Space' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.SurfaceModel.model' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.CompactSurface' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.CircleFibration' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori.torusMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori.image' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori.torusMap_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori.boundaryMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori.torusMap_isEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.BoundaryTori.incompressible' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.TorusPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.TorusPairing.QuotientSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.TorusPairing.quotientMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.RawGraphPresentation' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.isHyperbolicInteriorGeometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.HyperbolicOrGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.exists_prime_decomposition_of_rawGraphPresentation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.exists_geometric_decomposition_of_prime_rawGraphPresentation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.geometrizes_of_rawGraphPresentation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.exists_prime_geometric_decomposition_of_hyperbolicOrGraph' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.geometrizes_of_hyperbolicOrGraph' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GC.GraphManifold.sphere_split_of_rawGraphPresentation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.rawGraphPresentation_of_sphere_summand' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'GC.GraphManifold.BoundaryTori.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.GraphManifold.RawGraphPresentation.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.torusAt_injective_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.componentCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.TorusDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.TorusDecomposition.component' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Topology.TorusDecomposition.toGeometricDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Endpoint.NoCuts.torusDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'GC.Endpoint.geometrization' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Delivery

Implementation commit and verified push: `e59c2630acd0d5a8230234db773309189d4d4a5a`. The final dated outer HANDOFF records both the implementation and report commits and the verified remote branch head, avoiding a self-referential commit hash inside its own contents.

## Verdict

Mathematical soundness: proved leaves have ordinary axiom closure; admitted producers and their conditional consumers remain explicit. API: the approved flow split and multiple structural repairs are installed, while the listed Task 5/finite-C interfaces remain incomplete. Compiler: unified root and fresh declaration audit pass; selected declaration linters and proof-only fresh leaf silence are separately checked; literal silent-root acceptance is not met.

**Not accepted** as completion of the entire requested task. Minimum remaining work is the listed full Task 5/finite-C interfaces plus resolution of the literal zero-diagnostic requirement within the protected-baseline authorization boundary. This verdict does not retract the passing admission-aware skeleton build or claim the admitted mathematics false.

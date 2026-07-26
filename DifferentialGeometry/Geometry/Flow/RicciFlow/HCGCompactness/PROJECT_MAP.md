# HCG COMPACTNESS — PROJECT MAP (single entry point)

> **Wider program (2026-07-05):** this map covers the HCG compactness lane.
> The program-level plans sit one directory up:
> `../DimensionThree/HAM3_BLACKBOX_PLAN.md` (the original 8-frontier audit for
> `ham3_main`; three strict frontiers remain: #2, #3, and #5;
> short-time, Perelman noncollapse, and both space-form directions are closed)
> and `../POINCARE_PLAN.md` (the Poincaré-endpoint master plan + infrastructure gap
> list).  HCG compactness is `ham3_cgh_limit`'s producer and Morgan–Tian
> `converge2`'s counterpart inside that program.

> **Merge (2026-07-11):** the `qinz1yang` fork PROVED `ricci_flow_short_time_existence`
> (sorry-free, axiom-clean, joint smoothness to `t=0`); merge + forward plan
> (U-track uniqueness, E-track `extends_of_rmBounded`) = `../SHORTTIME_MERGE_PLAN.md`.
>
> **Migration (2026-07-07):** work moved from Claude (Fable) to Codex.  The
> full state/next-work/long-term handoff is the repo-root `CODEX_HANDOFF.md`
> (includes the durable lessons formerly held in the assistant's private
> memory).  New sessions: read `AGENTS.md` → this map → `CODEX_HANDOFF.md`.

Created 2026-07-05.  **Read this first**; it is the one place that ties the whole
Hamilton–Cheeger–Gromov compactness project together.  Keep it current: when an
endpoint, lane, or plan file changes, update the pointer here (one line), not by
writing a new overview elsewhere.

## 1. Goal and theorem tree (MSM135 Chapters 3–4)

```
Thm 3.10  Ricci-flow solution compactness            [unconditional endpoint 0%;
                                                       conditional wrapper checked]
  ⇐ Thm 3.9  metric compactness                      [Ch4 line, proved in book Ch4]
  ⇐ Lemma 3.11  whole-window C^p metric bounds       [DONE sorry-free, hShi = cited hyp]
  ⇐ hShi  Shi derivative estimates                   [CITED boundary, not a proof obligation]

Thm 3.9 (Ch4 proof) = Step A (good coverings, DONE)
                    → Step B/C selected producer route (DONE: concrete
                      `StepB1RawInput`, 5/5 fields; the separately named
                      textbook B1 statement remains unstated, 0%)
                    → Step C historical arbitrary-recurrence route (separate,
                      incomplete, and not required by the selected producer)
                    → Step D (direct limit + assembly, DONE conditionally)
                    + F-track engines (F1–F13, 100%)
```

## 2. Endpoints and their `sorry`s (report progress ONLY against these)

| Endpoint | Where | Status |
|---|---|---|
| **Conditional Thm 3.9** `MetricCompactnessInputs.metricCompactness` | `C4/MetricCompactnessEndpoint.lean` | **100% checked.**  `MetricCompactBase.exists_b1_raw` produces all 5/5 fields, `compactness_of_b1` performs Step-D assembly, and `MetricCompactnessConclusion.ofSeqSubseq` transports the nested subsequence conclusion back to the original sequence.  Focused check and exact targeted refresh are green. |
| Unconditional Thm 3.9 `metricCompactness` | `MetricCompactness.lean` | 0%; the conditional endpoint is available, but the native CGT, Bishop–Gromov/uniform-packing, [H6], and connectedness producers needed to instantiate it remain external to this Chapter 4 assembly. |
| Conditional Thm 3.10 `solutionComp_cond` / `compactnessSol_cond` | `C4/SolutionCompactnessInputs.lean` + `HamiltonCompactness.lean` | checked consumer of the now-complete conditional Thm 3.9 plus concrete `FlowUpgradeData`; it does not produce that P4 input or prove unconditional Thm 3.10 |
| MSM135 Thm 3.10 `compactnessSol` | `HamiltonCompactness.lean` + `P4_CONV_PLAN.md` | exact open-interval target is stated with one visible P4 `sorry`; theorem 0%. `open_upgrade_of_raw` checks the complete consumer path, the concrete Step-D canonical provenance lane is closed, `srcCovLip_of_soln` is focused/exact-green, and `open_upgrade_canon` is focused/exact-green. The HCG-facing complete-Shi assembly is exact-green. Its trusted foundation includes the exact arbitrary-dimensional fixed-basis Hamilton identity, fixed global residual recursion, direct curvature tower, and smooth-cutoff generic Bernstein consumer. Route B-prime is selected for the remaining no-extra-input Shi producer: the local upper-support maximum principle, smooth/barrier cutoff data boundary, basepoint-free completeness, point-pair Hopf--Rinow, finite closed-eball compactness, fixed-path Ricci-flow length variation, and the quantifier-corrected point-centered barrier Bernstein consumer are checked. The complete fixed-metric Calabi support is exact-current. The evolving-distance source proof is mathematically assembled and placeholder-free, but `scaledDist_calabiUpperSupport_of_sol` remains theorem-level 0% because its final private orchestrator deterministically times out during `whnf`; all seven constituent helpers elaborate. `DISTANCE_BARRIER_PERF_CONSULT.md` records the surgical Lean-performance question. The later solution-generated barrier cutoff and final `MovingShiOpen` switch remain unverified; `MovingShiOpen` still consumes the legacy sorry-backed `estimate_complete`. |
| Lemma 3.11 | capstone `covOrderBound_of_soln` chain | DONE sorry-free (hShi hypothesis) |

## 3. Live lanes and their entry documents

> **Tree-wide (not HCG-specific):** the outstanding merge of the upstream mainline
> `qinz/reunion` is planned in `DifferentialGeometry/REUNION_MERGE_PLAN.md`.  It also
> records the standing ruling that `InnerProductSpace ℝ E` on the *model* space is the
> wrong assumption — stay on `[NormedSpace ℝ E]`, and never compensate a newly-demanded
> instance downstream; fix the producer or `omit` the unused variable instead.

| Lane | Entry plan | State |
|---|---|---|
| Ch4 Step B/C (selected B1 producer route) | `C4/CHAPTER4_PLAN.md` + `C4/B1_STAGE_MAP_RULING.md` + `C4/StepCStageComparison.md` + `C4/StepCStageDiagonal.md` + `C4/StepCStageInjectivity.md` + `C4/StepCStageMaster.md` + `C4/StepB1MetricLocal.md` + `C4/StepB1MetricIntrinsic.md` + `C4/StepB1MetricCarrier.md` + `C4/StepB1RawProducer.md` | **100% checked for the selected canonical framed producer route.**  The support capstone, full stage-master DAG, forward intrinsic tail, exact-`Function.invFunOn` reverse tail, two-carrier capstone, and `MetricCompactBase.exists_b1_raw` are focused/exact-green; the unchanged `StepB1RawInput` closes 5/5 fields for one global finite-stage map.  The separately named textbook B1 theorem remains unstated at 0%, and the historical full Step-C arbitrary recurrence remains separate/incomplete. |
| Ch4 Step D | **`C4/STEPD_PLAN.md`** + `C4/StepDLimitMetrics.md` + `C4/StepDAssembly.md` + `C4/MetricCompactnessEndpoint.md` | **100% checked for the concrete conditional route.** `compactness_canon` now proves its canonical whole-source metric-equivalence and all-order covariant bounds by joining the `D.close` tail with compact finite-head collars, then transports them through the canonical pullback and nested subsequence. `StepDAssembly` and `MetricCompactnessEndpoint` are focused- and exact-green on the live framed import chain; no `HasCanonBounds` frontier remains. |
| Native [H6] normal-coordinate producer | `C4/B0NormalCoordBounds.md` + `C4/H6NormalCoord.md` | per-center `g_x`-orthonormal normalizer, framed exponential chart/inverse/differential, exact radial-ball correspondence, pullback metric, and framed radial-Jacobi bridge are checked. `StepBInputs.lean` now also focused-checks with canonical framed transition and metric semantics. The active API repair is ordered as radius profile, proper-ball/item-3, transition/overlap, metric-extension/branch stack, then Step-C/B1 readout; it adds no geometric hypothesis. |
| Ch3 P4 producer lane (3.10 ⇐ 3.9) | `P4_CONV_PLAN.md` + `P4_PRODUCER_RULING.md` + `P4_CUTOFF_CONSULT.md` + `DISTANCE_CALABI_CONSULT.md` + `CALABI_BRANCH_CONSULT.md` + **`CALABI_BRANCH_PLAN.md`** + `DISTANCE_BARRIER_PERF_CONSULT.md` + `ConvFieldCanon.md` | fixed-window/open consumer assembly is checked through `open_upgrade_of_raw`; the grow-only `hcovTail` migration is green and the Step-D provenance branch is closed. `rm04Base_of_solution_any`, `e0Residual`, the arbitrary-index fixed successor `resStarNext`, global residual capstone `rmResidual_cost`, direct tower `towerHeatSol_raw`, HCG `rmTowerCost`, constants-first `srcCovLip_of_soln`, and `open_upgrade_canon` are focused- and exact-green. Both the smooth fixed-order `BernsteinTower.estimate_cutoff_at` and family-centered `estimate_barrier_at` are exact-current; the private barrier adapter in `MovingShiOpen` is focused-green. Route B-prime is selected for complete Shi. The full fixed-first Calabi geometry is focused/exact-green through `calabiDist_support`, and the evolving source proof has been factored into seven placeholder-free helpers. Those helpers elaborate, but the three-line `scaledDist_support` orchestration boundary still times out at `whnf` even under a scoped 500000-heartbeat test. This is the active performance consultation frontier, not a mathematical or missing-API gap. `scaledDist_calabiUpperSupport_of_sol`, the solution-generated barrier cutoff, and the final MovingShi switch remain theorem-level 0%. Thm 3.10 stays 0%; dedicated P4 consumer machinery is about 98%, selected Route B-prime producer machinery is about 85%, and whole HCG supporting machinery remains about 60%. |
| Extension lane (interior-restart / Y1 3.11 inputs) | `ExtendShiInputs.md` + `Evolution/ExtendViaUniqueness` notes | active, separate from HCG critical path |
| A0′ volume-overlap producer (unconditional 3.9) | `C4/A0PRIME_VOLUME_PLAN.md` | LIVE 2026-07-25, endpoint `volInput_of_bg` **0%** (nothing above machinery until plan brick B7). Banked sorry-free: B3 (β intrinsic ratio layer past cut locus, `exists_intrRatio`/`intrDens_le_hyp`/`intrCross_anti`/`intrNoConj_min`), B4 (γ `lintegral_cross_le` cross-Chebyshev, new — Mathlib has none), B2 set layer (`SegDom`, star-shape, Hopf–Rinow surjectivity, measurability — past cut locus, no injectivity); B1 discharged by discovery (`ricciLower_of_rm` ∘ `rm04Bound_of_seq`). **Re-mapped single frontier (sharpened by 2026-07-25 read-only scout):** carried as exactly two precise sorrys `segBall_vol_le` (now with the explicit sphere-mass constant σ — orchestrator caught the missing factor, flat-ℝ² counterexample; `segBall_vol_fin` corollary proved) and `segBall_vol_rel` in `Comparison/Volume/SegmentPolar.lean`. Scout verdict: chart-partition route is shortest (the measure is POU-chart-local by construction, per-chart `≤` near-definitional; alternatives collapse onto the same bridge); the genuine frontier = **L1(large-v) cross-chart velocity-differentiability of `expMapIntrinsic`** (no off-zero velocity lemma exists — the cited one was fictional) **+ L2 chart-Jacobian ↔ `curveDensity` identity** (riskiest). Banked since: B5a (weighted non-injective Euclidean area `≤` `image_lintegral_le` + per-chart `vol_le_tsum_supp`; ⊤-sum catch adopted as L5 contract) and B6 (counting core `segBall_card` + explicit `segImult`, consuming the stated frontier sorrys, adds none). **B7 LANDED + ACCEPTED (2026-07-25): `volInput_of_bg` now EXISTS in `C4/VolumeOverlap.lean`** — own content sorry-free, `#print axioms` = standard + one `sorryAx` tracing exactly to the two SegmentPolar frontiers; honest inputs `hcpl : SeqMetricComplete X` + `hconn` (per-member completeness/connectedness the Hopf–Rinow entrypoint needs); dim-1 Ricci-vanishing proved from scratch (helpers pending B8 relocation). **THE LANE FRONTIER DISSOLVED (B5b, 2026-07-25):** L1 was a false wall — `intrinsicFiber_smooth` (Exponential/IntrinsicVelocity.lean) already gives global C∞ velocity-regularity of `expMapIntrinsic` (scout + B2 both missed the producer; memory lesson updated); L2 `exp_density_curve` (chartDensity·|det D(chart∘exp)| = curveDensity of the Jacobi frame) proved sorry-free for ALL v, invertibility- and nonconjugacy-free. Endpoint still **0%** per the §7 honesty rule. B5c landed **L5 = `riemVol_exp_image_le`** (Comparison/Volume/SegmentArea.lean — the manifold-valued non-injective area inequality the frontier was named after; sorry-free, axiom-clean) but correctly reported L6 is from-scratch, not assembly: no absolute `V ≤ σ·hypRadVol` template exists in-tree, and the sharp `N=1` transverse constant (pole-normalized ON parallel frame) is a newly-surfaced sub-frontier — the non-sharp `intrDens_le_hyp` can't give the exact statement (which is equality in flat ℝ²; orchestrator re-verified anisotropy-robustness on `diag(4,1)`). B5d landed the global Gauss factorization core (`velJac_gram_split`/`velJac_density_split`, SegmentGauss.lean, sorry-free) and fully derived the L6 route with exact constants (telescopes on flat + `diag(4,1)`), but L6 needs more sessions: four ordered sub-lemmas remain ((i) `radialJac_eq_vel` atom — stuck only on a trivial `mfderiv (1+·)` fiddle, (ii) change-of-basis `|det C| = √det gₓ`, (iii) sharp `N=1` ON-frame pole limit, (iv) `gₓ^{1/2}` CoV + polar Fubini). B5d2 banked `radialJac_eq_vel` + change-of-basis glue and produced a THREE-ROUTE COLLAPSE onto one named blocker: the **sharp `N=1` transverse pole limit** (in-tree `intrPoleCap` is self-flagged non-sharp; the flat-case equality tolerates no slack). In flight: **B5d3** — exactly that lemma + the step-(c) corollary, via the orchestrator's continuity route (`D(exp)₀ = id` + global C∞ derivative-continuity + Gram continuity). If its three-route fallback fires, the lane is genuinely blocked pending the browser-blocked Pro consult. After (c): (a)-assembly/(b)/(d) measure steps → `segBall_vol_le`; then L7; then B8 + final axiom replay. Running status = plan §8. |
| Space-form / quotient curvature | same-name `.md`s under `Geometry/Metric/Sphere` and `DimensionThree/HamiltonPositiveRicci.md` | **CLOSED, exact-green and axiom-clean;** parallel and unrelated to 3.9/3.10 |

Superseded/historical: `C4/STEPC_HANDOFF.md`, `C4/STEPC_B1_HANDOFF.md` (banners in
file), `PLANNER_HANDOFF.md`, `ARZELA_ASCOLI_PLAN.md` (delivered), `P3_PLAN.md`
(delivered).  Rule (2026-07-05): plan/architecture files live IN THE REPO —
do not leave approved plans only under `~/.claude/plans/`.

## 4. Honest-input audit (2026-07-05, per user request: "严格审查数学上哪些 inputs 是否成立")

Verdicts: **TRUE** = mathematically true as stated under Thm 3.9's hypotheses and
book-faithful; **FIXED** = the pre-audit statement was wrong and was corrected today.

| Input | Book cite | Verdict | Notes |
|---|---|---|---|
| `InjRadiusDecayInput` (A0) | `lbl384` (CGT) | **TRUE statement; backend repair pending** | The decay formula `a·min{ρ,1}^n·e^{−C·d}` matches the book and its constants are uniform in `k`. However, the current `HasInjRadiusAt` backend measures raw model-norm balls; a faithful native instantiation must first migrate `injRadius` to intrinsic tangent balls, equivalently orthonormally framed model balls. |
| `PackingBound` | `lbl387` | **TRUE** | per-radius count `A(r)`; no uniformity trap.  `MetricCompactBase` carries `forall D > 0, PackingBound D`; packing is instantiated only after the single large-`D` choice. |
| `VolumeComparisonInput` (A0') | Bishop–Gromov | **FIXED** | Uncapped-in-`r` multiplicity was **FALSE** (hyperbolic members: `r`-separated counts in `m·r`-balls grow like `e^{(n−1)(m−½)√C₀·r}`).  Now capped at containing scale `m * r ≤ r0`; consumers (`net_multiplicity`, `inter_count`) thread the needed Step-A ratio times `λ[0]` into the cap. |
| `RealizesEdist` | — | plumbing | provable at instantiation from `ProperMetricOn`; not external math. |
| `NormalCoordMetricBoundInput` / `NormalRadiusProfile` | `lbl395` = [H6] Cor 4.12 + CGT compatibility | **conditional consumers checked; native framed producer in progress** | The relative-radius and `g_p` tail consumers are checked. The per-center orthonormal frame, framed chart, exact radial-ball correspondence, pullback metric, and framed Jacobi bridge are proved. Native production still requires the shared input, transition, and injectivity-radius primitives to consume `z |-> exp_x(normalFrame z)` consistently; the current `injRadius` backend uses raw model-norm balls. `C4/H6NormalCoord.md` records the scoped migration route. |
| retired `ExpInverseDerivBoundInput` (S6) | `lbl418` | **REMOVED** | The localized H6 derivative producer replaced the temporary S6 consumer chain.  After the finite source-slot diagonal migrated and a zero-consumer audit passed, the S6 type, compatibility entrypoints, endpoint field, and obsolete selector budget were removed. |
| `IsometryDerivBounds` (F8) | `lbl375` → [H6] §5 | **PROVED producer; finite H6 migration and capstone wiring checked** | `C4/H6_ISOMETRY_DERIV_PLAN.md`: `normal_bounds_on`, fixed-pair/refinement/live-slot extraction, atom/weight packaging, and `exists_atom_lim`/`exists_atom_fin` are checked without S6. Positive interacting-pair extraction, active six-lambda image control, source-local decoded convergence, `activeFill`, the finite source cover, and the global existential-source corollary are checked. No glued weights or chart selector are used. |
| `Item3RadiusAt` / `Item3RadiusTail` | `lbl391/392` ("D large") | **conditional consumer checked; framed backend migration pending** | `radiusScaleTail` and the selected-scale consumers are checked under the current backend. A native book-faithful producer still has to replace the raw `injRadius`/`expMapC2Radius` realization by the framed intrinsic-radius realization before `exists_item3D` can be counted as unconditional geometry. The legacy all-index `Item3RadiusInput` is compatibility-only. |
| `Item3GpScaleAt` / `Item3GpScaleTail` | `lbl383/427` | **CHECKED producer and consumers** | `gpScaleTail` finite-intersects `lambda_window` after packing with the exact `c = 8` budget. Step-C atoms, atom package, and joins consume only `At`/`Tail`; legacy all-index `Item3GpScaleInput` is compatibility-only. |
| `SigmaScaleField` | `lbl383` family | relative branch and readout wiring checked | `normalMinScale` retains the full minimizing branch with its `expRadiusGp` half-floor, and `NormalBranchCage.exists_live_min` specializes it to live centers. The one-shot divisor, post-packing finite-slot tails, physical cage, quarter-ball tail, source-local support readout, and finite source maximum are checked. |
| `CmHessianInput` / selected-branch equivalent | `lbl413`-adjacent | **selected-branch producer checked** | `hess_half_inv`, the quantitative inverse estimate, weighted Neumann lemma, `cm_deriv_inv`, and `cm_sol_strict` prove and retain the invertible center derivative and strict local solution on the actual selected branch. The old abstract `chartCmEqn` input is not duplicated as a branch-specific input. |
| `StrictDistInput` | `lbl416/417` | **CHECKED selected-branch producer** | `hess_inv_sixth` and `HasNormalBrFull.hess_pos` give the positive Hessian bound; `deriv2_comp_geo_on` / `strictConvex_geo` transport it along `minJoin`; `HasNormalBrFull.strict_dist` proves speed, endpoints, midpoint confinement, and active-target strict convexity with the `R + 6 * rad < rho / 2` ledger. |
| endpoint `hconn` | book convention | added 2026-07-05 | connectedness is genuinely needed by the Hopf–Rinow proper realization (disconnected ⇒ emetric `⊤`); the book's manifolds are connected by convention. |

Meta-finding: 2 of the 12 audited inputs were mis-stated (one unsatisfiable, one
over-strong).  Rule going forward: any new honest-input structure gets a
one-paragraph "why is this true, at which scale, and who discharges it" note in
its docstring BEFORE consumers are built against it.

## 5. Label conventions (disambiguation — read before touching plans)

- `lblNNN` = MSM135 LaTeX labels (chapter4.tex/chapter3.tex).  **Cross-document
  references use `lblNNN` + a math name**; brick letters are plan-file-local.
- `C4/` the DIRECTORY = Chapter 4 modules.  "C1–C4" the ITEMS = Step C items
  (`lbl429/430/434/436`).  Say "Step C item 4", never bare "C4", in prose.
- "B1" = Step B item 1 (`lbl397`, `StepB1ApproxIso`).  The item-3 bricks
  formerly labeled B1–B5 live only in `ConvexBalls.md` history; P4's "Brick A/B"
  are Ch3-lane-local.  When ambiguity is possible, cite the file.
- P1–P4 = the Ch3 3.10⇐3.9 pipeline phases.  F1–F13 = Ch4 engine track.
  §2/§3/§6/§4 = the book's section numbers (non-monotone on purpose).

## 6. Honest progress (updated 2026-07-24)

- **Conditional Thm 3.9 endpoint: 100% checked.**
  `MetricCompactBase.exists_b1_raw` is checked and fills the concrete
  `StepB1RawInput` record 5/5.  The selected B/C-to-B1 producer route is 100%.
  `MetricCompactnessInputs.metricCompactness` now composes
  `exists_b1_raw → compactness_of_b1 → MetricCompactnessConclusion.ofSeqSubseq`
  in `C4/MetricCompactnessEndpoint.lean`; focused verification and its exact
  targeted refresh are green, with no local `sorry` or `admit`.  The canonical
  sidecar path is also closed: `compactness_canon` proves the concrete
  whole-source constants, and `metricCanon` retains them through the nested
  subsequence.
  The separately named textbook B1 theorem is still unstated and therefore 0%;
  the old full textbook Step-C arbitrary recurrence is a distinct incomplete
  route and is not being counted as endpoint completion.
- **Historical B/C chronology (snapshots through 2026-07-16; superseded by the
  2026-07-17 capstone above):** Step A done;
  Step-B/B1 machinery ~95% (`lbl394` done; B0 partial; **B1 assembly `stepB1_glue` PROVED
  sorry-free/axiom-clean 2026-07-05** — `exists_diffeo_of_injOn` construction +
  `BookApproxIsoPartialData` forward/reverse transport via `PreApproxIsoDataOn.congr`;
  **2026-07-09 statement repair:** the false P-only `stepB1_approxIso` and its `sorry`
  were removed.  `StepB1RawInput` now exposes the C-track producer boundary, and
  `stepB1_of_raw` is the checked conditional assembly.  Producer of that package
  from the endpoint inputs: 0%; textbook B1 theorem: 0%.  **⭐ B1 ENDPOINT
  `stepB1_of_bounds` (ANY order `p`) DONE 2026-07-07
  (`C4/StepB1Producers.lean`, green/axiom-clean)**: the full `lbl397` conclusion at any
  `p` closes from honest chart-level inputs (local diffeo on `U` + `InjOn` + basepoint
  fix + forward/reverse `C⁰` `hc0` AND `C^p` covariant-derivative `hcov` bounds) via one
  `stepB1_glue` call fed by `preApproxIsoDataOn_of_bounds`.  `stepB1_zero`/
  `preApproxIsoDataOn_zero`/`bookApproxIsoData_zero` are the `p = 0` wrappers (vacuous
  `hcov`).  The `hcov` inputs are produced by `C4/PullbackField.lean`'s pullback-invariance
  machinery (`covNormWith_pd_zone` + `iterCov_metric_zero`); the endpoint consumes them.  The entire `C⁰`
  approximate-isometry lane (rounds 16–29) is now honest-input-to-endpoint:
  chart-perturbation `bilinPerturb`/`quadPerturbNeumann` → tensor-norm bridge
  `normSq0S_ortho`/`sqrtNormSq_le_of_comp`/`exists_gON(_bd)` → center-derivative
  `mfderivNormalCenter` → single-point `pullbackErrComp`/`pullbackErrNorm` → carriers
  `preApproxIsoDataOn_of_bounds`/`bookApproxIsoData_of_bounds` → endpoint
  `stepB1_of_bounds` (ANY `p`; `_zero` wrappers are the `p=0` case).  Gap to a fully
  UNCONDITIONAL `lbl397` = producing the endpoint's honest input bounds: the uniform-`hc0`
  compactness + the `hcov` covariant-derivative bounds (the latter's engine — pullback
  invariance `covNormWith_pd_zone`, `iterCov_metric_zero` — is BUILT in `C4/PullbackField.lean`;
  NOT a pinned frontier, contrary to an earlier retracted note) + the C-track input production.
  **2026-07-09 radial-separation closure:** `mfderiv_exp_radial` + `radialEnorm_normal` close the
  former velocity-`hderiv` API gap, and `normLowerOfSepExp` now derives the coordinate norm lower
  bound directly from named-exp-ball containment and Riemannian separation.  This improves the
  producer machinery but does not change theorem completion: the `StepB1RawInput` producer and
  textbook B1 theorem remain 0%; Step-B/B1 machinery is about 95%.
  **2026-07-13 minimizing-branch closure:** Gates 1--6 are now focused-green:
  the selected inverse is minimizing, `halfSq` agrees with intrinsic squared
  distance on its cage, the generic gradient identity is proved in the
  comparison layer, and `centerReadoutB_min` derives the selected-branch center
  equation without endpoint radius assumptions.  The optimal
  `gpCoerciveConst` comparison, H6 origin bound, `gpRatio` floor,
  `normalMinScale`, and live-cage consumer close Gate 6.  `MetricCompactBase`
  then chooses one large `D` before instantiating packing and proves the old
  nonlinear Step-A cap.  This raises machinery modestly; the concrete
  `StepB1RawInput` producer and textbook B1 theorem remain 0%.
  **2026-07-13 post-packing `g_p` quantifiers:** `Item3GpScaleAt` and
  `Item3GpScaleTail` replace the over-strong all-index consumer boundary.
  `NormalRadiusProfile.gpScaleTail` proves the finite common tail from the
  `c = 8` window budget, and all Step-C atom/package/join consumers now use the
  weaker API. `Item3RadiusAt` / `Item3RadiusTail` are also checked: the book
  factor, injectivity/`expMapC2Radius` tail, one-shot divisor, fixed-`D` bundle,
  and combined tail producer are all in-tree.  The canonical
  `SigmaScaleField` refinement and its `r₁` bound are now produced as well;
  its later selected-scale convexity consumer is checked below.
  **2026-07-13 physical finite-hat closure:** the one-shot divisor accepts the
  extra minimizing-scale budget, `physScale_of_extra` gives the common physical
  inequality, and `exists_slot_min` uses the same `aMin` at every slotwise
  `rInf + 1` cage.  `exists_rad_cage` joins uniform active-radius decay to the
  half-margin, while `HasNormalBrFull.exists_cm_eqn` and `exists_hat_cm_eqn`
  handle actual points and dead slots and produce the selected-branch center
  equation.  `StepCHatReadout.exists_hat_cm_tail` then joins the sequence and
  pair-index tails and builds the actual filled `CenterInput`, with
  `StrictDistInput` left as the honest independent continuation.  This is
  machinery; `StepB1RawInput` remains 0% produced.
  **2026-07-13 source-local/global capstone closure:**
  `existsAtomWeightH6_of_innerCover`, `exists_live_source_cover`, and
  `exists_supp_pts_fin` produce one master subsequence carrying chart-local
  normalized weights and old-`L` sparse interaction points.  The support
  readout now consumes only nonzero limit-weight slots.
  `StepCSupportCapstone.exists_supp_cm_fin` chooses the minimizing scale before
  the one-shot divisor, then uses separate finite maxima over target and source
  slots. `exists_cm_on_source` gives the global-ball existential-source
  corollary. This conditional architecture is 100%; the concrete
  `StrictDistInput` comparison producer and `StepB1RawInput` remain open.
  **2026-07-14 Hessian/Neumann and strict-distance closure:** the
  intrinsic Hopf--Rinow `minimizingVec`/`minJoin` API is checked, and
  `IsNormalDiag.hess_half_inv` closes the branch-native `lbl412` identity.
  `cm_deriv_inv` uses the weighted inverse-velocity derivative and Neumann
  estimate to prove center-derivative invertibility; `cm_sol_strict` and
  `HasHatCmStrict` retain the strict local solution through the support-local
  and global finite-cover capstones. `hess_inv_sixth`,
  `HasNormalBrFull.hess_pos`, and the generic along-geodesic Hessian API prove
  the positive lower bound and `StrictConvexOn`; `HasNormalBrFull.strict_dist`
  closes speed, endpoints, midpoint confinement, and the active-target field.
  `exists_hat_cm_min` and the canonical support/global capstones now use the
  fixed intrinsic `minJoin` without a downstream `StrictDistInput` premise.
  Selected-branch Hessian/Neumann/strict-distance machinery is 100%; the
  concrete `StepB1RawInput`, textbook B1, and all endpoints remain 0%.
  **2026-07-14 retained-data and compact-core closure:** `HasSuppConvData`
  keeps source-domain openness, all-stage cover geometry, chartwise
  `HasAtomWeightLim`, and both transition limits on the capstone's one master
  subsequence. `HasCompactCover` then gives compact cores inside the frozen
  source patches which still cover the closed source ball. Both producer and
  capstone are focused-green, and the producer module refresh passed. The next
  frontier is architectural/analytic: define the single stage-weighted
  cross-manifold comparison map without gluing limit weights, upgrade the
  frozen-stage tail to raw B1's all-pairs quantifiers, and prove global
  injectivity plus arbitrary-order two-sided metric bounds. The concrete
  `StepB1RawInput`, textbook B1, and all endpoints remain 0%.
  **Later 2026-07-09:** `seqCenter_zero` / `seqCenter_edist_ge` and
  `seqChartNorm_ge` connect the actual ordered-net centers to that coordinate
  lower bound.  The former POU representation mismatch is now resolved:
  `centerAverage.WeightDataOn`, `normWeights_data` / `bumpWeights_data`,
  `NetLimitData.unifHatCageData`, and `stepCJoinDataFixed` give a checked
  explicit-weight route through the current radius-`4 * lamInf` hat endpoint,
  while the bundled POU entrypoints remain available.  The intrinsic quadratic
  atoms, strict-inner-one and hat-support facts, eventual `WeightDataOn`,
  canonical basepoint delta weights, live/dead slot stabilization, and full
  `C^infty` atom/normalized-weight convergence are now checked in
  `StepCAtoms.lean` / `StepCAtomConv.lean`.  Origin metrics are extracted only
  on the finite `LiveSlot` subtype.  `StepCAtomJoin.existsLiveJoint` implements
  the fixed-source common refinement with eventual live geometry, a common
  finite tail, and one Pi-valued forward-transition extraction; it does not
  consume irrelevant reverse/cocycle data.  The shared
  `Regularity/Derivation.lean` wall was repaired by the checked
  `modelAt_mcovRS` projection, and the entire join chain now verifies.
  `StepCAtomPackage.existsAtomWeightLim` packages the common-subsequence atom
  and normalized-weight limits; its implementation is checked.  The literal
  MSM135 radius-`5 * lamInf` support instantiation remains distinct.
  **(b) `lbl403` CLOSED 2026-07-07 (both halves, sorry-free/axiom-clean)**:
  manifold forward IFT `Geometry/Coordinates/LocalDiffeoIFT.lean` incl. the **`n = ∞`
  version** (`contMDiffOn_isLocalDiffeomorphOn_infty`, inverse-uniqueness upgrade of the
  order-1 diffeo) + Neumann `isInvertible_of_norm_id_sub_lt` + antilipschitz injectivity
  (`injOn_of_fderiv_near_id`) + chart-transfer `injOn_of_writtenInExtChart`; producers in
  `stepB1_glue`'s exact shape: `hlocOn_of_chartNeumann_infty` and the combined
  `hlocHinj_of_chartNeumann` (`(hloc, hinj)` pair from chart-Neumann data).  ALSO the
  `lbl404` C⁰/C¹ **diagonal engines** banked (`norm_pair_sub_self_le`,
  `fderiv_pair_sub_id_le`: diagonal identity + targets `C¹`-close ⟹ `dG ≈ id` — what the
  Neumann producers consume).  **`lbl404` ABSTRACT LAYER 100% 2026-07-07
  (`averagedCInf_id`, StepB1Producers): the "MISSING Faà-di-Bruno brick" line was STALE —
  `MapCInfConvOnCompacts.comp` is delivered, and the convergence route (comp +
  `mapCInfConv_prodMk`/`_pi`/`_const` + `congr` + the diagonal identities
  `centerOfMass_diag`/`chartCm_diag`/`diagEventuallyEqId`) needs NO quantitative
  derivative-difference bounds.**  Also `centerOfMass_delta` (δ-weights pin the center —
  the (d)-basepoint cm-core).  POU convergence and the basepoint `δ_{α0}` producer are
  now present.  The live-slot origin-metric/transition refinements and
  atom/weight limits are joined and packaged.  Remaining `lbl404`/B1 work =
  INSTANTIATION plus the genuine analytic producers: (i) targets per-slot
  convergence (instantiate `comp_cInf_id_on` on the concrete
  transitions; C⁰ base = `stepCJoin`); (ii) fixed-trivialization readout
  containment for the checked quantitative branch and its concrete finite-hat
  instantiation.
  `StepCCmDomain.lean` records the actual
  center on the admissible simplex and the separate `cmExt_contDiffOn` analytic interface;
  sparse/delta weights admit no ambient open `CenterInput` neighborhood.  The
  pinned local branch and ambient gluing/agreement are now checked via
  `existsPinnedLocal`, `existsRootExtension`, and `existsCmExtension`; the
  generic conditional center-root theorem is checked as `centerReadout_zero`.
  Its finite-hat instantiation is not yet complete: it still needs
  moving and reverse normal-source/smallness and fixed-chart containment.
  Pointwise producers are now checked: `exists_halfSqDist_md` supplies
  fixed-target differentiability, while `expDiffeoRadius` and
  `diagInv_eq_normal_lt` supply intrinsic/realized-exp identification below a
  named radius.  Their finite-hat hypotheses have not yet been instantiated.
  `DiagExpDerivative.exists_diagInvDom_inf` and
  `StepCSmoothness.exists_readoutDom_inf` now expose one fixed open
  inverse-exp/readout domain carrying all orders, built from Route A's checked
  joint forward producer and the existing `diagExpInv` branch.
  `exists_readoutEBall` extracts a finite positive radius per fixed base, while
  `centerPairs_lt_le` proves the local cage ledger `4 * lambda + 2 * r < δ` is
  sufficient for all readout pairs.  The missing scale is not local
  containment and relative-radius profiles are now checked:
  `MetricCompactnessInputs.normalRadius` provides `floor_le_radius` / `floor_le_exp`,
  while `NormalPhaseSym` constructs a common confined bilateral phase family and
  its `ApproximatesLinearOn` estimate.  The arbitrary-velocity naturality chain
  (`covAlong_natCrossAt`, `geodesicOn_mapLocal`, `normalGeo_map`) and interval
  endpoint uniqueness (`geo_end_eq_intr`) are now checked.  Consequently
  `NormalPhaseEndpoint.exists_normal_diag` packages one quantitative model branch,
  its explicit positive target ball and radius formula, and the exact commutative
  square with intrinsic `diagExp`.  `diagExpInv_diagExp` and `normal_inv_eq`
  prove compatibility with the existing `diagExpInv` on every verified overlap.
  The qualitative-germ containment route has been rejected because the private
  `diagExpIFT` choices carry no uniform quantitative source.  The selected
  explicit-branch route is now checked through `DiagInvBranch`,
  `DiagInvReadout`, `stdBranch`, the branch-parametric center consumers,
  `normalDiagAtFull`, and `IsNormalDiag.toBranch`.  The checked
  `IsNormalDiag.full_transport` gives the exact transported source and target
  equalities plus the inverse formula on the whole model target.
  `exists_phase_scale` and `normalBrAccept` provide global positive `aq`, `aδ`,
  and `aρ`, choose `q` and `δ` before the sequence index and center, retain the
  common `aρ * mu R` consumer domain, and expose the entire quantitative `δ`
  target ball and inverse formula.  `normalBrScale` is the compatibility
  projection used by existing consumers.  `normalMinScale` keeps the full
  branch/fence/transport data while shrinking to the H6-derived intrinsic
  radius, and `NormalBranchCage.exists_live_min` checks it on the eventual live
  centers. The minimizing route no longer needs the qualitative
  `expMapIntrinsic = expMap` radius. The post-packing `g_p` finite-slot ledger
  is checked by `gpScaleTail`, and the exp-diffeomorphism radius tail is checked
  by `radiusScaleTail`.  `sigmaCenterTail`/`exists_sigmaField` close the
  canonical sigma family, and `exists_rad_cage`/`exists_hat_cm_eqn` close the
  physical finite-hat readout.  The remaining scale surface is full geodesic
  convexity; reverse-chart/Hessian-Neumann assembly remains independent.
  The quantitative variant awaits the honest all-order lbl430 bounds; the
  `StepB1RawInput` producer must thread `stepCJoin`'s honest inputs.  B2–B6 open); Step C ~3/4
  (C1/C3/C4-shape done conditionally; C2
  regularity at `C^n` for every finite `n` DONE 2026-07-05 — `lbl430`(ii),
  `centerOfMass_contDiffAt`; C2 quantitative `|∇^j cm| ≤ C̃_j` bounds half
  (`lbl430`(i), `C4/StepCDerivBounds.lean`) — **base case + honest inputs DONE
  2026-07-05, axiom-clean**: `implicitDeriv_one_le` (abstract order-1 IFT bound
  `‖Df‖ ≤ Λ·B`, sorry-free), `CmHessianBoundInput` (`‖L⁻¹‖ ≤ Λ`, honest lbl413),
  `CmGDerivBound` (`‖∇^j G‖ ≤ B_j`, honest S6/lbl418 reduction), `cmChartFDerivLe`
  (`j=1`: `‖∇(chart∘cm)‖ ≤ Λ·B₁`, sorry-free); **2026-07-06 the Route-A minimal missing
  Mathlib bridge PROVED sorry-free/axiom-clean — `norm_iteratedFDeriv_ringInverse_le`
  (`‖∇^i (Ring.inverse) x‖ ≤ i!·‖x⁻¹‖^{i+1}`), the quantitative inverse-derivative
  Neumann bound**; **2026-07-06 ingredient (a) — the neighbourhood implicit-derivative formula —
  PROVED sorry-free/axiom-clean: `implicitFDeriv_eq` (pointwise) + `implicitFDeriv_eventuallyEq`
  (`∇f =ᶠ[𝓝 params₀] fun p => −(Ring.inverse (∂_zG(f p,p))).comp (∂_pG(f p,p))`), abstract, from
  eventual differentiability + `G(f,·)=0` + eventual z-block invertibility**; **2026-07-07 (b)
  j=2 LANDED sorry-free/axiom-clean: `graphBlockDeriv` (block-family derivative bound
  `‖∇(∂G∘graph)‖ ≤ ‖∇²G‖·(‖∇f‖+1)`), `implicitDeriv_two_le` (abstract `‖∇²f‖ ≤ Λ²a₂b₁ + Λb₂`),
  `CmHessianNbhdInput` (nbhd Hessian input bound to the center family, audit docstring), and the
  checked `cmChartDerivLe2` fully wires j≤2 (`C²` regularity → eventual differentiability,
  `graphBlockDeriv` at `inl`/`inr` from `B 2`, `C̃₂ = Λ'²a₂B₁ + Λ'a₂`, `a₂ = B₂(ΛB₁+1)`)**.
  **2026-07-09 statement repair:** the former all-order `cmChartDerivLe` was removed because C²
  regularity and constraints on only `Ctil 0/1/2` cannot imply j≥3 bounds.  The honest all-order
  theorem remains unstated/0% and needs order-p regularity plus a recursive majorant.  **2026-07-07 (c) analytic
  bricks ALSO landed green/axiom-clean** (`multilinear_prod_opNorm_le`, `norm_iteratedFDeriv_id_le`/
  `_graph_le`, `norm_iteratedFDeriv_invComp_le` (Faà-di-Bruno for `inverse∘A` on the unit set),
  `norm_iteratedFDeriv_graphComp_le` (Faà-di-Bruno through the graph)); remaining = c4/c5
  (bilinear collection at `compL` + recursive constants + the strong induction — scoped
  in StepCDerivBounds.md); Step D consumer machinery 100%
  (**D3 COMPLETE 2026-07-07 — `lbl408` all of D3a–D3e green, axiom-clean, zero warnings**:
  `Geometry/Topology/DirectLimitManifold.lean` = `ChartedSpace H Lim` (D3a) + `IsManifold I ∞ Lim`
  (D3b, `lbl409` transition crux) + σ-compact/T2/`T2Space (TangentBundle I Lim)` (D3c, via NEW
  `Geometry/Topology/FiberBundleT2.lean` general `FiberBundle.t2Space_totalSpace`) + **D3d metric
  transport `SmoothSeqSystem.limitMetric`**: per-factor metrics + isometry cocycle (`MetricCocycle`,
  D2c's shape) ⟹ `g∞` on `Lim` with `limitMetric_pullback : (incl k)^* g∞ = g k` — fiber form =
  pullback along the smooth local inverse `invFun (incl k)` (no derivative inverses), smoothness via
  the `cotangentCov_clmSection_smooth_aux` test-section engine + `tangentMapWithin`; D3e endpoint =
  `C4/StepDLimit.lean` `limitPointedCoc` (metrics+cocycle in → `PointedRiemannianManifold` out);
  no Step A/B/C imports.  **Plus 2026-07-07 later session: D4a DONE (`limitCGMaps` =
  `PointedRiemannianCGMaps` package of the `(incl k)⁻¹` comparison maps, + `rangeExhausts`,
  `factorSeq`, `inclPartialDiffeo`, limit connectedness `instConnectedSpaceLim`) and the D5
  distance cornerstones DONE (`enorm_mfd_incl` pointwise isometry, `pathELength_incl`,
  `edist_incl_le` 1-Lipschitz edist)**.
  **2026-07-07 (4th session) D1a + D1b machinery** (report as MACHINERY, not endpoint completion):
  D1a-(i) `exists_pullbackField`, D1a-(ii) `covNormWith_pd_zone` (zone-local partial-pullback
  cov-tower-norm naturality), D1a-(iii) `partialData_comp` (book lbl371 asymmetric form) +
  `PartialDiffeomorph.trans` — ALL PROVED SORRY-FREE, axiom-clean (consume F5/B1 which stay
  sorry-backed per the gate policy), in `C4/PullbackField.lean`; supporting
  `restrictOpen0S`/`tangentCoordChange_opens`/`tensor0SModelAt_opens` promoted to canonical
  `Tensor/RSTensor/Coordinates/OpensRestrict.lean` (0 sorry).  D1b `C4/StepDDirected.lean`:
  `chainComp`/`chainComp'` (two bracketings, equality-parameter right fold), `chainComp_coe_head`
  + `chainComp'_snoc`, `geomTailBudget`, `exists_strictMono_ge`, exact-zero separated base
  `reflSepData`, and the separated scalar ledger (`sepTail`, `sepBeta`, `sepFeed_le_beta`,
  `sepNextC0_le`, `sepNextCov_le`) are checked.  **2026-07-09: the conditional consumer
  `directed_of_b1` is CLOSED** in `StepDDirected.lean`: the active `hacc` carries separated
  `c0/cov` ledgers, uses peel-last `compSepFwd` and peel-first `compSepRev`, transports the
  right-fold inverse germ back to the left fold, and focused-checks with no local `sorry`
  warning.  **2026-07-09 later: the separated composition organs `compSepFwd`/`compSepRev`
  are now proved in `PullbackField.lean`**.  **2026-07-09 F4/F5 CLOSED:**
  `claim1MulConst` / `lemma45_F3_bound` expose data-independent scaled constants,
  `RicBoundGoodFrame.metricComp_mul` absorbs the good-frame and metric-swap loss,
  and both `lemma45_corII` and `lemma45_corII_unif` are proved.  F5,
   `PullbackField`, and `StepDDirected` verify downstream.  The former false B1
   dependency is now an explicit `StepB1RawInput` argument.  **2026-07-09 D1-to-D2
   REALIZATION LANDED:** `SeqSystem.ofSucc`, `SmoothSeqSystem.ofSucc`, the range-scoped
   open-ball restriction API, and `StepDLimitMetrics.directedBallSystem` turn the eventual
   D1 maps into a tail-shifted smooth open-ball system.  The former `lbl404` gate is also
   green in `MapConvergenceComp.lean`.  D2's actual ball pullback metric, ambient-inner
   readout, restriction covariant-norm bridge, positive-order bounds, and `C0` lower/upper
   plus order-zero bounds are checked locally.  **2026-07-09 D2 PREFIX-TAIL GEOMETRY
   LANDED:** target-normalized chain splitting, nested/composite pullback equality,
   prefix image containment, and exact positive-order bound transport are focused green.
   `metricComp_iter_refs` converts bounds measured against an order-dependent prefix reference
   into uniform chart-component derivative bounds.  **D2a COMPLETE 2026-07-09:**
   `engine_input_refs` now propagates through `metricPreconv_refs` and `metricCInf_refs`;
   `chainPullback_bdd` proves the concrete fixed-stage pullback sequence's bounds, and
   `exists_chain_limit`/`exists_chain_data` produce its stagewise C-infinity limits from the
   eventual D1 package.  The live D2 frontier is the common diagonal, `lbl407`, and the cocycle.
  **HONEST SEPARATION (per CLAUDE.md rule):** conditional D1b consumer body = **100% checked**;
  producing `StepB1RawInput` and proving the textbook D1b theorem remain **0%**.
  The conditional Step-D theorem `compactness_of_b1` is **100% proved** from
  that package, and Step-D consumer machinery is **100%**: `repoint` /
  `unrepoint` / `ofSubseq` close the original-sequence convergence transport,
  while `alignedProper` and `compactness_of_b1` complete D6 field assembly.
  This was the 2026-07-09 Step-D snapshot.  Its then-open endpoint wiring and
  concrete B/C producer were discharged on 2026-07-17; see the capstone above.
  F-track engines are **100%**: F4/F5/F6 are closed, and the book-facing F2
  producers `speed_le_of_c0` / `data_image_ball` now live in
  `C4/Distances.lean` and are consumed by `StepDDirected.lean`.  This counts the
   checked conditional engines. The separately audited [H6] localized
   `IsometryDerivBoundsOn` producer is **100% proved**; its fixed-source B/C
   consumer, finite source-slot diagonal, and endpoint S6 removal are **100%
   migrated**.  Finite positive interacting-pair extraction is checked, as are
   stable-disjoint zero limits and the active six-lambda target-image theorem.
   The source-local decoded convergence, point-only totalization, finite source
   cover, support readout, two finite maxima, and global-ball existential-source
   corollary are now checked in `StepCProducers` and
   `StepCSupportCapstone`.  The selected-branch Hessian/Neumann and strict-IFT
   chain is also retained through that capstone, and the `lbl413` to
   `StrictDistInput` comparison is checked.  Generic map convergence now lives
   in `Analysis/Calculus`, and the proof-independent metric spray plus
   `normalGeodesicSpray_conv` are checked.  The remaining B/C analytic frontier
   starts with the proof of `MapCInfConvOnCompacts.ode_solutionAt`, whose exact
   low-level statement is typechecked but whose all-order stability proof is
   0%.  Forward normal phase, compact moving roots, selected inverse
   convergence, and `invVelSum` roots follow; H6, chart compatibility,
   support filling, and Neumann are not frontiers.
   This historical snapshot estimated Ch4 machinery at ≈87%; the current
   rounded estimate is ≈95%.  The conditional endpoint is now 100%, while the
   separately named textbook B1 theorem remains 0%.
- Unconditional Thm 3.9: 0%, intentionally out of scope (external citations).
- Ch3: Lemma 3.11 is done under its cited `hShi` hypothesis.  The canonical
  conditional assembly `solutionComp_cond` → `compactnessSol_cond` is checked from
  conditional Theorem 3.9 plus concrete `FlowUpgradeData`.  In the P4 producer
  lane, `gSeqExt_ricci`, `gSeqExt_pde`, `ConvOut.gInf_pde`,
  `gSeqExt_scalar`, and `ConvOut.scalar_conv` are checked, and
  `flowLimit_of_reg` consumes the PDE and scalar passages internally.
  `flowLimit_of_reg` remains compatibility-only: its two window containments
  collapse the carrier, regular set, and fixed closed window.  The exact
  open-interval target `compactnessSol` is now stated, and the canonical nested
  compact-window exhaustion is checked.  `exists_openConv_raw` now produces
  one subsequence and one compatible limit family on all windows from the raw
  fixed-window hypotheses. `ConvOut.gramSmooth` now proves fixed-window joint
  chart-Gram `C∞`, and `OpenConvOut.smoothMetric_of_conv` checks the complete
  window-to-open-interval regularity assembly.  `OpenConvOut.isSolution`,
  `flowUpgrade_of_open`, and `open_upgrade_of_raw` now check the remaining
  consumer assembly, including completeness of every time slice of the
  constructed limit.  Uniform production of the raw hypotheses remains, and
  the canonical time-zero CP witness from the concrete Step-D construction
  must be retained because the abstract convergence package leaves its
  reference metric unpinned. The
  Hamilton nonregular-endpoint route remains a separate stronger consumer.
  Dedicated P4 consumer/assembly machinery is about 98%; unconditional
  Theorem 3.10 remains 0%.
  **2026-07-09 noncollapse repair:**
  the canonical Perelman layer
  now defines actual time-slice metric balls, Riemannian volume, parabolic
  curvature control, and model-dimension kappa lower bounds.  Hamilton's
  `Ham3Noncollapse` now ranges over genuine `paraSolution` rescalings; the fake
  `Ham3BallPair`/numeric-volume path was removed.  The checked data/realization
  machinery includes `ham3_rm_control`, the original-flow theorem
  `no_local_open`, and the rescaled Hamilton consumer `ham3_noncollapse`.
  The latter two theorems and their dedicated noncollapsing machinery are
  100%; the separate Cheeger-Gromov-Taylor `flowInj_of_vol` producer remains
  theorem-level 0%.
  The W-entropy producer lane has now checked conjugate-heat total-mass
  conservation, time reversal, the interval-local classical-solution
  interface, conditional nonnegativity, a time-operator lift, the abstract
  two-scale nonautonomous fixed-point engine, and local moving-volume first
  variation.  The Galerkin route now proves the moving-metric classical
  endpoint `heatpot_of_gallim`; `heatpot_exists` then removes the conditional
  Galerkin input for every smooth initial tensor, and `conj_heat_exists`
  produces `IsConjHeatOn` with the prescribed terminal trace.  These theorems
  and their dedicated classical existence machinery are 100%.  Its
  genuine frozen-scale
  operator inputs are checked: `lapDiffA20_short` gives the support-independent
  `A2 : H2(gT) -> H0(gT)` moving-Laplacian difference, `lapDiffA20_graph` and
  `lapDiffA20_test` give its selector-free closed-core realization, and
  `conjA1_short` / `scalarPotH0_test` handle the scalar-curvature potential
  `A1 : H1(gT) -> H0(gT)`.  `Entropy/ConjStrong.lean` proves the combined
  contraction package, `conj_strong_exists`, and the a.e. scalar weak equation
  `conj_weak_ae`.  The intrinsic all-order Galerkin chain `scalar_gal_bound` →
  `scalar_gal_subseq` → `galLim_tendsto` → `scalar_gal_limit` is checked.  The
  last theorem packages a genuine `MaxRegSolutionSpace` / `timeH1` solution
  with exact initial trace and the explicit represented `H² → H⁰` path.  The
  all-scale follow-up proves `galLimVel_lift`, `galLimExt_deriv`, and the
  canonical strong ODE `galLimExt_ode` on one order-independent positive slab.
  `ParametricAppHsTime`, `ScalarPotentialTime`, and `ScalarNonautTime` now
  give the fully applied dynamic completed-action regularity required by the
  ODE induction. `galLimExt_smooth` is proved simultaneously at every natural
  Sobolev order on one common smaller interval.
  `Entropy/ConjGalerkinClassical.lean` now proves `galLim_jet_mass`: compact
  interior time intervals, a higher Sobolev path, and the closed-manifold
  counting tail give one summable majorant for every coefficient time jet.
  All nine rank-zero Galerkin consumers (six in `ConjGalerkinClassical` and
  three in `ConjGalerkinOn`) now use the checked `scalar_eigen_tail`; its axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  The
  deferred generic arbitrary-valence Weyl theorem is a separate frontier and
  is not on this Entropy/Perelman chain.  `galLim_slice_cc`, `galLim_pde`, and
  `heatpot_of_gallim` now complete scalar reconstruction, the pointwise PDE,
  and the genuine classical heat-potential package.  The separate
  `heatpot_of_maxreg` route remains theorem-level 0%.  The positive unit-mass
  input is now complete: `gallim_pos`, `heatpot_mass_deriv`,
  `heatpot_mass_eq`, and `gallim_unit_pos` give a strictly positive genuine
  reversed heat potential of moving mass one (or identify the empty-manifold
  case), without exporting the old global regularity assumptions.  The
  Perelman potential inverse is also checked: `density_potential` and
  `weighted_potential` recover the density and weighted measure exactly.
   These are dedicated entropy machinery, not endpoint theorems.  The potential
   evolution and moving-gradient producers are checked, and
   `w_rev_hasDerivAt`, `w_rev_square`, `w_rev_deriv_nonpos`, and
   `w_rev_antitone` now give the genuine raw variation, weighted-square
   identity, derivative sign, and interval antitonicity for the reversed-flow
   `conjCoeff` heat potential.  Their dedicated theorem layer is 100%.
   `wFunctional_base`, `square_pot_energy`, and `w_square_form` expose the
   exact scalar positive-amplitude normal form needed by later estimates.
   `sobolev_closed`, `sobolev_intrinsic`, and `sobolev_lpNorm` choose a single
   closed-manifold Sobolev constant and expose the intrinsic `L²` to `L⁶`
   estimate.  `withDensity_prob`, `int_log_le_moment`, and
   `entropy_le_moment` provide Jensen; `logSobolev_closed`, `log_prefactor`,
   `w_fixed_lower`, and `w_density_lower` close the actual fixed-metric W lower
   bound in amplitude and density normal forms.  Each of these producer
   theorems is 100%.  The selected quantitative cutoff/contradiction route now
   closes `no_local_open : NoLocalCollapsing S rho`, and the Hamilton consumer
   `ham3_noncollapse` is also checked.  Both endpoint theorems and their
   dedicated noncollapsing machinery are 100%, with axiom audits containing
   only `propext`, `Classical.choice`, and `Quot.sound`.  The
  former `nablaRSFun_eval_moving_raw` elaboration wall and the
  downstream Laplacian-bridge object refresh are both resolved.  The canonical constant-metric volume and
  distance laws are checked (`Analysis/Integration/Measure/Scaling.lean` and
  `Geometry/Metric/DistanceScaling.lean`).  `Perelman/ScaleTransfer.lean` now
  proves two-way transfer of the genuine ball, curvature, kappa, below-scale,
  and `NoLocalCollapsing` predicates.  Hamilton's `ham3_radius_event` and
  `ham3_noncollapse_of` complete the downstream implication from an
  original-flow `NoLocalCollapsing` producer to fixed-radius
  `Ham3Noncollapse`.  The original-flow producer is now `no_local_open`, so
  this scale-transfer sublane and `ham3_noncollapse` are both theorem-level
  100%.  `HamiltonPositiveRicci.lean` directly imports
  `ExtendedSolutionRegularity` rather than the unused `MaximalTime` umbrella
  and is focused/exact-green.  Independent axiom replay for both
  `no_local_open` and `ham3_noncollapse` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  The positive-space-form
  classification lane is closed: `ham3_space_box` and its
  `constPosQuotient` machinery have complete proofs.  The former
  universal-cover `fibre_countable` `sorry` is replaced by the refined
  countable polygonal-loop producer, without the invalid
  pairwise-intersection assumption.  The complete downstream exact replay
  passes, and the endpoint axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  `ham3_space_box` and its dedicated
  machinery are each trusted at 100%.  The two
  remaining sorries in the Hamilton file belong to the separate
  `ham3_flow_exists_normalized` and `ham3_cgh_limit` producers and are not
  dependencies of `ham3_noncollapse`; those unconditional endpoints remain
  theorem-level 0%.
  **2026-07-09 CGH/3.10 repair:** `Ham3CGHLimitData` now retains the real source,
  original-index composition, `SmoothCGHConverges` maps, source-to-original
  diffeomorphisms, and limit-slice completeness.  The forgetful adapter and
  arbitrary `HamCGHTopology.lift` wrapper were removed.  `LimitRoundAt` keeps
  the exact complete slice and Ricci lower bound used by the repaired
  `limit_to_orig` statement.  `PointedRiemannianManifold.compact_of_ricci` and
  `PointedCGHMaps.exists_source_univ` / `target_univ` / `globalDiffeomorph`
  provide the real compact-limit globalization route, and `limit_to_orig` is
  now checked with no `sorry` (**theorem 100%**).  Separately, the conditional route
  `MetricCompactnessInputs.metricCompactness -> FlowUpgradeData ->
  solutionComp_cond -> compactnessSol_cond` is checked and makes zero calls to
  the unconditional Theorem 3.9; the former exact-conclusion backend has been
  removed.  This conditional assembly machinery is 100%; unconditional Theorem 3.10 and
  `ham3_cgh_limit` remain 0% pending the common-window/source compactness producer.
  The Hamilton contract now makes that producer exact: `Ham3SourceRealizes`
  carries common-time inclusion, selected basepoints, and pullback equality to
  the actual rescaled metrics; `Ham3CompactInput` retains the raw curvature
  bound, window, kappa, and noncollapse; both black boxes carry the finite
  maximal-time interval.  Transfers are bound to the actual CGH witness rather
  than quantified over arbitrary limits.  This contract refactor is checked
  infrastructure, not completion of either producer.
  **2026-07-24 fixed-time pinching transfer:** `ham3_tf_bound0`,
  `ham3_scale_decay`, cross-pullback Ricci/trace-free naturality, intrinsic
  Ricci-norm convergence from the retained C2 jets, and closed/open
  `ConvOut`/`FlowLimitData` retention now assemble the focused-green theorem
  `HamiltonPositiveRicciAdapter.tf_decay0_of_cgh : LimitTfDecayAt L 0`.
  This source theorem and its dedicated fixed-time transfer machinery are
  focused-green and 100%; it uses neither a scalar strong maximum principle
  nor a new transfer assumption.  The broad exact target has exited, but the
  adapter artifact remains older than the latest source; formal build handback
  is pending, so it is not yet exact-current.
  `ham3_cgh_limit` remains theorem-level 0%, and whole-HCG machinery remains
  about 60%.
- **Hamilton E1 low-regularity short-time input:** `LowRegCoeff` and
  `exists_low_reg_coeff` now package two-sided active-chart ellipticity, Gram
  bounds through order three, a uniform absolute Ricci--DeTurck RHS bound, and
  RHS-value Lipschitz control against metric `2`-jet differences directly from
  the restart theorem's `Lambda`-equivalence and
  `MetricCovDerivOrderBoundOn` hypotheses.  This
  coefficient sublane is checked and axiom-clean.  The next missing producer
  is the three-dimensional mixed `H^3 -> H^1` tame estimate; the uniformly
  parabolic low-regularity solver, same-interval smoothing, and
  `ricci_flow_unif_existence` remain theorem-level 0%; see
  `../SHORTTIME_MERGE_PLAN.md`.
- **B/C support-local H6 integration (historical milestone; superseded by the
  checked selected-route capstone below):** the normalized limit-weight projection,
  actual-support compact cages, producer-owned finite source cover,
  support-local decoded composition/readout, old-`L` sparse interaction points,
  source finite maximum, and global-ball existential-source corollary are all
  focused-green. The approved conditional source-local/global capstone is 100%.
  H6 derivative production, pair extraction, outer cover wiring, and the
  selected-branch Hessian/Neumann strict-IFT path are no longer blockers.  The
  positive Hessian, along-geodesic strict convexity, and direct intrinsic-join
  `StrictDistInput` producer are now checked as well.  This advances
  infrastructure only: `StepB1RawInput`, textbook B1, and compactness endpoints
  remain 0%.
- **B/C global finite-stage map (updated 2026-07-16):** `stageTarget`,
  `HasUniqueStageCenter`, and `stageComparisonMap` define one chart-independent
  actual-weight comparison map, and zero-weight energy congruence identifies
  local filled center branches with its global minimizer.  The source producer
  now returns fixed compact nested cores whose strict inner images cover the
  source ball, and the producer/capstone chain retains them on the same master
  subsequence.  `StepCStageFill` now supplies the fixed two-bump safety filler,
  old-`InterSlot` finite totalization, actual refined configuration,
  arbitrary-reindexing `C^infinity` convergence, and exact raw-target readout
  at retained nonzero interacting slots.  The ODE/normal-phase/moving-root
  chain and all-pairs chart-jet theorem are now checked.  The actual maps are
  focused-green as local diffeomorphisms, preserve basepoints exactly, admit an
  independently constructed approximate return, and are globally injective on
  every retained smaller source ball by the uniform intrinsic-buffer argument.
  `StepCStageSeed` and `StepCStageDiagonal` choose the radius-independent seed
  and one strict master diagonal; every fixed integer radius persists on a
  tail.  `StepCStageMaster` now transports the same actual map to the direct
  master indices.  The target-first `MetricCompactBase.exists_b1_raw` proof
  opens the real `StepB1RawInput.comparison` field and fills local
  diffeomorphism, injectivity, and exact basepoint preservation for that map.
  `StepB1Inverse.inv_chart_conv` and `inv_chart_tail` now give compact-open
  smooth convergence, eventual smoothness, and one rectangular pair-index jet
  tail for the exact `Function.invFunOn` coordinate inverse.  The checked
  `StepB1MetricReverse.inv_cov_comp_tail` upgrades this to the complete
  exact-inverse component covariant-derivative tower on the moving target
  image; the reverse stage comparison map is still used only as an approximate
  return map.
  Its forward and exact-local-inverse `PreApproxIsoDataOn` fields now have
  complete source proof bodies.  The pullback coefficient bridge is checked
  through the buffered fixed-patch tail and its finite-source maximum
  `pb_local_tail`.  `MetricCovDerivConv.iter_comp_conv` and `iter_comp_zero`
  now prove, at every finite order, that compact-open smooth convergence of
  the base coefficient and Christoffel arrays propagates through the complete
  component covariant-derivative tower.  `MetricCovDerivMetric.metric_tower_conv`
  now also derives the real raised-Koszul/Christoffel convergence from two
  metric-coefficient families converging to the same coercive limit and sends
  every finite `(q-g)` component tower to zero.
  `HasStageJetData.cov_comp_tail` packages this as one rectangular all-pairs
  tail, uniform over the finite source cover, every order through a prescribed
  `p`, and every component.  The metric-only cross-model naturality theorems in
  `MetricCovDerivPullbackCross` are also checked for the complete metric tower,
  difference tower, squared tensor norm, and `metricDerivNorm`.
  `PDE.RicciFlow.iterCovComp_restrict` closes the recursive constant-frame
  restriction to an open subtype.  `stagePull_coeff` checks the actual
  finite-stage pullback coefficient formula; `metricError_eq_zero`,
  `t02Norm_metricDiff`, and `sqrt_norm_le_comp` close the order-zero,
  positive-order, and component-to-intrinsic carrier readouts.
  `PreApproxIsoDataOn.of_metric` is the checked collar-local constructor that
  packages those bounds without a global pullback premise.  The local-open
  Christoffel/component-to-norm bridge `local_norm_le` and the cross-model
  `quarter_norm_eq` readout are focused-green.  The source proofs of
  `fwd_norm_tail` and `inv_norm_tail`, the generic/stage-specific carrier
  assembly in `StepB1MetricCarrier`, and the complete target-first
  `MetricCompactBase.exists_b1_raw` body is checked with no explicit `sorry` or
  `admit`; the raw proof fills all five record fields and uses
  `cast_preapprox` once for the final master-index transport.  Focused checks
  and exact targeted refreshes are green through the intrinsic, carrier, raw,
  Step-D, and endpoint chain.  Thus the selected B/C-to-B1 producer route is
  100%, the concrete raw record is 5/5, and the conditional compactness
  endpoint is 100%.  The separately named textbook B1 theorem remains unstated
  and 0%.  Rounded machinery estimates are approximately 100% / 95% / 60% for
  the selected B/C producer route / Chapter 4 / whole HCG.
- **Perelman noncollapse cutoff closure (2026-07-23):** the fixed-metric W
  lower bounds, quantitative cutoff/contradiction, initial-time volume lower
  bound, and positive-time entropy route now assemble the checked theorem
  `no_local_open`.  All nine rank-zero spectral consumers use the axiom-clean
  `scalar_eigen_tail`; the generic arbitrary-valence Weyl frontier is not a
  dependency of this chain.  `no_local_open` and the downstream
  `ham3_noncollapse` are each theorem-level 100%, and their dedicated
  noncollapsing machinery is 100%.  Their axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`.  Whole-HCG machinery remains about 60%.
  The unconditional Hamilton main/compactness endpoint remains theorem-level
  0%; the separate `ham3_space_box` classification theorem is closed.  See
  `../Perelman/Noncollapsing.md`.
- **Whole HCG project — conservative MACHINERY estimate ≈ 60%** (this is
  infrastructure coverage, not completion of the unconditional Hamilton
  endpoint).  **Conditional Thm 3.9 is 100% checked.  Unconditional Thm 3.9,
  unconditional Thm 3.10, and `ham3_cgh_limit` remain 0%.**  The selected B/C
  producer and conditional Step-D/endpoint chain are closed; the separately
  named textbook B1 theorem remains unstated at 0%, and the historical full
  Step-C arbitrary recurrence remains incomplete.  The `g_p`,
  exp-diffeomorphism-radius, canonical sigma, pre-packing large-`D`, physical
  finite-hat, outer source-slot, `lbl412`, positive-Hessian/full-convexity, and
  Neumann ledgers are now checked.
  The metric/transition join, atom/weight package, pinned center gluing, generic
  conditional root producer, D5 metric exhaustion, and flat nested-open
  convergence are no longer on this list.

## 7. Real sorries in this tree (audited 2026-07-23)

`MetricCompactness.lean` (unconditional metric endpoint) ·
`HamiltonCompactness.lean` (`compactnessSol`, unconditional solution endpoint) ·
`NoncollapseInjectivity.lean` (`flowInj_of_vol`, the separately declared CGT
frontier) · `Evolution/BernsteinComplete.lean` (`estimate_complete`, legacy insufficient
complete-Bernstein interface).  The legacy `estimate_complete` statement
remains visible while its caller awaits the solution-produced cutoff; a green
wrapper does not discharge that mathematics.
`FlowLimitRegularity.lean` has no remaining proof `sorry`; in particular,
`ConvOut.gramSmooth` is checked.  Neither
`C4/MetricCompactnessInputs.lean` nor `C4/StepB1RawProducer.lean` is in the live
proof-`sorry` census: the conditional endpoint is implemented in
`C4/MetricCompactnessEndpoint.lean`, and `MetricCompactBase.exists_b1_raw` is
focused-green with all five fields checked.  The former ODE convergence
`sorry` has been discharged.

`C4/PullbackField.lean` has no
remaining proof `sorry`: the unconsumed ordinary `compDataFwd`/`compDataRev`
wrappers were removed, while the D1b separated `compSepFwd`/`compSepRev` organs
remain proved.  `C4/StepB1ApproxIso.lean` has no `sorry` after the
false P-only endpoint was replaced by `StepB1RawInput` plus `stepB1_of_raw`.
`C4/StepCDerivBounds.lean` also has no `sorry`: it now exposes only the checked order-two theorem
`cmChartDerivLe2`; the honest arbitrary-order theorem is not yet stated.
`C4/StepDDirected.lean` has no active local
proof `sorry` after the separated `hacc` replacement.  Other `sorry` grep hits in
`HCGCompactness/` may include docstring mentions; inspect before counting.  `Comparison/HopfRinow.lean` carries 4
dead sorries (3 unconsumed statements — see its header note); the C4 chain's
properness needs are served sorry-free by `HopfRinowProper.lean`.

The public `HCGCompactness.lean` umbrella imports the new modules.  The endpoint,
conditional-solution, and Hamilton modules are individually focused- and
targeted-green; a fresh umbrella check currently stops later in the independent
entropy chain at the missing
`Analysis/Spectral/Intrinsic/HeatSemigroup/GalerkinLimitUniformMass.olean`, so
no broad shared refresh was started from this lane.

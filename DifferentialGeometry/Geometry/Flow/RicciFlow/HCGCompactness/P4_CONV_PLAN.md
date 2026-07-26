# P4_CONV_PLAN — the `conv`/`L` engine for MSM135 Thm 3.10 ⇐ 3.9 (final assembly phase)

The approved post-assembly producer architecture is
[`P4_PRODUCER_RULING.md`](P4_PRODUCER_RULING.md).  It is authoritative for the
two independent lanes (complete-noncompact arbitrary-dimensional Shi analysis
and concrete Step-D provenance), the grow-only `hcovTail` migration, and their
final meeting point at `open_upgrade_of_raw`.  The provenance lane is now
closed; the analytic lane remains active.

Self-contained execution plan for Opus sessions. Planner (Fable) verifies each brick on
return (build + `#print axioms` + statement read). Approved architecture:
`C:\Users\liao9\.claude\plans\fluffy-coalescing-leaf.md` (Route 2, bump-extension), updated
2026-07-01 for the now-complete pullback layer.

## Standing rules

- ALL Lake via `scripts/lake-locked.ps1` (`claim -Files` → keep token → `check -Token` →
  `build +Module` → `release -Token`). NEVER bare `lake`. NEVER push/commit unless asked.
- Other sessions share this tree (C4/StepC files etc. are theirs — do not touch). A stale
  claim on `Evolution/ExtendViaUniqueness.lean` belongs to another session; ignore it.
- `lake env lean` SUCCESS is not trustworthy (cached false-green); verify closure with a
  targeted `build +Module` and axiom-check endpoints (`[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`).
- Honest partial results: precise `sorry` in a mathematically correct statement is acceptable
  mid-brick, NEVER in the final brick deliverable. No hypothesis-wrapper "adapters" that move
  the goal into new named assumptions.
- Record findings in same-name `.md` notes; update this plan's Status lines when a brick lands.

## Context (what this phase produces)

Endpoint: the `conv` field of `FlowLimitData` (`FlowLimitUpgrade.lean:100`) plus the limit
flow `L` — together the proved upgrade `MetricCompactnessConclusion (X.atZero) →
CompactnessConclusion X` (= the book's §lbl352, "compactness for solutions from compactness
for metrics"). Cited inputs (NOT proof obligations): Theorem 3.9 output `mc`, and the
moving-Shi bound `MovingShiBoundOn` (`RicBound.lean:141`) for the sequence flows.

Mathematical shape (book, chapter3.tex:815–857): the comparison maps Φ_k from `mc` identify
the flows with metrics `Φ_k^* g_k(t)` near any compact of `M_∞ = mc.limit.M`; Lemma 3.11
(done: `covOrderBound_of_soln`) + Arzelà–Ascoli (done: `windowGInf`/`winGInfOfSol`) give a
subsequence converging C^∞-window-uniformly to a limit family `g_∞(t)`; `g_∞` is the metric
of the limit flow `L`; Ricci-continuity closes "limit is a solution".

## Current status (2026-07-22)

The P4 analytic ruling has been corrected after a theorem-shape review.  The
solution curvature tower is produced directly as a costed `TowerHeatBoundOn`:
the old fixed-`card^2`, per-`j` `IteratedRmTowerOn.starBound` is not implied by
the concrete `StarSum2Cost` factorization.  The arbitrary-index successor and
solution capstone are now assembled in source as `resStarNext_spec` and
`rmResidual_cost`; the direct pointwise consumer is `towerHeatSol_raw`, and
`towerHeatSol_any` is only its positive-tail wrapper.  The HCG level cost and
explicit Shi envelope now use `rmTowerCost d k`.  The sorry-backed
`exists_rmTowerSol` has been removed rather than retained as a compatibility
theorem.  The complete ordered chain is now focused- and exact-green:
`resStarNext_spec`, `rmResidual_cost`, `towerHeatSol_raw`, `towerHeatSol_any`,
and the `MovingShiOpen` cost migration are all exact-current.

The level-zero flow equation is now checked and exact-current.
`rm04Base_of_solution_any` combines the canonical coordinate variation with
the static Hamilton identity and proves, in every finite orthonormal basis,
`partial_t Rm04 = roughLap Rm04 + hamiltonRmReact` directly from
`IsSolutionOn`.  It uses no dimension-three identity, tail regularity package,
or extra solution assumption.  The costed level-zero join is exact-current as
`e0Residual` (with `rmResidual_zero` retained as the existential compatibility
wrapper): it identifies the canonical reaction with `e0Field`, chooses one
global witness before the point and basis, and records the exact
`rmResidualCost` base value.

The bookkeeping part is also checked.  `rmResidualCost`,
`rmTowerCost`, their nonnegativity API, `TowerHeatBoundOn.mono_cost`,
`e0Field_cost_any`, and `e0Field_comp_any` are focused-green, while
`rmBaseReact` records the eight-term level-zero reaction, and
`e0Residual` closes their solution-facing base assembly.  The supporting
`hamiltonRm04Id` and `rm04Var_of_sol` theorems are exact-current, and their
fixed-basis solution combination is `rm04Base_of_solution_any`.  The historical
[`P4_BASE_CONSULT.md`](P4_BASE_CONSULT.md) is now resolved.  The
arbitrary-index recursive residual and direct tower are sorry-free,
focused-green, and exact-current.  `rmResidual_cost`, `towerHeatSol_raw`, and
`towerHeatSol_any` are theorem-level 100% checked, and their dedicated
direct-tower machinery is 100%.

The complete-noncompact Bernstein architecture is now Route B-prime.  Anchor
completeness, metric equivalence, and a Ricci lower bound do not by themselves
produce a globally smooth parabolic exhaustion.  Instead, the selected route
uses point-centered Calabi lower supports for the cutoff and asks for a smooth
upper support only at a selected negative Bernstein minimizer.  The actual
curvature-tower Kato estimate remains solution-generated, not a new HCG
assumption.  The existing smooth fixed-order theorem
`BernsteinTower.estimate_cutoff_at` stays exact-current, while the barrier
  sibling `BernsteinTower.estimate_barrier_at` is now focused- and
  exact-green.

The fixed-window PDE and scalar passages are checked.  `ConvFieldPDE.lean`
provides `gSeqExt_ricci`, `gSeqExt_pde`, and `ConvOut.gInf_pde`; the last theorem
passes the genuine source-flow equation through the bump extension and then
through the Arzelà–Ascoli limit.  The scalar path is likewise concrete:
`gSeqExt_scalar` proves bump-local scalar-curvature equality and
`ConvOut.scalar_conv` combines that locality with `scalarConv_of_dnConv` to
produce the required pullback scalar convergence.  `flowLimit_of_reg` consumes
both the PDE and scalar producers internally.

The architecture-independent local-window selector is also checked:
`RealTimeInterval.exists_Icc_regular` places every `t ∈ X.D.regular` in the
interior of some closed `Icc a b ⊆ X.D.regular`.  This is exactly the local
topological input for upgrading a windowwise `HasDerivWithinAt` result to
`HasDerivAt`.  It does not construct a common `ConvOut`, a master subsequence,
or any convergence at nonregular carrier endpoints.

The book-facing target is now stated explicitly as `compactnessSol` in
`HamiltonCompactness.lean`, with
`X.D = RealTimeInterval.openInterval α b 0 h0`.  The canonical nested windows
`RealTimeInterval.openWindow α b 0 n` and their checked containment, nesting,
initial-time, point-cover, and union-exhaustion lemmas are available in
`TimeInterval.lean`.  Thus MSM135 Theorem 3.10 needs no new time-domain
predicate and no endpoint extension.

`flowLimit_of_reg` is nevertheless only a compatibility theorem.  Its retained
assumptions `Set.Icc β ψ ⊆ X.D.regular` and
`X.D.carrier ⊆ Set.Icc β ψ`, together with
`X.D.regular ⊆ X.D.carrier`, force all three sets to coincide.  This does not
model an open interval by itself.  The fixed-window mismatch is now closed at
the raw-producer layer.  `ConvFieldOpen.lean` fixes one bump family, reruns
`convOut` after every prescribed refinement, extracts one master subsequence,
and glues the windowwise limits by compact-open uniqueness.
`OpenConvOut.conv_Icc` reads the result on every compact subinterval of the
open domain.  The remaining producer work is to discharge the four raw
hypotheses on all canonical windows from the theorem-level sequence-flow data.
The independent joint-spacetime regularity bridge is now closed:
`ConvOut.gramSmooth` is proved from the existing fixed-window data `hwin + co`,
and `OpenConvOut.smoothMetric_of_conv` localizes and glues those windowwise
results into all four `MetricFamilySmoothOn` fields on the ambient open
interval.  Both are checked with no new exhaustion predicate, endpoint
assumption, lower-metric field, or stage-family stay hypothesis.  The
open-interval PDE, scalar, and regularity readouts are now wired through
`ConvFieldOpenEndgame.lean` and `ConvFieldOpenAssembly.lean`.  The checked
theorem `open_upgrade_of_raw` constructs one `FlowUpgradeData` from the four
raw window packages plus the time-zero CP witness, and proves completeness of
every time slice of that same limit flow.  The assembly consumes the canonical
`flowUpgrade_open_L` projection rather than unfolding the dependent record.

The remaining P4 work is producer-side and analytic: the theorem-level
curvature and completeness inputs must yield uniform open-window lower,
covariant, and time-Lipschitz estimates in the complete noncompact
arbitrary-dimensional setting.  The formerly independent provenance task is
closed.  The concrete Step-D sidecar retains the canonical time-zero
`MetricSourceData` and its constants-first bounds, while the abstract
`MetricCompactnessConclusion` remains intentionally unchanged.

The analytic boundary is now explicit in `MovingShiOpen.lean`.
`movingShi_complete` and `CurvBoundInput.movingShi_open` choose the common
curvature bound and the explicit `shiOpenConst` before the member index; they
do not uniformize memberwise existentials.
`movingShi_of_bound`, `movingShi_complete`, and
`CurvBoundInput.movingShi_open` are now focused- and exact-green.  The
chart-local curvature/tower/norm regularity chain was weakened honestly to the
complete-noncompact setting, and the anchor-norm statement mismatch was
repaired.  Their trusted lower work is now split visibly between one closed
producer and one genuine analytic frontier.  The arbitrary-dimensional costed
residual and direct tower (`rmResidual_cost`, `towerHeatSol_raw`, and
`towerHeatSol_any`) are focused- and exact-green.  The generic localized
consumer is also closed: `GfunCut_parabolic_le` and
`BernsteinTower.estimate_cutoff_at` are exact-current; the old
`estimate_of_cutoff` is its all-order compatibility wrapper.  The HCG
`complete_of_cutoff` adapter is also focused- and exact-green, retaining the
genuine tower through `m + 1`.

Route-neutral cutoff plumbing is now checked as well.  `CutoffProfile` supplies
a smooth one-dimensional plateau with the required derivative bounds;
`laplacian_comp`, `heatDrift_comp`, and `parabolic_comp` supply the spatial and
spacetime scalar chain rules; and `edistOf_le_of_quad` /
`le_edistOf_of_quad` turn pointwise metric comparison into distance comparison.
These results do not produce a cutoff.  A live route audit found that a
fixed-anchor smooth bump is circular without a genuinely controlled parabolic
exhaustion, while a distance cutoff requires a new Calabi/barrier consumer and
cut-locus/time-distance comparison stack.  A local-Shi detour does not avoid
that same analysis.  The architecture choice is recorded in
[`P4_CUTOFF_CONSULT.md`](P4_CUTOFF_CONSULT.md).

Accordingly, a solution-generated globally smooth `ShiCutoffData` is no longer
the mandatory blocker.  The Route B-prime maximum-principle and data boundaries
are checked: `strict_barrier_cpt_of_upperSupport`,
`ShiCutoffLowerSupportAt`, `ShiBarrierCutoffData`, and
`ShiCutoffData.toBarrierAt` are focused- and exact-current.  The basepoint-free
  completeness package, connectivity-free intrinsic-geodesic producer spine,
  point-pair Hopf--Rinow endpoint, and finite closed-eball compactness are also
  focused- and exact-current.  The first genuine geometric producer frontier is
  now the spatial part of the evolving-distance Calabi upper support.  Its
  fixed-path time variation is focused-green:
  `pathLength_timeDeriv_of_ricciFlow` proves the exact Ricci-flow derivative,
  and `pathLength_deriv_ge` gives `∂ₜ L ≥ -A L` from a quadratic Ricci bound.
  The pure model estimate `hypMeanCurv_le` and the full fixed-first
  radial-Hessian/Laplacian bridge through `branchLap_eq_mean` and
  `radialLap_eq_mean` are focused- and exact-green.  The comparison-layer
  `calabi_tail_of` and `exists_calabi_tail` are also exact-current, but the
  deeper half-length audit shows that this terminal branch is too short to
  produce the required `2(d-1)/r` pole, while `exists_radial_mean` is a
  small-launch raw/C2 theorem.  The next honest architecture frontier is an
  early minimizing-tail nonconjugacy/local-inverse producer plus a global
  intrinsic minimizing-tail comparison; see
  [`CALABI_BRANCH_CONSULT.md`](CALABI_BRANCH_CONSULT.md).
  `scaledDist_calabiUpperSupport_of_sol` and `shiBarrierCutoff_of_sol` remain
  theorem-level 0%.  The independent consumer-side sibling
  `BernsteinTower.estimate_barrier_at` is focused- and exact-green and sorry-free.
  Its corrected signature consumes a point-centered family
  `∀ O, Nonempty (ShiBarrierCutoffData G B.T O)` and proves the fixed-order
  estimate globally; a single fixed-center cutoff was insufficient for the
  strong-induction hypothesis at the arbitrary compact-support minimum.
  The private `MovingShiOpen.complete_of_barrier` adapter is focused-green and
  transports the same finite truncation and Kato prefix to that consumer.

The varying-source interface is also now explicit in `SourceCovLip.lean`.
`SrcCovLipData` records constants before `k`, and `srcCovLip_of_soln` is
focused- and exact-green.  Its positive-order strong induction consumes the
explicit fixed witnesses from `AkMFold`/`RicBoundClaims`,
`covOrderBound_stage_on`, and `ric_bound_field_on`; there is no compact
subcover, per-member witness, or new assumption.  The grow-only
`hcovTail` migration is now complete across the ten-module open-convergence
chain: `hchi` and the artificial whole-source bump-collar estimate are gone,
and the focused checks plus exact refreshes are green.  The concrete
`StepDCanonData` provenance sidecar, its subsequence transport, and
`compactness_canon` are now complete.  `HasCanonBounds` is proved by an
all-tail/compact-finite-head argument, and `StepDCanonP4.canon_cp`,
`canon_rel`, and `canon_init` are focused- and exact-green against the live
framed import chain.  The approved architecture therefore needs no further
provenance consult.

The downstream audit rules out globally replacing `carrier` by `regular` in
the canonical convergence API.  `SourceSpacetimeConvergenceData.toSpatial`
currently derives carrier-time spatial convergence from singleton windows, and
the Hamilton adapter uses `scalar_converges` at `t = 0`, which is a carrier but
not regular time in its backward closed window.  Therefore the existing
carrier-capable API remains as a stronger Hamilton compatibility interface.
The book theorem is the separate open-interval specialization, where carrier
and regular are definitionally the same.  Hamilton endpoint extension is a
different later producer and is not part of the MSM135 3.10 denominator.

`ConvFieldCanon.open_upgrade_canon` is also focused- and exact-green, so the
canonical provenance sidecar, varying-source bounds, and final open-field
consumer now meet in one checked assembly.

Accounting: unconditional Theorem 3.10 remains theorem-level 0%.
The dedicated P4 consumer/assembly machinery is approximately 98%, and
whole-HCG machinery remains approximately 60%.

## Inventory — DONE, verified, reuse (do not rebuild)

- **AA engine (fixed M, total metrics)**: `windowGInf` (`MetricPreconvWindowGInf.lean:520`,
  raw hypotheses `hgLip`/`hbdd`/`hlow`, NO solution field), `WindowGInfOut` (:506, ONE compact
  K, one p, produces fresh `⟨φ, gInf⟩`); `winGInfOfSol`/`winGInfOfData`
  (`MetricPreconvWindowSolutions.lean:403/435`) with `SolWindowData` (:136) + producers
  `hgLip0Sol`/`covBddAllSol`/`hgLipFinSol` (solution-driven bounds).
- **Pullback layer along a GLOBAL `Φ : M ≃ₘ⟮I,I⟯ N`** (all sorry-free, green 3877–3899):
  `solutionOn_pullback` + `isSolutionOn_pullback` (`SolutionPullback.lean` — all 9
  `IsSolutionOn` fields transport); `solWindowData_pullback` + endpoint `winGInfOfPullback`
  (`WindowDataPullback.lean:388/426`) + the metric/cov-bound transports
  (`metricUniformEquivalentOn(Window)_pullback`, `metricCovDerivNorm_pullback`,
  `metricCovDerivOrderBoundOn(Window)_pullback`, `solLowData_pullback`, `solSwapData_pullback`
  — same file :43–310); Shi transfer `MovingShiPullback.lean` (P1.3).
- **Partial→total primitives**: `SmoothRiemannianMetric.bumpExtendOpen` (+ inner/locality
  lemmas, `Geometry/Metric/BumpExtend.lean`); `convexComb` (+ `convexComb_inner`,
  `convexComb_eq_left_on`, `Geometry/Metric/ConvexCombination.lean`).
- **Norm bridges**: restriction-invariance `metricDerivNorm_restrictOpen` +
  `metricDerivNormSupOn_restrictOpen` (`MetricDerivNormRestrict.lean:289,~305`);
  pullback-invariance `metricDerivNorm_pullback`/`metricDerivNormSupOn_pullback_image`
  (`MetricCovDerivPullback.lean:458,482`).
- **Curvature restriction bricks (banked for Brick 1)**: `OpenSubtypeNaturality.lean`
  (Koszul/LC/metricCov restrict to opens), `RestrictOpenRm04.lean`
  (`connectionRiemannCurvatureField_restrictOpen`, `metricRm04StdAt_restrictOpen`),
  `PullbackNaturalityLocal.lean`/`PullbackNaturalityCross.lean`, `Metric/PullbackCross.lean`
  (cross-manifold `pullbackMetricCross`).
- **Comparison-map geometry**: `sourceTargetDiff : SourceDomain Φ k ≃ₘ TargetDomain Φ k`
  (`PointedConvergence.lean:~1315`), `ExhaustsByOpen.subset` (:471), `sourceCompactSet` (:966)
  + `sourceCompactSet_isCompact` (:987, contains the `Subtype.val '' · = K` computation),
  `SourceDomainMetricData.ofRestrictPullback` (:1232, `pullbackMetric` =
  `Diffeomorph.pullbackMetric (restrictOpen g_k) sourceTargetDiff`, `limitMetric` =
  `restrictOpen (L.S.family.metric t)` — hard-wired), `derivNormSupOn` (:1424).
- **Time-0 input**: `mc.convergence` (`MetricCompactness.lean:1062`, `MetricSourceCPConvOn`
  :968): `Φ_k^* g_k(0) → mc.limit.metric` in the source-domain C^p seminorm on compacts.
- **Assembly (done)**: `flowUpgrade_of_maps`, `flowUpgrade_of_mc`,
  `solutionComp_of_mc`, `cghMaps_of_hL0`, and
  `pointedCGHMaps_of_atZero` (`FlowLimitUpgrade.lean` /
  `SolutionCompactness.lean`).  The former exact-conclusion
  `SmoothFlowLimitInput` route was deleted.
- Diagonalization helper: `C4/DiagonalSubseq.lean`; Mathlib `CompactExhaustion` (σ-compact M).

## KEY architectural facts (read before coding)

1. `windowGInf` takes RAW `hgLip`/`hbdd`/`hlow` — no `SolutionOn`, no `hmet`. So the
   bump-extended (non-solution) sequence is legal input. The SOLUTION-driven producers are
   used per-k on the source domains to PROVE those raw bounds, then transported.
2. `WindowGInfOut` fixes ONE (K,p) and extracts a FRESH subsequence+limit per call. The conv
   field needs ONE subsequence and ONE global `gInf` for ALL (K,p,window) — Brick 3 upgrades
   the endpoint by diagonalization. The internal `hbdd` is already ∀-compacts, so the machinery
   supports it; the diagonal + limit-identification is the new content.
3. `FlowLimitData.L` requires `isSolution : IsSolutionOn L.S` (structure field,
   `Basic.lean:38–63`), so the FlowLimitData TERM waits for Brick 6 — but conv's PROOF only
   uses `L.S.family.metric = gInf`. Build gInf-first, L-term last.
4. The head of the sequence (k below the exhaustion threshold for a compact) uses the
   constant-R convention: `gSeqExt k t := R` there; all raw bounds are trivial or finite-max
   for the head.
5a. **ENDGAME-SHAPE RULING (2026-07-03, after the hsmooth scoping): do NOT block the phase on
   `hsmooth`.** The joint-regularity producer is an honest 6–10-session sub-project (kernel +
   C⁰ half landed, verified — `Analysis/Calculus/TimeSliceBootstrap.lean` +
   `HCGCompactness/FlowLimitRegularity.lean`; the four remaining sub-frontiers, incl. the one
   genuine wall (jets-of-Ricci algebra closure, GPT-Pro consult candidate), are isolated in
   `FlowLimitRegularity.md`). Therefore: **Brick 5 is a DATA-producing `def`** — package
   `(φ, gInf, the conv/identification properties)` as a structure (`Brick5Out`-style), not bare
   existentials — and **Brick 7's endgame theorem takes `hsmooth : MetricFamilySmoothOn …
   ({base := {metric := b5.gInf}}).family` as an explicitly-tracked input** (the same honest
   pattern as `hShi` and Theorem 3.9). 3.10⇐3.9 then closes modulo THREE tracked inputs:
   `metricCompactness` (Thm 3.9), `MovingShiBoundOn` (Shi), and `hsmooth`-of-the-limit — the
   first two cited by the book, the third with its own in-tree machinery track. Note the conv
   field itself never needs `hsmooth` (KEY fact 3); only the `L`-term's `isSolution` does, via
   `isSolutionOn_of_reg` (whose other inputs — hpde/scalar/ricci/rm04 continuity — are all
   produced: `metricLimit_pde`∘`ricciConv_of_dnConv`, `scalarConv_of_dnConv`,
   `metricTensorContLim`, `ricciConv`-family).
5b. **PARAMETRIZATION RULING for Bricks 4–5 (the phantom-L problem, decided 2026-07-02).**
   `SourceDomain` is indexed by `PointedCGHMaps X L subseq`, but `L : PointedFlowData` requires
   `isSolution` and so only exists after Brick 6 — while Bricks 4–5 must run before it. Do NOT
   try to build a provisional L (a constant family is not a Ricci flow), and do NOT work through
   `hL0.symm ▸ mc.maps` directly (the `▸` along the propositional `hL0` is stuck — cast hell).
   Instead: state Bricks 4–5 **parametrized by** `(L : PointedFlowData X.D)` and
   `(rmaps : PointedRiemannianCGMaps (X.atZero) (L.atTime 0) mc.subseq)`, working with
   `Φ := pointedCGHMaps_of_atZero X L mc.subseq rmaps` (`FlowLimitUpgrade.lean` — a pure field
   copy, hence defeq-transparent: `Φ.source k` is definitionally `(rmaps.partialDiffeomorph k).source`).
   Every mc-derived input (time-0 convergence seed for `initC`, time-0 equivalence, the cited
   Shi bounds on the sequence flows) enters as a HYPOTHESIS stated against `rmaps`. At Brick 7,
   instantiate `rmaps := hL0.symm ▸ mc.maps` and discharge those hypotheses from `mc` by
   `cases hL0` FIRST (which turns the `▸` into `rfl` and lets everything compute). Note
   `PointedRiemannianCGMaps` depends on its manifold index only through M/topology/charted
   (MetricCompactness.lean:35-47, never the metric), which is why the cases-discipline works.

## Bricks (dependency order; each = one focused session/subagent)

### Brick 1 — flow restriction to an open: `solutionOn_restrictOpen` + `isSolutionOn_restrictOpen`
**Status: DONE (verified, axiom-clean).** `SolutionRestrictOpen.lean`: `solutionOn_restrictOpen` +
`isSolutionOn_restrictOpen` (all 9 fields) sorry-free; targeted build green (3720 jobs),
`#print axioms isSolutionOn_restrictOpen = [propext, Classical.choice, Quot.sound]`. Carries
`[BoundarylessManifold I U] [IsManifold I 1 U] [IsManifold I ((∞)+1) U]` as hypotheses (Brick 2's
call site supplies them for SourceDomain/TargetDomain — see NOTE below). New crux sub-lemma
`Tensor0SFamilyContinuousOnSet.restrictOpen` landed in `Curvature/Realized/MetricFamilyContinuity.lean`
(needed import `Geometry/Metric/OpenSubtype`). Frame-transfer via `frameCompSmooth_restrictOpen`.
Curvature germ-locality: `ricciTensor_restrictOpen`/`metricRicci_restrictOpen_eval`/
`metricScalarAt_restrictOpen`/`metricRm04_restrictOpen_eval`. Notes + the TangentSpace-flavor-`rw`
gotcha in `SolutionRestrictOpen.md`. **NOTE for Brick 2:** `BoundarylessManifold I (SourceDomain/
TargetDomain)` is NOT auto-derived for opens — Brick 2 must construct it (open subset of a
boundaryless manifold; both `isSolutionOn_restrictOpen` and `isSolutionOn_pullback` require it).
(was: OPEN. The one missing transport link.)
New file `HCGCompactness/SolutionRestrictOpen.lean` (or `Geometry/Flow/RicciFlow/` layer if
cleaner). For `S : SolutionOn D` on `M`, `U : Opens M` (`[SigmaCompactSpace U] [T2Space U]`):
a `SolutionOn D` on `U` with `family.metric t = (S.family.metric t).restrictOpen U` and the
base data fields restricted (`rm04` via `metricRm04StdAt_restrictOpen`-style bricks), plus
`isSolutionOn_restrictOpen : IsSolutionOn S → IsSolutionOn (S.restrictOpen U)` — all 9 fields.
The PDE field restricts pointwise once `ricciTensor (g.restrictOpen U) x = ricciTensor g x`
(search `OpenSubtypeNaturality`/`RestrictOpenRm04` first — Ricci is a trace of the restricted
Rm/LC objects already banked; expect ≤1 new trace-restriction lemma). Regularity fields
restrict by locality of `ContMDiff`/continuity on opens (chart-of-subtype lemmas in
`OpenSubtype.lean`; `mdiffAt_restrictOpen_section` in `OpenSubtypeNaturality.lean`).
MODEL: mirror `SolutionPullback.lean`'s field-by-field structure.
*(real-but-bounded, volume in 9 fields; the curvature ingredients are banked)*

### Brick 2 — the per-k pulled-back flow on `SourceDomain Φ k`
**Status: DONE (core + metric-equiv restriction primitive, verified, axiom-clean).**
`HCGCompactness/SourceDomainFlow.lean` (new): `sourceFlow Φ k hσsrc hσtgt`,
`isSolutionOn_sourceFlow`, `sourceFlow_metric_eq` all sorry-free; targeted build green (3882 jobs),
`#print axioms = [propext, Classical.choice, Quot.sound]`. `sourceFlow_metric_eq` closes by `rfl`
(both sides = `pullbackMetric ((S_k.metric t).restrictOpen (targetOpen Φ k)) (sourceTargetDiff Φ k)`).
`BoundarylessManifold` on every domain is AUTO from `[I.Boundaryless]` (the key thinning enabler).
letI plumbing mirrors `ofRestrictPullback`; gotchas (don't `open ENNReal`; register U-instances at
the `↥(targetOpen)` form not the abbrev; `IsSolutionOn`/`SolutionOn` return type needs
`SigmaCompact`+`T2` for `gradientFun`) in `SourceDomainFlow.md`.
**Cited-input transports:** metric-equivalence restriction LANDED (`metricUniformEquivalentOn(Window)_restrictOpen`,
same file — definitional via `restrictOpen_inner`; composes with `metricUniformEquivalentOnWindow_pullback`
for Brick 4). `MovingShiBoundOn` restriction **DONE** (`MovingShiRestrictOpen.lean`, verified,
axiom-clean; targeted build green 3880 jobs, `#print axioms movingShiBoundOn_restrictOpen`
= `[propext, Classical.choice, Quot.sound]`). Landed the full chain: `covDerivOfField_restrictOpen`
(tower base naturality, NO `mfderiv` — vectors shared), `ricciSection_restrictOpen`,
**`ricCovTower_restrictOpen`** (analog of `ricCovTower_pullback`), `ricCovTower_normSq0S_restrictOpen`,
**`movingShiBoundOn_restrictOpen`** (endpoint). All banked restriction bricks
(Rm04/LC/metricCov/normSq0S + `extDerivFun_restrictOpen`) were exactly sufficient — NO new
curvature-restriction API needed; composes with `movingShiBoundOn_pullback` for the Brick-2
cited-input transport to `sourceFlow`. See `MovingShiRestrictOpen.md` (route + TangentSpace-flavor
gotchas). (was: DEFERRED — needed `ricCovTower_restrictOpen`, a Brick-1-addendum concern.)

### Brick 3 — all-compacts window endpoint `windowGInfAll`
**Status: DONE (verified, axiom-clean).** New file `MetricPreconvWindowAll.lean` (imports
`MetricPreconvWindowGInf` + `AllTimesBoundsFlow`); `windowGInfAll` sorry-free, targeted build green
(3885 jobs), `#print axioms = [propext, Classical.choice, Quot.sound]`. Signature took an extra
`[WeaklyLocallyCompactSpace M]` (for `CompactExhaustion.choice`) and the dense net `(e, he, hdense)`
+ ∀-compacts/∀-orders `hgLip` as hypotheses. KEY design fix: the naive "diagonalize per `(K_j,j)` and
glue per-`j` limits" FAILS (limits pinned only on each compact, no global metric / no cov-deriv
agreement); instead diagonalize the net-time **global (all-x) inner tendsto** (`netFullDiag`) so
`tendsto_nhds_unique` forces ONE global limit, build `gInf` from `metricPreconvFull` on `Kx 0`, and
identify per-`j` limits via new `metricLimit_uniq`. Reusable lemmas added: `metric_ext_inner`,
`metricInnerApply_diff_le`, `metricInner_cauchy`, `metricLimit_uniq`, `windowGInfPt`. See
`MetricPreconvWindowAll.md`. (was: OPEN. Independent of Bricks 1–2 (can run in parallel).)
In `MetricPreconvWindowGInf.lean` (or a new file importing it): same raw hypotheses as
`windowGInf` but hypotheses quantified over all compacts (they already are: `hbdd` is
∀-compacts; `hgLip` needs upgrading to ∀-compacts input) and conclusion
`∃ φ StrictMono, ∃ gInf : ℝ → SmoothRiemannianMetric I M, ∀ K IsCompact, ∀ p, ∀ ε > 0, ∃ k0, ∀ k ≥ k0,
∀ t ∈ Icc β ψ, metricDerivNormSupOn K p (gSeq (φ k) t) (gInf t) gRef < ε`.
Route: `CompactExhaustion` K_j (σ-compact M) + per-j nested application of the existing
extraction + `DiagonalSubseq` + identify the per-j limits (all equal the diagonal's limit by
uniqueness of pointwise/C⁰ limits along sub-subsequences — the inner-convergence output of
`metricPreconvFull` gives pointwise `Tendsto`, so uniqueness is `tendsto_nhds_unique`).
For ∀p: fold p into the diagonal (p_j := j) and use `MetricCPConvOn.mono_order`-style
monotonicity (`metricDerivNormSupOn` is monotone in p by sup-set inclusion). Windows: keep
[β,ψ] fixed in this brick; the conv field's per-window quantifier is handled in Brick 5 by
applying windowGInfAll to a countable window exhaustion of `X.D.carrier` inside the same
diagonal (design choice: either fold windows in here too — preferred if clean — or diagonal
once more in Brick 5).
*(real-but-bounded; the sole new analytic content is diagonal + uniqueness bookkeeping)*

### Brick 4 — the bump-extended sequence + raw hypotheses on `M_∞`
**Status: ✅ DONE — ALL THREE raw hypotheses (2026-07-03, planner-verified: build green 3912,
`#print axioms hgLip_gSeqExt = [propext, Classical.choice, Quot.sound]`).** `hgLip_gSeqExt`
landed via the banked m-fold tower (`iterCov_smulF_le`/`smulByFun_eq_product`,
`ProductMFoldNorm.lean` — the "missing χ-Leibniz" was already proved, stale-docstring trap)
+ two cited inputs (tail `gSeqExt`-granularity Lipschitz on `grow k`; per-k source-granularity
Lipschitz, dischargers = `hgLipFinSol`/`hgLip0Sol` on `sourceFlow`).  Final-mile repairs by the
planner after a third process crash: (1) the `SourceDomain Φ k` vs `↥(sourceOpen Φ k)`
instance-spelling gap blocks implicit resolution for `restrictOpen` — fixed by the file-level
`refRes` def passing instances explicitly after `change` (the `gSeqExt`/`ofRestrictPullback`
idiom; 31 call sites swapped); (2) generic-rank `HSub (Tensor0SField ∞ 2)` synthesis wall —
fixed by `set_option backward.isDefEq.respectTransparency false in` placed BEFORE the
docstring (the StarSum2 idiom; after the doc comment it's a parse error).
*(Superseded history below.)*
**(was: PARTIAL — 2 of 3 raw hypotheses DONE (2026-07-02).)** `ConvFieldAssembly.lean` delivers
sorry-free (targeted build green 3911 jobs, axiom-clean): `gSeqExt` (bump-extended sequence on `L.M`),
`BumpFamily` + `nonempty_bumpFamily` (coherent bump family: compact exhaustion + `findGreatest` index
+ normality collar + cutoff), `gSeqExt_inner_of_mem`/`_of_notMem` (eval), **`hlow_gSeqExt`** (the
`hlow` hypothesis, from a cited uniform source lower bound `cLow·R ≤ srcMetric`, via `≥ min(cLow,1)·R`),
and **`hbdd_gSeqExt`** (the `hbdd` hypothesis — NEW).  `hbdd`: cited hypothesis
`hcovTail : ∀ q, ∃ C, ∀ k t∈[β,ψ] ∀ z∈Φ.source k, metricCovDerivNorm q (gSeqExt k t) R z ≤ C`;
tail `k0 ≤ k` (`grow_cover`, `K' ⊆ grow ρk ⊆ Φ.source ρk`, `k ≤ ρk`) inherits `Ctail`, head/mid `k < k0`
each bounded by `metricCovDerivNorm_bddOn` (the CONSUMED unblocker, import added), combine by `max` +
`Finset.sup'`.  Added `bumpExtendOpen_inner`/`_of_notMem_tsupport` to `Geometry/Metric/BumpExtend.lean`.
Dense net = reuse `denseIccSeq`.  NOTE: the earlier "missing spatial continuity API" diagnosis is
RESOLVED — `metricCovDerivNorm_bddOn` LANDED and dispatches `hbdd` (which fixes `t` before `∃C`, so
each metric is a fixed smooth metric — no annulus/χ-Leibniz analysis).
**BLOCKED: `hgLip` (time-Lipschitz, all orders `a ≤ p`)** on the **χ-Leibniz collar tower**.  The time
difference is `gSeqExt k s − gSeqExt k t = χ_k·(src_s − src_t)` on `Φ.source k` (else 0; dichotomy
`z∈Φ.source k ∨ z∉tsupport χ_k` is total).  Order 0 is tractable (`|χ|·(order-0 source Lip)`), but
orders `a ≥ 1` on the collar `{0<χ<1}` expand `∇^a(χ·T)` into `Σ_i (∇^iχ)(∇^{a−i}T)` and need the
iterated χ-Leibniz NORM bound `|∇^a(χ·T)|_R ≲ Σ_i|∇^iχ|_R·|∇^{a−i}T|_R` — CONFIRMED MISSING (the
one-STEP `nabla0S_product_realizes` exists in `Tensor/RSTensor/ProductNablaLeibniz.lean`; the iterated
all-orders tower + norm sub-additivity is a ~1-session sub-project).  The consumer needs one `L` for
ALL `a ≤ p` (order-0-only is not consumable), and carrying the collar bound on all of `Φ.source k`
(vs only `grow k` where `χ=1`) is a forbidden frontier-wrapper.  See `ConvFieldAssembly.md`.
**→ UNBLOCKED (2026-07-02, parallel session; build green 3803 jobs, axiom-clean):**
`metricCovDerivNorm_cont`/`metricCovDerivNorm_bddOn` (∃C on any compact) and
`metricDerivNorm_cont`/`metricDerivNorm_bddOn` (∃C ≥ 0 uniform over orders `a ≤ p`) LANDED in new
`HCGCompactness/MetricCovDerivContinuity.lean`, over new
`Tensor0SBundle.normSq0S_cont`/`normSq0S_contAt` + slot-eval engine `tensor0SField_eval_cmdAt_slots`
(`Tensor/RSTensor/FiberMetric/Tensor0SMetricContinuity.lean` — trivialization local frame +
inverse-Gram Cramer continuity + `normSq0S_eq_coord`, no orthonormal frame needed).  For fixed
metrics — enough for `hbdd` head/mid since `hbdd` fixes `t` before `∃C`.  NOTE for `hgLip` orders
≥ 1 on the collar: continuity gives per-`(k,t)` bounds but NOT the `|s−t|` factor; the collar
Lipschitz needs the χ-Leibniz tower (`|∇^a(χ·T)| ≲ Σ|∇^iχ||∇^{a−i}T|`, grep-confirmed missing) OR
a carried hypothesis at source-flow granularity.  Notes: `MetricCovDerivContinuity.md`,
`Tensor0SMetricContinuity.md`.
(was: OPEN — ALL INPUTS READY (Bricks 1,2,3 + MovingShi transport all DONE/verified).) The bulkiest brick.
Available: `sourceFlow`/`isSolutionOn_sourceFlow`/`sourceFlow_metric_eq` (`SourceDomainFlow.lean`),
`movingShiBoundOn_restrictOpen` (`MovingShiRestrictOpen.lean`) ∘ `movingShiBoundOn_pullback` for the
moving-Shi input on `sourceFlow`, `windowGInfAll` (`MetricPreconvWindowAll.lean`) as the consumer,
`metricUniformEquivalentOn(Window)_restrictOpen`/`_pullback` for `hlow`.
New `HCGCompactness/ConvFieldAssembly.lean`. Fix `R : SmoothRiemannianMetric I M_∞`
(e.g. `mc.limit`'s metric). Build a coherent bump family: increasing opens `V_j` with
`K_j ⊆ V_j ⊆ closure V_j ⊆ source_{m_j}` (compact closure; `ExhaustsByOpen.subset` for m_j;
`exists_smooth_zero_one`-style bumps χ with `tsupport χ ⊆ source`), and per-k bump = the
largest j with m_j ≤ k. Define `gSeqExt k t := bumpExtendOpen R (source_{k-domain}) (pullback
metric of S'_k) χ_k …` for k ≥ m_1, else `R`. Prove the three raw hypotheses of
`windowGInfAll` for `gSeqExt` (gRef := R):
- `hbdd` (∀K' cov bounds): tail via Brick 2's flows + `covBddAllSol`-side bounds on
  `SourceDomain` + restriction-invariance (`metricDerivNorm_restrictOpen`) + the locality
  lemma (`bumpExtendOpen` = pullback on V); head/mid = finite max of sups of smooth metrics
  on a compact (continuity + compactness), or trivial for the constant-R head.
- `hgLip` (time-Lipschitz on compacts): tail via `hgLipFinSol`/`hgLip0Sol` on `S'_k`
  transported the same way; head: `metricDerivNorm a (R)(R) = 0`.
- `hlow`: from the window metric-equivalence (cited, transported) on V + convex-combination
  structure off V (both endpoints ≥ c·R).
Time-0 seed (`initC` for Lemma 3.11 inside the producers): from `mc.convergence`.
*(real-but-bounded, high volume; every transport lemma exists)*

### Brick 5 — one global `gInf`, identification, re-index, the `conv` field
**Status: ✅ DONE (2026-07-03, verified: targeted build green 3914, all 6 endpoints
`#print axioms = [propext, Classical.choice, Quot.sound]`, no warnings).**
`ConvFieldMain.lean` (new): `ConvOut` (ruling-5a data package: one `φ`/`hφ`, one global
`gInf`, sup-level `conv` = the windowGInfAll conclusion for `gSeqExt` along `φ`, PLUS
pointwise `convPt` along the SAME `φ` — the Brick-6 consumer shape, no fresh subsequence);
`convOut` (ONE `windowGInfAll` call; carried cited inputs verbatim at Brick-4 granularity:
`hbound`/`hcovTail`/`hlipTail`/`hlipSrc`, dischargers unchanged; `convPt` via the
`windowGInfAll_pt` BddAbove pattern in-line); `ofRP_supOn_eq` (per-index three-slot
identification on `K ⊆ grow k`, `hmet : L.S.family.metric t = gIt` — the pullback slot is
swapped against `resSrc (gSeqExt k t)` pointwise on the chi_one sub-open `O ⊆ SourceDomain`
via `metricDerivNorm_restrictOpen` ×2 + new `derivNorm_congr_left` (first slot depends only
on `metricTensorField`), then `supOn_congr_left` + `supOn_resSrc_eq` +
`sourceCompactSet_image_eq` land on `L.M`; `ofRP_supOn_def` = ONE-SHOT `rfl` through
`derivNormSupOn ∘ ofRestrictPullback` incl. `sourceFlow`); `ofRP_supOn_conv` (the conv-field
bridge at `(Φ, co.φ k)` granularity, hypothesis `hmetric : ∀ t ∈ [β,ψ],
L.S.family.metric t = co.gInf t` — Brick-6 discharger `rfl`); `gInf_zero_eq` (Step 4 DONE:
`co.gInf 0 = g0` from pointwise time-0 hypothesis `hconv0` in Φ-terms, mc-discharger =
`mc.convergence` via singleton-sup + `metricInnerApply_diff_le`, noted not executed;
`tendsto_nhds_unique` + `metric_ext_inner` + `ContinuousLinearMap.ext` — `.inner x` is
→L-bundled, `funext` fails).  `refRes` un-privatized in `ConvFieldAssembly.lean` (Brick-5
reuse).  Statements are for GENERAL `Φ` (5b-compliant; instantiate
`Φ := pointedCGHMaps_of_atZero X L subseq rmaps` at Brick 7).  Route + Brick-7 handoff
(compSubseq re-spelling expected rfl-style; hconv0/hmetric discharge recipes) in
`ConvFieldMain.md`.
**(was: OPEN. Needs Bricks 3–4.)**
- Apply `windowGInfAll` to `gSeqExt` → ONE `⟨φ, gInf⟩` for all (K,p,window in the exhaustion).
- `gInf 0 = mc.limit.metric`: both are limits of `Φ_k^* g_k(0)` on every compact
  (`mc.convergence` vs the AA output, bridged by restriction-invariance + locality);
  `tendsto_nhds_unique` pointwise + a `SmoothRiemannianMetric` ext lemma (add if missing:
  metrics equal iff `inner` equal — check `Geometry/Metric/Basic.lean`).
- Re-index `mc` along φ: ✅ **DONE (2026-07-02, verified)** —
  `MetricCompactnessConclusion.compSubseq` + layered `ExhaustsByOpen/PointedRiemannianCGMaps/
  MetricSourceData/MetricCGConvergenceData.compSubseq` + rfl simps `compSubseq_subseq/_limit/
  _source/_supOn` (`MetricCompactnessSubseq.lean`, build green, axiom-clean). KEY FINDING for
  the rest of Brick 5: `MetricSourceData (Φ.compSubseq …) k` is NOT type-defeq to
  `MetricSourceData Φ (φ k)`, but every FIELD reduces definitionally — the 11-field re-wrap
  `MetricSourceData.compSubseq` has no casts and `derivNormSupOn` is preserved by literal
  `rfl` (`compSubseq_supOn`). Consume that wrapper, do not reuse the type directly.
- The conv field: for K,p,[a,b],ε — `windowGInfAll` smallness on `gSeqExt` + locality
  (extension = pullback on V ⊇ K) + `metricDerivNormSupOn_restrictOpen` +
  `sourceCompactSet_image_eq` (extract from `sourceCompactSet_isCompact`) ⟹
  `(ofRestrictPullback …).derivNormSupOn K p t < ε` for k ≥ max(k0, threshold). This is the
  three-slot identification: gk = restrictOpen(gSeqExt) on V (locality), gInf-slot =
  restrictOpen(gInf) (hard-wired once L.metric := gInf), gRef-slot = restrictOpen R (set
  `refMetric k := restrictOpen R`).
*(bounded; the delicate spot is quantifier/threshold bookkeeping)*

### Brick 6 — the `L` term: limit flow + the PDE (parallel-izable after Brick 5's gInf)
**Status: REGULARITY/PDE/SCALAR CLOSED; OPEN ENDGAME PENDING (2026-07-17).**  The local bump equation
(`gSeqExt_ricci`, `gSeqExt_pde`), the limit equation (`ConvOut.gInf_pde`), and
the scalar pullback producer (`gSeqExt_scalar`, `ConvOut.scalar_conv`) are
checked.  `flowLimit_of_reg` assembles these internally but is compatibility-only
because its fixed-window hypotheses collapse carrier, regular set, and window.
Fixed-window joint chart-Gram regularity is now proved by `ConvOut.gramSmooth`,
and `OpenConvOut.smoothMetric_of_conv` packages it on the open interval.  The
honest open endgame and all-time completeness producer remain open.
- `L : PointedFlowData X.D` with manifold data copied from `mc.limit` (defeq-preserving, so
  `hL0 : L.atTime 0 = mc.limit` reduces to the Brick-5 metric identification), `S.family.metric
  := gInf`, and base curvature data (`rm04`/`ricciAt` fields of `SolutionFamily`) := the
  canonical ones of `gInf`.
- `IsSolutionOn L.S`: regularity fields from smooth `gInf` (+ `ricci_continuous_in_metric_time`,
  `RicciContinuityInMetricTime.lean:1154`, and its chart-continuity companions). The `equation`
  field `∂ₜ gInf = −2 Ric(gInf)`: ✅ **BOTH HALVES PROVED (2026-07-02, verified)** — compose
  `metricLimit_pde` (`LimitSolutionEquation.lean`, PDE passage) with `ricciConv_of_dnConv`
  (`RicciFromJets.lean` — the hRicConv producer: `ricciSub_le_dNorm` gives
  `|Ric(u)−Ric(u′)| ≤ C·Σ_{a≤2}‖∇̂^a(u−u′)‖` pair-uniformly from equivalence + C² bounds;
  `jet2Diff_le_dNorm` = the once-"missing" covariant→chart-jet conversion, proved by reusing
  the P3 tower engine + the DeTurck-coefficients perturbation layer). Inputs match
  `windowGInfAll_pt` + window equivalence.
  **REGULARITY-ROUTE NOTE for the remaining L-term packaging (2026-07-02):** `IsSolutionOn`'s
  other fields (`smoothMetric : MetricFamilySmoothOn`, scalar/ricci/rm04 continuity, …) demand
  FAMILY (t,x)-regularity of `gInf`, but the AA output gives per-time smoothness + time-Lipschitz
  only. The book gets joint regularity by running the AA on SPACETIME (`g+dt²` on `M×(α,ω)`,
  chapter3.tex:842-846) — heavy to formalize. Cheaper routes, in order: (1) READ what
  `MetricFamilySmoothOn` and the other fields actually demand (they may be per-time + continuity
  packages, not joint chart-C^∞); (2) route through the BBS-track builder
  `isSolutionOn_of_extendData` (`Evolution/ExtendedSolutionRegularity.lean`, sorry-free — built
  for exactly this "construct IsSolutionOn from family data" purpose; check its input record);
  (3) PDE bootstrap (`∂ₜg = −2Ric(g)` upgrades time-regularity: ∂ₜ-derivatives express through
  spatial jets). Decide after (1).
  ✅ **equation bridge LANDED (2026-07-02, build green 3888, axiom-clean)** —
  `LimitSolutionEquation.lean`: `metricLimit_pde`/`metricLimit_pdeOn` prove the PDE passage on
  the CLOSED window (endpoints included; fresh convex-set `hasDerivWithinAt_lim`, since Mathlib's
  uniform-limit-deriv needs an open set); sole remaining input = `hRicConv`.
  ✅ **`hRicConv` producer LANDED (2026-07-02, verified):** `RicciFromJets.lean`
  (build green 3925, all 3 endpoints axiom-clean, no sorry) — `ricciConv_of_dnConv`
  matches `metricLimit_pde`'s `hRicConv` verbatim, from: pointwise-at-x seminorm
  smallness `metricDerivNorm a (gSeq k t) (gInf t) gRef x < ε` (a ≤ 2, uniform in t —
  the z = x instance of Brick 5's hconv), window equivalence LOWER bounds
  `lam·gRef ≤ gSeq k t, gInf t` at x, and window covariant bounds
  `metricCovDerivNorm a · gRef x ≤ B` (a ≤ 2) for BOTH families.  Per-pair core
  `ricciSub_le_dNorm` (∃C uniform over the metric pair); the diagnosed missing
  covariant→chart-jet conversion is `jet2Diff_le_dNorm` (proved via the P3 tower
  identity `fderiv_chartRep_eq_towerStep` + CS `abs_apply_le_sqrt_normSq0S`); the
  chart-Ricci modulus algebra was REUSED from the DeTurck perturbation layer
  (`Analysis/Spectral/Intrinsic/DeTurckCoefficients/` — `ChristoffelPerturbation`/
  `RicciDiffAffine`, pair-uniform re-assembly).  Route + reuse map in
  `RicciFromJets.md`.  NB `metricLimit_pdeOn` consumes the
  POINTWISE seminorm form, not `metricDerivNormSupOn`. ✅ **Pointwise variant LANDED
  (2026-07-02, verified):** `windowGInfAll_pt` (`MetricPreconvWindowAllPt.lean`, build green,
  axiom-clean) — same hypotheses as `windowGInfAll`, pointwise conclusion (∀a≤p ∀x∈K smallness);
  + reusable `derivNorm_le_cov_add`/`derivNorm_le_sup_sing`. CAUTION (recorded in its .md):
  `Real.sSup` of an unbounded set is junk 0 — "sup < ε ⟹ pointwise" is UNSOUND without
  `BddAbove`, which must be discharged from `hbdd`-type data (the file shows the pattern).
  Brick 5's conv bridge still needs the SUP-level `derivNormSupOn < ε`: derive it from the
  pointwise form + the same `BddAbove` pattern (bound the sup-set, then `csSup_le`/`Real.sSup_le`).
- **L-term builder ✅ LANDED (2026-07-02, planner-verified: build green 3692, all 3 endpoints
  axiom-clean):** `FlowLimitBuild.lean` — `isSolutionOn_of_reg` (9-field IsSolutionOn from
  honest inputs: `hsmooth : MetricFamilySmoothOn` + `hpde` (= `metricLimit_pdeOn`-shape) +
  4 curvature-continuity fields; per-time fields discharged internally), `flowOfMetric`
  (PointedFlowData constructor, manifold data copied definitionally from a
  PointedRiemannianManifold), `flowOfMetric_metric`/`flowOfMetric_atTime` (the Brick-7 `hL0`
  reduction to the time-0 metric identification). Phase-A field-by-field demands + route
  ruling in `FlowLimitBuild.md`. **Remaining hard input = `hsmooth`:** `MetricFamilySmoothOn`
  genuinely demands JOINT (t,x) C^∞ (`frameCompSmooth` on `D.regular ×ˢ u`) — the AA gives
  per-time C^∞ + time-Lipschitz; joint upgrade = a dedicated brick (bootstrap via the PDE, or
  spacetime-AA per the book).  **hsmooth brick STARTED (2026-07-03): route DECIDED = limit-side
  PDE bootstrap** (spacetime-AA ruled out: eq-(3.4) as formalized has NO mixed ∂ₜ^q bounds);
  full route + statement chain in `FlowLimitRegularity.md`.  Analytic kernel LANDED + VERIFIED
  (`Analysis/Calculus/TimeSliceBootstrap.lean`, 4 endpoints axiom-clean): `hasFDerivAt_of_slice`
  (joint differentiability from time-slice PDE — the "continuous partials" lemma Mathlib lacks),
  `contDiffOn_succ_of_pde` (induction step, jet-level-generic), `contDiffOn_one_of_pde` (first
  bootstrap step, joint C¹), `contDiffOn_inf_of_pde` (C^∞ endpoint).  NB the ⊤-vs-∞ bug of the
  old memory note is FIXED in-tree (MetricFamily.lean:545 reads ∞; C^∞-frame form).  Remaining
  sub-frontiers: (a) neighborhood-uniform covariant→chart-jet conversion (jet2Diff_le_dNorm is
  single-point-anchored), (b) the ∂ₜ-past-spatial-jets swap (FTC + parametric interval
  integral), (c) jets-of-Ricci-algebra closure at all orders (THE wall; Mathlib FaaDiBruno /
  functional Leibniz routes listed in the .md), (d) de-compactify + general-D the ESR chartGram
  reduction (audit says `[CompactSpace M]` likely unused; `omit` + rebuild).
  **C⁰ HALF of hsmooth LANDED + VERIFIED (2026-07-03, same session):**
  `FlowLimitRegularity.lean` (build green 3637, 4 endpoints axiom-clean) —
  `chartGram_sub_le`/`chartGramBound_contOn`/`chartGramLim_contOn` (locally-uniform-limit
  transfer from Brick-5-shaped order-0 `hconv` + per-k joint chartGram continuity) +
  endpoint `metricTensorContLim` (`Tensor0SFamilyContinuousOnSet` for `gInf` on the window
  = the `metricTensor_cont` field; `coeff_cont` follows by evaluation).  Remaining for
  hsmooth = the C^∞ half: (a)+(b)+(c)+(d) above.
- `scalar : ScalarPullbackTendsto`: ✅ **CONCRETE PRODUCER CHECKED
  (2026-07-17).**  `RicciFromJets.lean` supplies the analytic estimate
  `scalarConv_of_dnConv`; `ConvFieldPDE.gSeqExt_scalar` identifies the scalar
  curvature of the bump extension with the genuine pulled-back source metric on
  the grow region; `ConvOut.scalar_conv` combines these with `co.convPt` and
  exhaustion to obtain scalar pullback convergence for
  `Φ.compSubseq co.φ co.hφ`.  `flowLimit_of_reg` now constructs this field
  internally rather than accepting a scalar-convergence premise.  This closes
  the scalar producer only; it does not repair the fixed-window/global-carrier
  mismatch.
- `hσsrc`/`hσtgt`: ✅ **DONE (2026-07-01, verified)** — `Geometry.isSigmaCompact_of_isOpen`
  (`Geometry/Topology/SigmaCompactOpen.lean`, build green, axiom-clean, no T2 needed; both
  consumer shapes `Φ.source_open`/`Φ.target_open` under the letI instances checked to compose;
  recipe in `SigmaCompactOpen.md`).
*(hard-frontier in the `equation` field; the rest bounded)*

### Brick 7 — endgame wiring (SPLIT 2026-07-03: 7a discharge chain → 7b assembly)

**7c — open-window capstone** *(Status: ✅ DONE 2026-07-18 —
`ConvFieldOpenEndgame.lean` checks the open solution/upgrade readout and
`ConvFieldOpenAssembly.lean:open_upgrade_of_raw` checks the full raw-input
assembly, including completeness of every time slice.  The exact module
refresh is green and the new source files are sorry-free.  Remaining work is
strictly upstream production of the four raw window packages and preservation
of the canonical time-zero convergence witness.)*

**7a — execute the carried-input discharge chain** *(Status: ✅ DONE 2026-07-04 —
`ConvFieldInputs.lean`, targeted build green 3916 jobs, all 6 endpoints axiom-clean, no
sorries; verbatim-pluggability into `convOut`/`gInf_zero_eq` elaboration-checked with a
temporary example, then removed).*  Producers: `hbound_of_equiv` (cLow = `(Crel·Bmax)⁻¹`,
from target-side window equivalence `hequivT` + reference relation `hrel` via the two
banked equivalence transports + new `equivOn_trans`); `covTail_of_bounds` (q=0 from the
two-sided `gSeqExt`-vs-`R` equivalence + NEW explicit-constant `covNorm0_le`; q≥1 via NEW
reverse triangle `covNorm_le_add` + NEW metric-compatibility `covNorm_self_succ`
(`∇_R^{q≥1}R = 0`, from `nabla_metric_zero`) + support dichotomy + `iterCov_smulF_le`
with cited `hcovSrc` (uniform source cov bounds on the tsupport diagonal) and `hchi`
(uniform bump-tower bounds — construction-side, see ledger)); `lipTail_of_src` (pure
locality from cited `hlipG` (uniform source Lipschitz on the grow diagonal) via NEW
`derivNorm_congr_diff`); `lipSrc_of_soln` (FULLY produced per-k: `hgLip0Sol`+`hgLipFinSol`
on `sourceFlow` with packs from `covOrderBound_of_soln` + `solnTowerSwap_reg` +
`metricCovDerivNorm_bddOn`, Shi via `srcShi` = restrictOpen∘pullback transports);
`conv0_of_cp` (singleton-sup + `metricInnerApply_diff_le`).  HONESTY LEDGER
(`ConvFieldInputs.md`): `hcovSrc`/`hlipG` are cited UNIFORM-in-k (in-tree per-k producers
hide constants behind `Classical.choose` — verified; uniform versions = the eq-(3.4)
citations); `hrel` = whole-source-domain time-0 comparability (3.9-side, formalized 3.9
carries no equivalence field); `hchi` exists ONLY because `hcovTail` was frozen on all of
`Φ.source k` though its consumer uses it on `grow k` only — 7b options: weaken `hcovTail`
to grow-granularity (cheap, dissolves `hchi`) / uniformly-regular bumps / carry it.
`hcp`-discharge caution: `mc`'s `MetricCGConvergenceData.domain` is an abstract field —
3.9's statement may need pinning to `ofRestrictPullback` data.
Original dispatch text:
Bricks 4–5 carried five cited inputs with dischargers "noted, not executed". 7a produces them
from honest THEOREM-LEVEL inputs (the window metric-equivalence and moving-Shi bounds for the
sequence flows — the book-cited hypotheses — plus `mc.convergence`):
1. `hbound` (uniform source lower bound `cLow·R ≤ srcMetric`) — from the transported window
   equivalence (`metricUniformEquivalentOnWindow_pullback` + `_restrictOpen`, both banked).
2. `hcovTail` (tail covariant bound for `gSeqExt` on `Φ.source k`) — from the transported
   window covariant bounds via `covBddAllSol`-side machinery on `sourceFlow` + the
   `gSeqExt = pullback`-on-source locality + restriction-invariance.
3. `hlipTail`/`hlipSrc` (time-Lipschitz at both granularities) — from `hgLip0Sol`/`hgLipFinSol`
   run on `sourceFlow Φ k` (they consume the flow equation — that is why Brick 2 exists) +
   `MovingShiPullback`/`MovingShiRestrictOpen` for their Shi inputs + transports.
4. `hconv0` (pointwise time-0 convergence feeding `gInf_zero_eq`) — extract from
   `mc.convergence`'s `MetricSourceCPConvOn` (sup→pointwise on the source domain; the
   `metricDerivNorm_le_…`/`derivNorm_le_sup_sing` pattern, order 0).
Per ruling 5b everything is stated against `(L, rmaps)`; the `mc`-instantiation happens in 7b.

**7b RULINGS (planner, 2026-07-03, from the 7a report):**
(A) `hcovTail` granularity: 7a showed `hbdd_gSeqExt` uses its `hcovTail` only on `grow k`, and
the all-of-`Φ.source k` freezing forced an artificial bump-tower citation `hchi`. 7b SHOULD
weaken `hcovTail` to grow-granularity in `ConvFieldAssembly.lean` (hypothesis-weakening =
strictly stronger theorem) and drop `hchi` from the chain, updating the `ConvFieldMain`/
`ConvFieldInputs` call sites.
(B) the `mc.domain` abstractness caution: to discharge the time-0 input from `mc.convergence`,
READ `MetricSourceData`'s property fields first (limit_inner/pullback_inner are pinned to the
canonical metrics; check what pins `referenceMetric`). If the reference is genuinely free, add
ONE honest equivalence hypothesis about `mc`'s reference data as a tracked input of the 7b
endgame theorem. Do NOT change Theorem 3.9's public conclusion (`MetricCompactnessConclusion`).

**7b — the assembly** *(Status: ✅ DONE 2026-07-07 — the endgame theorem `flowLimit_of_mc`
is WRITTEN + PROVED, targeted build green 3923 jobs, `#print axioms flowLimit_of_mc =
[propext, Classical.choice, Quot.sound]` sorry-free.  The phantom-L refactor (2026-07-06)
re-indexed the AA machinery by `P`; then `flowLimit_of_maps` (abstract `P` + `hPlim : P =
mc.limit` universe-tie + `hPL : L.atTime 0 = P` + `subst hPL` inside its own proof —
sidesteps the occurs-check and cast-hell) lets `flowLimit_of_mc` instantiate at `P :=
mc.limit` with the maps `Φ₀` DIRECTLY, no cast.  It takes `mc` + the honest tracked producer
outputs `co`/`hzero`/`hsol`/`scalar` (each with its verified discharger — `convOut`+7a,
`gInf_zero_eq`, `isSolutionOn_of_reg` per ruling 5a, `scalarConv_of_dnConv`) and builds
`L := flowOfMetric X.D mc.limit co.gInf hsol`, `hL0 := flowOfMetric_atTime`.  REMAINING =
wiring those 4 producer outputs from the deeper cited inputs (large but mechanical,
verbatim-pluggable ledgers).  See `ConvFieldEndgame.md` §2026-07-07.  Below = the earlier
PARTIAL note.)*
Earlier note *(2026-07-04, superseded)*: `ConvFieldEndgame.lean` (new): `flowLimit_of_co` — the full
7-field `FlowLimitData` assembly → `flowLimit_upgrade` → `CompactnessConclusion X`, taking
`(mc, L, hL0, R, bf, hsrc, htgt, β, ψ, hcarrier, co, hLmetric, scalar)` as inputs. VERIFIED: build
green 3923 jobs, `#print axioms flowLimit_of_co = [propext, Classical.choice, Quot.sound]`
(no sorryAx). All 7 fields discharged (σ-compact via `isSigmaCompact_of_isOpen`, `refMetric` via
`refRes`, `conv` via `ofRP_supOn_conv` — the `compSubseq` re-index reduces `ofRestrictPullback`
by `rfl`, no `▸`-cast). Rulings A SKIPPED (carry `hchi`; `covTail_of_bounds` already proves the
`Φ.source k`-granular statement — weakening exceeds the ~1-edit budget), B resolved
(`referenceMetric` free, `hcp` carried flow-side). **REMAINING = the phantom-L instantiation
circularity** (the genuine frontier): `L := flowOfMetric mc.limit co.gInf …` needs `co`, but
`co : ConvOut (endgamePhi mc L hL0)` needs the TERM `L`; no dummy `L₀` exists (PointedFlowData
needs `isSolution`, the only solution metric IS `co.gInf`). RESOLUTION IDENTIFIED (not executed):
`PointedCGHMaps` (`PointedConvergence.lean:499`) uses `L` ONLY via `L.M/topology/charted/basepoint`
— so re-parametrize the `Φ`-indexed AA machinery (`PointedCGHMaps`+`SourceDomain`/`sourceFlow`/
`gSeqExt`/`ConvOut`/`convOut`/`ConvFieldInputs`+`FlowLimitData.maps`) by a manifold-data record
instead of `PointedFlowData L`; then build AA over `mc.limit` → `gInf` → `L := flowOfMetric mc.limit
gInf hsol` → maps over `L` by defeq. ~1 focused refactor session (mechanical; only 4 projections of
`L` appear). SEPARATE blocker: `RicciFromJets.lean` has double-encoded-unicode mojibake
(`≤`→`â‰¤`, `:1916`/`:2033`) failing to compile — parallel session's file, blocks the PDE-input path
(re-add the 3 omitted imports after repair). See `ConvFieldEndgame.md`. *(orig 7a-verified note:* `co := convOut …` (Brick 5); the limit-PDE
inputs for `isSolutionOn_of_reg` from `co.convPt` + 7a bounds via
`metricLimit_pde`∘`ricciConv_of_dnConv` and `scalarConv_of_dnConv` + `metricTensorContLim`;
`L := flowOfMetric … co.gInf (isSolutionOn_of_reg … hsmooth …)` (hsmooth = tracked input,
ruling 5a); `hL0` via `flowOfMetric_atTime` + `gInf_zero_eq`; re-index `mc.compSubseq co.φ
co.hφ`; instantiate `rmaps := hL0.symm ▸ (mc.compSubseq …).maps` and discharge the 7a inputs
by `cases hL0`; construct `FlowLimitData` (`maps := cghMaps_of_hL0 …`,
`conv := ofRP_supOn_conv …`) → `flowUpgrade_of_mc` → `solutionComp_of_mc`.
Do not restore the deleted exact-conclusion compatibility backend.

TOOLING NOTE (2026-07-03/04): PowerShell 5.1 has TWO Lean-file-corrupting traps.
(1) `Add-Content/Set-Content -Encoding utf8` writes a BOM → empties Lake's importArts →
misleading "unknown configuration option" on fresh builds. (2) WORSE: `Get-Content` on a
no-BOM UTF-8 file decodes as cp1252, so a Get-Content→Set-Content round-trip MOJIBAKES every
math symbol (`≤` → `â‰¤`; this hit `RicciFromJets.lean` on 2026-07-03, repaired byte-exactly
on 2026-07-04 by re-encoding UTF-8-read text back through cp1252). NEVER round-trip Lean
files through Get-Content/Set-Content. For temporary axiom-prints and trims use
`[System.IO.File]::ReadAllText/WriteAllText` with `[System.Text.UTF8Encoding]::new($false)`.

**⚠ 7b-final RULING CORRECTED by the 2026-07-04 dry-run (two empirical findings — the
authoritative, de-risked spec is now `ConvFieldEndgame.md`; read THAT, not just this ruling):**
(1) the PointedCGHMaps↔PointedRiemannianCGMaps UNIFICATION is import-blocked
(`MetricCompactness` imports `PointedConvergence`) — use a plain structure re-index by
`P : PointedRiemannianManifold` inside `PointedConvergence` (no `X.atZero` needed there);
(2) the OUTPUT-convergence layer (`ScalarPullbackTendsto`, `PointedCGConverges`/
`SmoothCGHConverges`, `CompactnessConclusion`/`flowLimit_upgrade`) needs the limit flow's
METRIC FAMILY, which `P` lacks — those structures STAY over `L : PointedFlowData` with maps
typed over `L.atTime 0`. The maps/domain layer re-indexes by `P`; the family-threading of the
output layer is the genuine remaining scope. The ~270-reference bulk rename is validated
scriptable (mojibake-safe Python transform, dry-run 2026-07-04, restored per discipline).
**Original ruling (partially superseded):** the salvaged
assembly core `ConvFieldEndgame.lean:flowLimit_of_co` is verified axiom-clean but takes
`L`/`co`/`hLmetric`/`scalar` as inputs; instantiating them hits the circularity (`co`'s TYPE
is indexed by `Φ`-over-`L`, `L`'s metric is `co.gInf`). Resolution = re-index the maps layer
by a `PointedRiemannianManifold` instead of `PointedFlowData`: `PointedCGHMaps X L subseq`
provably uses `L` ONLY through `M/topology/charted/basepoint` (`PointedConvergence.lean:~499`)
— all fields of `PointedRiemannianManifold`, and `mc.limit` IS one. Design: change the index
of `PointedCGHMaps` (and the `SourceDomain`/`sourceFlow`/`gSeqExt`/`ConvOut`/producer chain)
to `(P : PointedRiemannianManifold)`; note it likely UNIFIES with `PointedRiemannianCGMaps`
(same 4 fields, targets defeq via `atZero`) — prefer unification over a parallel record if the
diff stays surgical. `SourceDomainMetricData.ofRestrictPullback`'s `limitMetric` field uses
`L.S.family.metric t` — pass the metric family as a separate argument there (the Brick-5 conv
statement already mediates it through `hmetric`, so consumers are hypothesis-compatible).
`FlowLimitData.L` remains `PointedFlowData`; its `maps` field re-types over `L.atTime 0` and
`cghMaps_of_hL0`/`pointedCGHMaps_of_atZero` simplify or disappear. Instantiation order after
the refactor: `co := convOut` over `P := mc.limit` → `L* := flowOfMetric X.D mc.limit co.gInf
(isSolutionOn_of_reg … hsmooth …)` → `hL0` via `flowOfMetric_atTime` + `gInf_zero_eq` →
`flowLimit_of_co`. No circularity remains.

## Danger points (read twice)

- **Subsequence discipline**: ONE φ from Brick 3 serves everything; `mc` must be re-indexed
  along it BEFORE building maps/conv (Brick 5). Do not extract fresh subsequences per compact.
- **Do not feed bump-extended metrics to solution-driven producers** (`hgLip0Sol` etc. use the
  flow equation via `hmet`); run producers on the genuine `S'_k` (Brick 2) and transport.
- The `IsManifold I 1/2/(∞+1) U` instances for subtypes: derive as in `Basic.lean:49–63` /
  `letI` blocks of `ofRestrictPullback`; watch for instance-diamond `letI` mismatches — reuse
  the exact `sourceDomTop/Charted/Smooth` spellings.
- `metricDerivNormSupOn` is an `sSup` over a possibly-unbounded set — reuse its existing
  API (`AllTimesBoundsFlow.lean:420` `metricDerivNorm_le_metricDerivNormSupOn` and the
  bounded-above lemmas nearby) instead of raw `csSup` fights.
- Head-of-sequence: `k0`s must be `max`-ed with exhaustion thresholds; keep a single named
  `threshold : ℕ` helper to avoid `omega` drift.
- **UTF-8 BOM corruption trap (2026-07-03)**: a fresh compile failing with
  `invalid -D parameter, unknown configuration option 'linter.style.emptyLine'` means the
  FILE's first bytes are `EF BB BF` (some tool re-saved it as cp1252→UTF-8-with-BOM): the BOM
  breaks Lake's import scan (`setup.json` gets `"importArts": {}`), so options are validated
  against an empty closure.  Check the file head, not the lakefile.  `ConvFieldAssembly.lean`
  was hit (repaired byte-reversibly, incl. double-encoded unicode); `RicciFromJets.lean`
  still carries a BOM (owning session should strip it before its next build).

## Acceptance (planner verifies per brick)

Targeted build green; `#print axioms <endpoints>` = `[propext, Classical.choice, Quot.sound]`;
statements read against this plan (no vacuity, no hypothesis-wrapper adapters, conclusion is
the stated one); same-name `.md` updated with route + gotchas; this plan's Status line flipped.

## Honest denominator

The unconditional Theorem 3.10 endpoint remains 0%: `compactnessSol` is now
stated with one explicit P4 `sorry`, but is not proved.  The fixed-window PDE,
scalar, joint chart-Gram smoothness, open endgame, and raw-input capstone are
checked, so the dedicated P4 consumer/assembly machinery is conservatively
about 98%.  The
common subsequence, compatible limit family, upgrade record, and all-time
limit completeness are now checked from the existing raw fixed-window
hypotheses.  The remaining genuine work is to produce those hypotheses
uniformly on every canonical window.  Canonical time-zero convergence
provenance through Step D is already checked.  The checked `ConvOut.gramSmooth`,
`OpenConvOut.smoothMetric_of_conv`, and `open_upgrade_of_raw` close the
fixed-window-to-open consumer path. Hamilton's
nonregular endpoint extension is tracked separately and is
not needed to prove the book theorem.  Whole-HCG machinery remains about 60%.
The completed selected Step B/C producer and conditional Theorem 3.9 accounting
are unchanged.

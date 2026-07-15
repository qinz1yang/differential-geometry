# STEP D PLAN — directed system, direct limit, and the Theorem 3.9 assembly

Written 2026-07-05 (planning/acceptance lane).  Self-contained execution plan for
MSM135 Chapter 4 Step D, chapter4.tex **L1883–2102** (`\subsection{The directed
system}` through the completeness proposition), at `STEPB_PLAN.md` granularity.

**Endpoint being served:** `C4/MetricCompactnessInputs.lean:
MetricCompactnessInputs.metricCompactness` — the conditional Theorem 3.9 (ruling
2026-07-05).  Step D is the final assembly: everything below feeds its `sorry`.
Do NOT target the unconditional `metricCompactness` (see its docstring).

**Book fidelity rule:** one Lean declaration per book result, book order, honest
inputs only where the book cites externally.  All four D-results are proved in
the book — no new honest inputs are budgeted for Step D itself.  If a brick
seems to need one, stop and report (it means an upstream producer is misshapen).

---

## Current execution structure (2026-07-13)

This section is the active running source of truth.  The older D1--D6 sections
and chronological codas below are kept for proof-route detail, but this current
status overrides stale instructions such as starting with D3 or treating D5 as
unfinished.

Overall accounting, by endpoint:

- `MetricCompactnessInputs.metricCompactness`: theorem body still 0% complete;
  the endpoint is still a `sorry`.
- Conditional Step-D assembly `compactness_of_b1`: 100% stated and proved from
  the honest `StepB1RawInput` package.  It constructs the strict subsequence,
  common limit, completeness, original-member maps, and convergence.
- Step-D consumer machinery: 100%.  D1's conditional recursion, D2's common
  diagonal and metric cocycle, D3's smooth metric direct limit, D4 convergence,
  D5 completeness, and D6 reindex/field assembly are checked.  The former D6
  maps-indexed convergence blocker is closed by `repoint`, `unrepoint`, and
  `ofSubseq`; do not restart it.
- D1b conditional consumer `directed_of_b1`: body is 100% checked.  The F4/F5
  uniform constant chain is proved and checked downstream.  The false P-only
  `stepB1_approxIso` was removed; `directed_of_b1` now exposes the missing B/C
  mathematics as `StepB1RawInput`.  The textbook D1b theorem from the endpoint
  hypotheses remains 0%.

Active dependency lanes for the endpoint (Step-D consumer itself is complete):

1. **Lane 1: D1 axiom-clean composition frontier.**
   Do not restart the `StepDDirected.lean` `hacc` recursion.  It is closed.
   `compSepFwd` and `compSepRev` are now proved in `PullbackField.lean`, reusing
   the existing `partialData_comp` proof organs with separated ledgers.  The
   downstream D1b consumer checked after the refresh.  The remaining Lane 1
   branches are now:
   - B1: produce `StepB1RawInput` from the C-track data; the missing work is the
     honest-input bundle / instantiation that
     supplies POU weights, target convergence, center-input data, local
     diffeomorphism/injectivity, and forward/reverse bounds.
   - F4/F5: **closed 2026-07-09.**  `claim1MulConst` and
     `lemma45_F3_bound` expose data-independent scaled constants;
     `RicBoundGoodFrame.metricComp_mul` absorbs the good-frame and metric-swap
     losses into `4^(2+p)`; `lemma45_corII`, `lemma45_corII_unif`, F5,
     `PullbackField`, and `StepDDirected` all verify.  No F4 `sorry` remains.

2. **Lane 2: D2 limiting metrics.**
   `C4/StepDLimitMetrics.lean` now contains the verified realization chain
   `ballSystem` -> `ballSystemOfData` -> `directedBallSystem`: the eventual D1
   data yields a tail-shifted `SmoothSeqSystem` of open balls.  D2a is now
   complete: the concrete fixed-stage pullback sequence has checked per-order
   `hbdd`, fixed-base `hlow`, and a `MetricCInfConvOnCompacts` limit through
   `metricCInf_refs`.  `exists_chain_data` derives its inputs from the original
   eventual D1 package.  D2b is complete: `exists_limits_close` returns one
   common diagonal, all fixed-stage limits, and the uniform all-tail `lbl407`
   estimate.  D2c is also complete: the same output carries the pointwise
   pullback cocycle for adjacent limit metrics.  The D6 audit additionally
   requires shrunk stages of radius `2^n`: their source/image control, closed
   ball containment, smooth system, and compact successor containment are
   checked.  `tailMetric` now restricts the already-constructed large-stage
   limits to those shrunk stages, and `tailMetricCocycle` proves their full
   compatibility without rerunning D2.

3. **Lane 3: D4b/c convergence to the limit — complete.**
   D4a (`limitCGMaps`) is done.  `limitCGConverges` and `chainCGConverges`
   provide the subtype-target form.  `PartialDiffeomorph.liftTargetOpen`,
   `chainAmbientMaps`, `ambientCGConverges`, and `chainAmbientConv` now lift the
   same result to the original ambient members with target `U k`; the zero-tail
   identity is `chainPullback_zero`.

4. **Lane 4: D5 concrete completeness producer — complete.**
   The old per-stage-properness input is false for open stages.  The corrected
   `HasCompactBallCover` / `limitComplete_cover` consumer is checked, as is
   `tailSystem_compact`; the compact-cover API now correctly quantifies only
   finite `ENNReal` radii.  `half_ambient_le_tail` uses `lbl407` only at order
   zero.  Compact half-radius cores and their closed limit images are checked,
   and `exists_first_exit` supplies the generic first-exit point.  The next
   `incl_mem_coreInt`, `frontier_core_radius`, `pathELength_val_le`,
   `path_escape_core`, `mem_core_of_edist`, and `tailRangeExhausts` now prove
   that every finite Riemannian ball around any limit point lies in one shrunk
   stage range.  `tailLimitComplete` now performs the checked assembly
   `tailSystem_compact -> compactCover_of_step -> limitComplete_cover`; concrete
   D5 is complete.

5. **Lane 5: D6 final assembly -- complete.**
   `tailAmbientConv` and `tailLimitComplete` use the same `S`, `gTail`, and
   `hgTail`; `tailMemberConv` transfers the convergence to the original sequence
   through `repoint`, `unrepoint`, and `ofSubseq`; and
   `compactness_of_b1` assembles every `MetricCompactnessConclusion` field.

Current execution status: the historical D6 recount remains recorded as 3/3,
but its API blocker is resolved and is no longer an active stop condition.
`D6_PRO_PROMPT.md` is retained only as history.  The sole dependency preventing
the working endpoint from consuming the checked Step-D theorem is upstream:
the B/C lane has not yet produced `StepB1RawInput` from the endpoint's concrete
atom/weight/center data.  Resume from the live status in `B1_JOIN_HANDOFF.md`
and `B1_MIN_BRANCH_RULING.md`; do not duplicate that active B/C lane here.
The F2 book-facing supplier is also complete: `speed_le_of_c0` and
`data_image_ball` are public in `Distances.lean`, and `StepDDirected` consumes them.
There is no independent Step D/F producer left.  Do not edit D1--D6 again
unless the B/C producer exposes a genuine interface mismatch.

---

## 0. Producer map (what Step D consumes, and its current state)

| Book cite | Content | Lean producer | State |
|---|---|---|---|
| `lbl397` | approx isometry on a large ball (B1) | `StepB1ApproxIso.stepB1_of_raw` | conditional assembly green from `StepB1RawInput`; producer from real C-track inputs 0%; textbook endpoint reserved |
| `lbl372` | composition accumulation `e n ≤ C·Σδᵢ` (F6) | `ApproxIsometryCompHigher.comp_cov_accum` | green |
| `lbl367` | image-ball control `Φ(B(O,r)) ⊆ B(O',(1+ε)^{1/2}r)` (F2) | `Distances.lean`: `speed_le_of_c0` + `data_image_ball` over `image_ball_tangent` | green; book wrapper complete |
| `lbl404` | `C⁰→C^∞` composition-convergence ("apply Lemma 4.4 again") | `MapConvergenceComp.lean` (`MapCInfConvOnCompacts.comp` and moving-composition derivative convergence) | green |
| `lbl379–381` | direct-limit topology: compact-factors / σ-compact / T2 | `Geometry/Topology/DirectLimit.lean` (`SeqSystem`, `Lim`, `incl`, `isCompact_exists`, `sigmaCompact`, `t2Space`, `lift`) | green |
| `lbl332` | C^∞-CG convergence definition | `MetricCompactness.lean` (`MetricCGConvergenceData`, `PointedRiemannianCGConverges.ofRestrictPullback`, `MetricSourceData.ofRestrictPullback`) | green |
| — | per-member proper realization | `GoodCoveringOrdered.properMetricOn` (needs `MetricComplete` + `ConnectedSpace`) | green |

The remaining **critical-path gate** from outside Step D is `lbl397` (B1
assembly).  The old `lbl404` composition-convergence gate is closed in
`MapConvergenceComp.lean`.

---

## D1 — `lbl406`: the directed system of approximate isometries

**Book:** L1891–1957.  A subsequence `k_j` and maps
`Ψ_j : B(O_{k_j}, 2^j) → B(O_{k_{j+1}}, 2^{j+1})`, `Ψ_j(O) = O`, such that every
composition `Ψ_{j,ℓ} = Ψ_{j+ℓ-1} ∘ ⋯ ∘ Ψ_j` is an `(ε,p)`-approximate isometry
for `j > j₀(ε,p)`.

**Proof shape (book):** pick `C_j ≥ 1` increasing; recursively choose `k_{j+1}`
so `F_{k_j k_{j+1}; 2^j}` is a `(C_j⁻¹2⁻ʲ, j)`-approximate isometry (`lbl397`
existence at radius `2^j`, tolerance `C_j⁻¹2⁻ʲ`, order `j`); set
`Ψ_j := F_{k_j k_{j+1}; 2^j}`.  Accumulate with `lbl372`:
`Ψ_{r,ℓ}` is `(2^{1-r}, r)`-approx.  Ball containment `Ψ_r(B(O,2^r)) ⊆ B(O',2^{r+1})`
from `lbl367` since `(1+C_r⁻¹2⁻ʳ)^{1/2} ≤ 2`.

**Lean target (one declaration + a recursion helper):**
```
structure DirectedApproxSystem (X : PointedRiemannianSeq) where
  φ : ℕ → ℕ                       -- the subsequence k_j
  strictMono : StrictMono φ
  Psi : ∀ j, PartialDiffeomorph I I (X.obj (φ j)).M (X.obj (φ (j+1))).M ∞
  source_sub : ∀ j, closedBall (basepoint (φ j)) (2^j) ⊆ (Psi j).source
  maps_ball : ∀ j, (Psi j) '' closedBall (basepoint (φ j)) (2^j)
                     ⊆ closedBall (basepoint (φ (j+1))) (2^(j+1))
  base : ∀ j, Psi j (basepoint (φ j)) = basepoint (φ (j+1))
  comp_approx : ∀ ε > 0, ∀ p, ∃ j₀, ∀ j ≥ j₀, ∀ ℓ,
    Nonempty (BookApproxIsoPartialData (closedBall (basepoint (φ j)) (2^j)) ε p
      (psiComp j ℓ) (metric (φ j)) (metric (φ (j+ℓ))))
theorem exists_directedApproxSystem … : ⟸ stepB1_approxIso, comp_cov_accum, image_ball_tangent
```
`psiComp j ℓ` is the composition of partial diffeos with the domain-tracking
(`PartialDiffeomorph.trans` restricted to the ball; the `maps_ball` field is what
makes the composite's source contain the ball).  Composition of
`BookApproxIsoPartialData` at the data level is a NEW small lemma
(`partialData_comp`): F5/F6 give the tensor estimates; the partial bookkeeping
(source/image tracking through `trans`) is mechanical but must be its own brick
— do not inline it into the recursion.

**Bricks:**
- D1a `partialData_comp` — two-sided partial approx-iso data composes
  (`BookApproxIsoPartialData K … Phi` + `… (Phi''K) … Phi'` ⟹ `… K … (Phi.trans Phi')`),
  constants per F5 (`comp_cov_le`).  File: `C4/ApproxIsometryComp.lean` (extend).
- D1b `exists_directedApproxSystem` — the recursion (Nat.rec choosing `k_{j+1}`;
  the accumulation estimate `2^{1-r}` by `compEpsAccum`).  File: NEW
  `C4/StepDDirected.lean`.

**Acceptance:** builds green; `#print axioms` clean modulo the declared inputs
threaded from B1's hypotheses; no new `sorry`.

**Gate:** consumes `stepB1_approxIso` — until B1's assembly lands, D1b can be
stated and proved AGAINST the B1 statement (it is a theorem-consumer, and B1 is
`sorry`-backed), so D1 work may start now; its axiom report will show B1's
`sorryAx` until the B-track closes.  State this honestly in the file docstring.

## D2 — `lbl407`: limiting metrics on the balls

**Book:** L1961–2006.  Pull back: `{Ψ_{j,ℓ}* g_{j+ℓ}}_ℓ` are uniformly bounded
with all derivatives on `B(O_j, 2^j)` (because `Ψ_{j,ℓ}` are `(ε,p)`-approx
isometries uniformly in `ℓ`), so a diagonal subsequence converges to `g_{j,∞}`
on each ball, with the uniform closeness
`|∇^r_{g_{j,∞}}(Ψ*⋯*g_{j+ℓ} − g_{j,∞})| ≤ ε` for `r ≤ p`, `j ≥ j₀(ε,p)`.
Consequence (L1996–2006): each `Ψ_j` is an **isometry** `g_{j,∞} → g_{j+1,∞}`
(two-term telescoping estimate).

**Lean route:** the open-ball realization is complete in
`StepDLimitMetrics.lean`.  For metric extraction, first try the existing
intrinsic endpoint `ComponentConvAssembly.metricPreconvInf` on each fixed
stage; it already packages the all-orders diagonal once `hbdd` and `hlow` are
proved.  Use `MapConvergenceComp.MapCInfConvOnCompacts.comp` for the later
composition/cocycle passage — NO new metric-AA.

**Bricks:**
- D2a0 open-ball realization — **DONE, verified.** `ballOpen`, `ballSystem`,
  `ballSystemOfData`, and `directedBallSystem` connect the eventual D1 maps to
  `SmoothSeqSystem` through a single tail shift.
- D2a `pullback_seq_bounded` — define the smooth Riemannian pullback metrics on
  a fixed `ballOpen`, then prove `metricPreconvInf`'s `hbdd` and `hlow` from
  `comp_approx`.  **Direct tail bricks DONE:** `ballPullbackMetric`,
  `ballPullback_covNorm`, `ballPullback_cov_le`, `ballPullback_lower/upper`, and
  `ballPullback_zero_le`.  **Prefix-tail geometry DONE:**
  `chainComp_add_apply`, `chainCompAssoc(_apply/_eq)`, `ballTransSource`,
  `nestedBallPullback`, `ballPullback_trans`, `ballPullback_congr`,
  `prefixTail_cov_le`, `chainPrefix_cov_le`, and `chain_image_ball`.
  `metricComp_iter_refs` is focused green.  **Live sub-brick:** verify
  `engine_input_refs`, then carry this per-order-reference chart input through
  the extraction/limit assembly.  Do not strengthen D1 to all orders at fixed
  `j`, and do not misuse `lemma45_corII` as a generic reference-change theorem.
- D2b `exists_limit_metrics` — the diagonal extraction + the `lbl407` uniform
  closeness estimate.  ⟸ D2a, `exists_cInf_subseq_on`, `DiagonalSubseq`.
- D2c `psi_isometry_limit` — `Ψ_j* g_{j+1,∞} = g_{j,∞}` on the ball (telescoping
  + limit-passing; equality, not just closeness).
- D2d re-index bookkeeping — the book re-indexes twice (after `lbl406` and after
  `lbl407`).  Fold both into the `φ` of a single final
  `DirectedApproxSystem`-with-limits structure; do NOT model the re-indexing as
  separate layers.

**Gate status:** the former `lbl404` gate is green in
`MapConvergenceComp.lean`.  The live D2 frontier is now the pullback-metric
realization plus its intrinsic derivative/lower bounds.

## D3 — `lbl408`: the limit manifold (independent of D1/D2 — START HERE)

**Book:** L2008–2046.  `M∞ := dirlim B(O_k, 2^k)` along the `Ψ_k` (open
embeddings); Hausdorff by `lbl381`; charts `H^α_{∞,k} := I_k ∘ H_k^α` with
transitions (`lbl409`) `(H^β_ℓ)⁻¹ ∘ Ψ_{k,r} ∘ H^α_k` smooth ⇒ `C^∞` structure;
`Ψ` isometries ⇒ a metric `g∞` with `I_k* g∞ = g_{k,∞}`.

This is the genuinely new infrastructure (Mathlib has none of it), and it is
**abstract**: nothing here needs B1/C/lbl404.  Build it against an abstract
`SeqSystem` whose maps are smooth open embeddings of manifolds, in
`Geometry/Topology/` (Analysis-promotable), NOT in C4.

**Bricks (all in NEW `Geometry/Topology/DirectLimitManifold.lean` unless said):**
- D3a `SmoothSeqSystem` — a `SeqSystem` on manifold factors whose maps are
  `ContMDiff` open embeddings.  Charted structure on `Lim`: charts through
  `incl ∘ chart` — for `x = incl k a`, use `(chartAt a) ∘ (incl k).invFun` as a
  `PartialHomeomorph (Lim) H` (source `incl k '' (chartAt a).source`, open by
  `incl_isOpenMap`).  Deliverable: `instᐧChartedSpace : ChartedSpace H S.Lim`.
- D3b transition smoothness — two such charts differ by
  `chart_ℓ ∘ (S.F k ℓ …) ∘ chart_k⁻¹` (= book `lbl409`), smooth since `S.F` is;
  deliverable `IsManifold I ∞ S.Lim`.  (This is `HasGroupoid` for
  `contDiffGroupoid ∞ I` — mirror `TopologicalSpace.Opens.instHasGroupoid`.)
- D3c second-countability / metrizability glue — `DirectLimit.md` records the
  deferral; needed for `SigmaCompactSpace` interplay and the
  `t2TangentBundle` field of `PointedRiemannianManifold`.  Route:
  `Manifold.metrizableSpace` needs σ-compact + T2 + locally-euclidean — all
  present; `T2Space (TangentBundle I S.Lim)` then via the standard
  `t2TangentBundle`-producer used by the port (grep `t2TangentBundle` for the
  existing recipe — do not hand-roll).
- D3d metric transport — given per-factor metrics `g_k` with
  `(S.F k (k+1))* g_{k+1} = g_k` (D2c's conclusion shape), a
  `SmoothRiemannianMetric I S.Lim` with `incl_k* g∞ = g_k`.  Pointwise: define
  `g∞` at `incl k a` by pushing `g_k` forward along the open embedding (the
  cocycle makes it stage-independent); smoothness is local, via the D3a charts.
  This is the heaviest D3 brick — bundle-valued transport along an open
  embedding.  Search `Geometry/Metric/Pullback.lean` FIRST: pullback along a
  diffeo-onto-image exists in some form (`Diffeomorph.pullbackInner`,
  `SmoothMetricFromCoeff.lean` "shared with Ch4 Thm 3.9" note) — adapt, do not
  duplicate.
- D3e the pointed bundle — assemble the
  `PointedRiemannianManifold` (`limit` field of the conclusion): carrier
  `S.Lim`, basepoint `incl 0 O_0`, fields from D3a–D3d.  File: NEW
  `C4/StepDLimit.lean` (this one IS C4-specific).

**Acceptance:** each brick green + axiom-clean standalone; D3a–D3d carry NO
Step A/B/C imports (promotability test).

## D4 — convergence of the sequence to the limit

**Book:** L2048–2085.  For compact `K ⊆ M∞`: `K ⊆ I_k[B(O_k,2^k)]` eventually
(`lbl379` = `isCompact_exists` ✓); the comparison maps of Definition `lbl332`
are `Φ k := I_k⁻¹` on those images; the `C^p` smallness
`sup_K |∇^α(g∞ − (I_k⁻¹)* g_k)|_{g∞} < ε` reduces, by pulling back along `I_k`,
to exactly the `lbl407` estimate `|∇^α_{g_{k,∞}}(g_{k,∞} − g_k)|`.

**Lean route:** this is precisely the shape
`PointedRiemannianCGConverges.ofRestrictPullback` was built for
(`MetricCompactness.lean`): supply `Φ` (sources `I_k[B]`, targets the balls),
σ-compactness of sources/targets, the reference metrics, and the
`derivNormSupOn < ε` field.  ONE bridge lemma converts the `lbl407` chart-level
estimate into `derivNormSupOn` (this is the D-side end of the metric-side/
map-side "parallel + bridged" ruling — the bridge lives at D4, nowhere else).

**Bricks:**
- D4a `maps` — package `I_k` inverses as `PointedRiemannianCGMaps` (sources,
  targets, smoothness of both directions from D3a/D3b, basepoint condition).
- D4b `conv_bridge` — `lbl407`-estimate ⟹ `derivNormSupOn K p < ε` for the
  restricted pullback data.  ⟸ D2b/D2c, D3d (`incl_k* g∞ = g_{k,∞}`).
- D4c `convergence` — instantiate `ofRestrictPullback`.  File: `C4/StepDLimit.lean`.

## D5 — completeness of the limit

**Book:** L2087–2100.  Closed geodesic balls of `g∞` are compact (each sits in
some `I_k[B]`, pulls back closed+bounded, `g_k` complete ⇒ compact), and
compact-closed-balls ⇒ complete.

**Lean route:** target the `MetricComplete` predicate
(`PointedRiemannian.lean:74`, completeness of
`EMetricSpace.ofRiemannianMetric`).  Route through the realized proper metric:
closed-balls-compact gives `ProperSpace`, and Mathlib's
`ProperSpace → CompleteSpace` (`ProperSpace.toCompleteSpace`-shape) finishes.
The `hcomplete`/`hconn` hypotheses of the endpoint supply per-member
completeness; connectedness of `Lim` follows from connectedness of the balls +
monotone union (small lemma, `DirectLimit`-level).

**Brick:** D5a `limit_complete` — `MetricComplete limit`.  ⟸ `isCompact_exists`,
D3e, per-member `ProperMetricOn` (`properMetricOn`).

## D6 — endpoint wiring

Fill `MetricCompactnessInputs.metricCompactness`: `subseq` = the composed
subsequence of Step A's diagonal, D1's `φ`, and D2's diagonal; `limit` = D3e;
`limit_complete` = D5a; `maps` = D4a; `convergence` = D4c.  Discharge the
construction-stage scale inputs (`Item3RadiusInput`, `Item3GpScaleInput`,
`SigmaScaleField`) from the bundle here, by choosing `D` large against
`normalBounds`' uniform radius — ONE uniformity lemma per input, stated in
`C4/StepAInputs.lean`-adjacent files (see `MetricCompactnessInputs.lean` module
docstring).  File: `C4/StepDAssembly.lean`.

---

## Execution order and parallelism

1. **Now, gate-free:** D3a → D3b → D3c → D3d → D3e (the new-infrastructure lane;
   largest and riskiest — start first).  D1a is also gate-free.
2. **After/with B1:** D1b (may be written against the B1 statement earlier).
3. **After lbl404 engine:** D2a → D2b → D2c → D2d.
4. **Then:** D4a → D4b → D4c → D5a → D6.

Risk register (honest): D3d (metric transport to the limit) is the most likely
place for a real wall — bundle-language transport along open embeddings has no
precedent in-tree at manifold level (only chart-level pullbacks); budget a
design pass before implementation.  D1a's partial-composition bookkeeping is
mechanical but fiddly (PartialDiffeomorph.trans source arithmetic).  Everything
else is assembly against existing engines.

## Status log

- 2026-07-09 (D4 ambient continuation, new route recount 0/3): the prior
  carrier-level blocker is closed.  `PartialDiffeomorph.liftTargetOpen` gives a
  smooth ambient lift with target exactly the open set and
  `liftOpen_mfderiv` gives its differential readout.  `chainPullback_zero`,
  `chainAmbientSeq`, `chainAmbientMaps`, `ambientCGConverges`, and
  `chainAmbientConv` are checked.  The comparison maps now land in the original
  ambient manifolds and consume the existing `lbl407` estimate without a new
  estimate.  Next target: D6 reindex/assembly.  Route errors: **0/3**.

- 2026-07-09 (D4 continuation, route count 3/3): D2d and the source-domain D4
  bridge are checked. `SmoothSeqSystem.MetricCocycle.ofSucc` and
  `chainMetricCocycle` extend adjacent limit compatibility to the full cocycle;
  `tail_derivSup_lt` gives the compact supremum estimate;
  `limitCGConverges` packages direct-limit convergence; and
  `chainCGConverges` instantiates it from `lbl407`.  Route error #3 is a
  carrier-level packaging mistake: `chainCGConverges` targets the open-ball
  subtype sequence `U n`, while `MetricCompactnessConclusion X` requires maps
  into the original members `X.obj (subseq n).M`.  The estimates are valid, but
  this result cannot fill D6.  Smallest repair: a smooth open-embedding lift of
  `inclPartialDiffeo`, an ambient `PointedRiemannianCGMaps` package, and the
  zero-tail restriction identity.  This is a routine-to-medium missing API, not
  a mathematical obstruction.  Stop condition reached: **3/3 route errors**.

- 2026-07-09 (D2 prefix-tail continuation, route count 2/3): the geometric
  prefix-tail path is now checked end to end through `chainPrefix_cov_le` and
  `chain_image_ball`.  Route error #1 was treating exact pullback invariance as
  sufficient for the old `metricPreconvInf.hbdd`; its reference metric depends
  on the requested order.  Route error #2 was treating `lemma45_corII` as a
  generic reference-change estimate; it requires the background metric tower
  to be small under the same `eps <= 1`.  The third route is viable rather than
  failed: `metricComp_iter_refs` converts per-order references directly to
  uniform chart-component derivative bounds.  That route is now complete:
  `engine_input_refs`, `metricPreconv_refs`, `metricCInf_refs`,
  `chainPullback_bdd`, `exists_chain_limit`, and `exists_chain_data` all check,
  with targeted producer builds refreshed.  D2a is closed.  Route failures
  remain **2/3**; the next target is D2b's common diagonal and `lbl407` estimate.

- 2026-07-08 (D6 input threading): `MetricCompactnessInputs` now has checked
  wrappers for the endpoint-hypothesis Step A entrypoint.  `properMetrics`
  builds the per-member `ProperMetricOn` family from `SeqMetricComplete` and
  connectedness; `stepA_net` produces the stable `NetLimitData` plus item-5
  intersection bound directly from the bundle and endpoint hypotheses; and
  `subseq` reindexes the full bundle after Step A/D diagonal subsequences.
  `StepBInputs` supplies the missing `subseq` wrappers for `normalBounds` and
  `expInvDeriv`.  Verification passed for focused checks and targeted module
  builds, all with no global Lake lock.  This is D6 wiring only; the D6
  endpoint theorem remains unstated/unproved.

- 2026-07-08 (D6 endpoint hypothesis wrappers): `SeqMetricComplete.subseq` and
  `SeqBoundedGeometry.subseq` are now checked and built in their native
  endpoint-input files.  Together with the existing `BaseInjBound.subseq`, the
  endpoint hypotheses can now be carried through composed Step A/D
  subsequences without manual field projections.  Next concrete target:
  compose these endpoint wrappers with `MetricCompactnessInputs.subseq` in the
  D6 assembly layer, then feed `properMetrics` and `stepA_net`.
- 2026-07-08 (D6 Step A net after subsequence): `MetricCompactnessInputs` now
  has checked `stepA_net_subseq`, a direct consumer theorem for the Step A net
  package after reindexing by a subsequence.  A product-shaped all-hypotheses
  helper was tried and removed because ordinary `Prod` is the wrong wrapper
  for `Prop` endpoint hypotheses; the direct consumer theorem is the smaller
  usable API.  Local D6 input-threading for Step A nets after diagonal
  subsequences is now done.  Next D6 work is no longer a local endpoint-input
  adapter: it needs the actual D1/D2/D3/D4/D5 producers to exist before the
  endpoint `metricCompactness` `sorry` can be replaced.
- 2026-07-08 (D1b radius bookkeeping micro-bridge): `StepDDirected` now has
  checked `ball_subset_eball_ofReal`, `closedEBall_ofReal_subset_ball`, and
  `data_image_metric_ball`, plus `two_pow_lt_openRad` for the strict radius
  margin `2^j < 2^j * (1 + (1/2)^(l+1))`.  These discharge the generic
  metric/emetric set-conversion piece of the remaining open-ball accumulation
  step and expose a direct metric-ball image-control theorem.  Also removed the stale duplicate
  `ExpInverseDerivBoundInput.subseq` from `StepCTransitionRefine`; the canonical
  subsequence wrapper is `StepBInputs.ExpInverseDerivBoundInput.subseq`.
  Focused checks passed for both files.  Targeted refreshes passed for the
  stale/missing upstream modules `StepCTransitionRefine`, `StepCAveraging`,
  `AllTimesBounds`, `Evolution.Connection`, `MetricCovDerivPullback`, and
  `Evolution.BernsteinShiHigher`.
  `StepDDirected` targeted module refresh timed out twice while replaying wide
  dependencies, so its current verification evidence is the focused file check.
  Next D1b target: use `data_image_metric_ball` to state/prove the specific
  image inclusion `chainComp Ψ j l '' ball(R_l) ⊆ ball(O_{σ(j+l)}, 2^{j+l+1})`
  needed before `partialData_comp`.

- 2026-07-08 (D1b composition-domain package): `StepDDirected` now has checked
  `chainComp_base`, midpoint-radius helpers (`midRad`, `openRad_next_lt_mid`,
  `midRad_lt_openRad`), and image-radius bounds (`imageRad_lt_step`,
  `imageMid_lt_step`).  In the live `exists_directedApprox` succ branch, the
  accumulated map's image inclusion is proved with the correct intermediate
  radius `r2`, and `partialData_comp` instantiates successfully for
  `U1 = ball(r2)`, `K2 = ball(2^(j+l+1))`, and
  `K = closedBall(R_{l+1})`.  Focused `StepDDirected.lean` check passed with the
  same single endpoint `sorry`.  Next D1b target: strengthen the `hacc`
  induction invariant with a quantitative geometric-ledger bound; the current
  invariant `0<a ∧ a≤ε ∧ a≤1/2` is too weak to choose the next `ε''` satisfying
  both `partialData_comp` lower bounds while keeping `ε''≤ε`.

- 2026-07-08 (D1b ledger invariant strengthened): the live `hacc` invariant in
  `StepDDirected` now carries `B = max C 2` outside the induction, records the
  quantitative budget
  `a_l <= 2 * B * sum_{i<=l} (1/2)^(j+i+1)`, and uses
  `geomTailBudget (ε / (2 * B))` for the eventual threshold.  It also carries
  both bracketings: left-fold `chainComp Ψ j l` data and right-fold
  `chainComp' Ψ l j (j+l) rfl` data.  Added checked helpers
  `PreApproxIsoDataOn.congr_eq`, `BookApproxIsoPartialData.ofParts`, and
  `chainComp_eq_right` so the next step can transport the reverse field from
  the right-fold ledger and assemble it with the left-fold forward field.
  Focused `StepDDirected.lean` check passed; endpoint theorem remains one
  `sorry`.  Next D1b target: use those helpers in the succ branch, then close
  the scalar bounds for the chosen next tolerance `a_{l+1}`.

- 2026-07-08 (D1b reverse transport + next tolerance): `StepDDirected` now has
  checked `symm_eventuallyEq_on_image`, proving inverse-germ equality on the
  image of an open source zone when two partial diffeomorphisms agree there.
  In the live succ branch, right-fold reverse data is transported to the
  left-fold reverse map (`Drev_left`), reassembled with the left-fold forward
  field via `BookApproxIsoPartialData.ofParts` (`D1parts`), and consumed by
  `partialData_comp`.  Added `nextTol` plus its two lower-bound projections and
  positivity lemma; the branch now defines `aNext = nextTol a δ B` and checks
  the two `partialData_comp` lower-bound hypotheses.  Focused
  `StepDDirected.lean` check passed; endpoint theorem remains one `sorry`.
  Superseded next-target note: a later audit showed that proving the remaining
  scalar obligations is not a valid standalone target while the succ branch
  still consumes the full two-sided `partialData_comp` on the peel-last
  bracketing.

- 2026-07-08 (D1b scalar target audit): the live succ branch currently
  transports right-fold reverse data to the left-fold map and then calls full
  `partialData_comp`.  That forces the reverse-side lower bound
  `δ/(1-δ) + a * B <= ε''`, multiplying the accumulated tolerance by
  `B = max C 2` at each peel-last step.  Therefore the recorded target
  `aNext < 1` plus
  `aNext <= 2 * B * sum_{i<=l+1} (1/2)^(j+i+1)` is not a scalar cleanup; it
  repeats the old linear-budget failure from codas 52-54.  Current route
  status: direct scalar proof failed by recurrence shape; increasing `ε''`
  under the full two-sided theorem fails the endpoint budget; the viable next
  D1b target is to expose/derive half-composition producers from
  `partialData_comp`'s proof organs, run the forward half on peel-last
  `chainComp`, run the reverse half on peel-first `chainComp'`, and assemble
  the final two-sided data with `BookApproxIsoPartialData.ofParts`.

- 2026-07-08 (D1b half-composition API): `PullbackField` now exposes
  `compDataFwd` and `compDataRev`, the forward-only and reverse-only data
  producers needed by the two-bracketing D1b recursion.  Their signatures are
  checked, and the focused `PullbackField.lean` check passed with exactly these
  two new `sorry` frontiers.  Next D1b target: refresh the `PullbackField`
  module if downstream `.olean` staleness appears, then patch
  `StepDDirected`'s succ branch to consume `compDataFwd` on peel-last
  `chainComp` and `compDataRev` on peel-first `chainComp'`, assemble with
  `BookApproxIsoPartialData.ofParts`, and only then close the now-valid scalar
  budget for the shared next tolerance.

- 2026-07-08 (D1b shifted-tail audit): downstream inspection found that the
  current fixed-start `hacc` invariant is still too weak for the new reverse
  half.  `chainComp'_snoc` lets the right fold tail-peel at the same start `j`,
  but using that shape with `compDataRev` again puts the accumulated tolerance
  in the `* B` slot.  The good book bound requires the genuine peel-first
  shape `Ψ j` followed by the shifted tail `chainComp' Ψ l (j+1)`, so the
  recursion needs accumulated data for start `j+1` (and, in the induction,
  generally for shifted starts), not only for fixed `j`.  Route status: local
  replacement of the full `partialData_comp` call is a third route failure for
  the current invariant.  Next target: strengthen `hacc` to a start-indexed
  ledger over all starts `s >= j` (with the same open-radius/tolerance budget),
  then consume `compDataFwd` on peel-last and `compDataRev` on the shifted
  peel-first tail.

- 2026-07-05: plan written.  No Step D Lean files exist yet; `DirectLimit.lean`
  (topology layer) is the only landed substrate.  Step D completion: **0%**.
- 2026-07-07: **D3a + D3b + D3c-part DONE** in NEW `Geometry/Topology/DirectLimitManifold.lean`
  (full `lake build` green, axiom-clean `[propext, Classical.choice, Quot.sound]`, NO Step A/B/C
  imports — promotability test passes).  Landed: `SeqSystem.instChartedSpaceLim`
  (`ChartedSpace H S.Lim`, D3a); the `SmoothSeqSystem I A` structure (fields `contMDiff_F` +
  `contMDiffOn_invFun_F` = the `Ψ_k` are `C^∞` diffeos onto open images); the D3b crux
  `transitionHomeo_contMDiffOn` (`lbl409`, factor transition `C^∞` via `invFun(F_{ℓ≤m})∘F_{k≤m}`);
  `SmoothSeqSystem.instIsManifoldLim` (`IsManifold I ∞ S.Lim`, D3b) via `isManifold_of_contDiffOn`
  + `limChart_symm_trans` + the model-space bridge `modelSpace_contDiffOn`; and the D3c wrappers
  `instSigmaCompactSpaceLim` / `instT2SpaceLim`.  See `DirectLimitManifold.md`.
  **REMAINING for D3 — two genuine bridges (no Mathlib producer), both flagged by this plan:**
  (a) `T2Space (TangentBundle I S.Lim)` (rest of D3c): the whole project carries this as a
  HYPOTHESIS (`Exponential/Defs.lean:210` `inferInstance` retrieves an assumption; there is NO
  `t2TangentBundle` producer — the plan's assumption of one was wrong).  Needs a "total space of a
  fibre bundle over a T2 base with T2 fibre is T2" bridge — a real topology sub-project.
  (b) D3d metric transport — unchanged, the flagged heaviest wall.
  D3e (`StepDLimit.lean`) is blocked ONLY on (a) + (b); its `charted`/`smooth`/`sigmaCompact`/`t2`/
  basepoint fields are all ready.  Step D completion: **~15%** (the two structural pillars D3a/D3b
  and the σ-compact/T2 glue are the largest new-infrastructure pieces; metric transport + T2-tangent
  + assembly remain).
- 2026-07-07 (2nd session): **D3c COMPLETED + D3e ASSEMBLED.**  (a) closed: NEW
  `Geometry/Topology/FiberBundleT2.lean` `FiberBundle.t2Space_totalSpace` (general topology,
  ~35 lines: `[T2Space B] [T2Space F] [FiberBundle F E] ⟹ T2Space (TotalSpace F E)`) + corollary
  instance `SmoothSeqSystem.instT2SpaceTangentBundleLim` (fires automatically, `IsManifold I 1`
  lowered from `∞`).  Also `SmoothSeqSystem.contMDiff_incl` (the stage inclusion is `C^∞` — a
  D3d/D4 prerequisite).  D3e: NEW `C4/StepDLimit.lean` `limitPointed` assembles the
  `PointedRiemannianManifold` bundle sorry-free, ALL structure fields auto-synthesized from D3a–D3c,
  conditional only on the `ginf` metric input.  Full `lake build` green (2707 jobs), axiom-clean.
  **ONLY REMAINING D3 FRONTIER = D3d metric transport** (`SmoothRiemannianMetric I S.Lim`,
  `incl_k* g∞ = g_k`).  Per the plan's ruling, the minimal missing bridge is reported (NOT built as
  a broad framework): pushforward of a metric along the open embedding `incl k` via
  `(mfderiv (incl k))⁻¹`, cocycle well-defined, smoothness in the `limChart` charts — a multi-lemma
  partial analogue of `Diffeomorph.pullbackMetric`, deferred to a dedicated session.  Step D
  completion: **~25%** (D3a/b/c done, D3e assembled; D3d metric + D4/D5/D6 remain).
- 2026-07-07 (3rd session): **D3d DONE — D3 COMPLETE (D3a–D3e all green, axiom-clean, zero
  warnings, full `lake build` 2738 jobs).**  `SmoothSeqSystem.limitMetric` (in
  `DirectLimitManifold.lean` §MetricTransport): per-factor metrics + isometry cocycle
  (`MetricCocycle`, D2c's conclusion shape, honest-input docstring) ⟹
  `SmoothRiemannianMetric I S.Lim` with `limitMetric_pullback : (incl k)^* g∞ = g k`.  Route: fiber
  form = pullback along the smooth local inverse `Function.invFun (incl k)`
  (`contMDiffAt_invIncl`; NO derivative inverses anywhere); stage-independence by the FORWARD
  factorization `F ∘ (incl k)⁻¹ =ᶠ (incl m)⁻¹` + `EventuallyEq.mfderiv_eq` + cocycle
  (`stageInner_mono`/`_congr`); base-point defeq crossings by subst-based `inner_base_eq`/
  `mfd_base_eq` helpers; the `contMDiff` field (the flagged wall) dissolved by the PUBLIC
  test-section engine `cotangentCov_clmSection_smooth_aux` (`Bundle/ClmSectionSmooth.lean`) +
  `ContMDiffOn.contMDiffOn_tangentMapWithin` + At-version `clm_bundle_apply₂` +
  `Bundle.contMDiffAt_section`.  D3e endpoint `C4/StepDLimit.lean` `limitPointedCoc` (metrics +
  cocycle in → pointed bundle out) wired.  See `DirectLimitManifold.md` + `StepDLimit.md`.
  Step D completion: **~35%** (D3 done = the largest new-infrastructure block; D1 gate-free next,
  D2 gated on `lbl404`, D4/D5/D6 assembly ahead).
- 2026-07-07 (4th session): **D4a DONE + connectedness + D1a/D5a scouted.**  Landed (all green,
  axiom-clean, `lake build` 3790 jobs): `SeqSystem.instPreconnectedLim`/`instConnectedSpaceLim`
  (monotone-union connectedness — the endpoint `hconn` input); `SmoothSeqSystem.inclPartialDiffeo`
  (`(incl k)⁻¹` as `PartialDiffeomorph Lim (A k)`, D3-smoothness packaged) + `invIncl_incl_le`;
  `C4/StepDLimit.lean` §StepD4a: `factorPointed`/`factorSeq`, `rangeExhausts`
  (`ExhaustsByOpen` of stage ranges = `lbl379`), **`limitCGMaps` = the D4a comparison-map package**
  (`PointedRiemannianCGMaps (factorSeq …) (limitPointedCoc …) id`).  Instance lesson recorded in
  `StepDLimit.md` (InnerProductSpace-vs-NormedSpace spine freeze).  **D1a scouted — heavier than
  planned**: the composite `BookApproxIsoPartialData` needs (i) a GLOBAL smooth extension of the
  K-only-smooth composite pullback field (`Tensor0SField` is `ContMDiffSection`; needs a
  bump-extension producer, K compact ⊆ open source — `Metric/BumpExtend`/`ConvexCombination`
  candidates) and (ii) partial-map covariant-norm naturality `|∇^k_{Φ^*h}(Φ^*δ)|_{Φ^*h} =
  |∇^k_h δ|_h ∘ Φ` (only same-domain F4/F5 and GLOBAL-diffeo (Ch3 WindowDataPullback) forms
  exist).  **D5a scouted — route pinned** (pointwise isometry → `pathELength` invariance →
  `edist ≤` via Mathlib's ℝ-line `exists_lt_of_riemannianEDist_lt`; reverse inclusion needs a
  metric-exhaustion honest input discharged at D6).  Step D completion: **~40%**.
- 2026-07-07 (4th session, cont.): **D5 distance cornerstones DONE** (`C4/StepDLimit.lean`
  §StepD5, green, axiom-clean, `lake build` 3790 jobs): `enorm_mfd_incl` (pointwise isometry of
  the stage inclusions under the two `RiemannianBundle` structures — `TangentNormDiamond` idiom +
  `limitMetric_pullback`), `pathELength_incl` (stage `C¹` paths push to limit paths of equal
  length), `edist_incl_le` (stage inclusions are 1-Lipschitz for `riemannianEDist`, via Mathlib's
  ℝ-line `exists_lt_of_riemannianEDist_lt`), **and `edist_invIncl_le`** — the REVERSE comparison
  assembled: ball-in-range hypothesis + `edist x y < r` ⟹ stage `edist ≤ r` (limit almost-geodesics
  stay in the ball by partial-length domination, pull back at equal length via
  `pathELength_invIncl`).  D5a remaining = the metric-exhaustion honest input
  (balls ⊆ stage ranges, D6-discharged) + the properness/completeness assembly on the realized
  `riemMetricSpace` layer.  Step D completion: **~45%** (D3 done, D4a done, D5 distance layer
  done; D1/D2 engines + D4b/c + D5a assembly + D6 remain).  LATER SAME SESSION:
  **`isCompact_cball_lim` DONE** — the D5a compactness core (metric-exhaustion honest input +
  stage-ball compactness ⟹ closed limit `riemannianEDist`-balls of finite radius compact;
  closedness via `EMetricSpace.ofRiemannianMetric`, where `edist = riemannianEDist` by `rfl`).
  D5a remaining = ONLY the `ProperSpace`/`CompleteSpace` endpoint glue on the realized
  `riemMetricSpace` layer.  AND THE CONDITIONAL GLUE LANDED: **`limitComplete` DONE AS AN
  ABSTRACT CONSUMER, NOT CONCRETE D5**
  (`MetricComplete (limitPointedCoc …)` from the exhaustion + stage-ball-compactness honest
  inputs; `EMetricSpace.toMetricSpace` uniformity-defeq + `ProperSpace.of_isCompact_closedBall_of_le`
  + ascribed `complete_of_proper`; needs `[NeZero (finrank ℝ E)]` + `[I.Boundaryless]` +
  `[∀ k, PreconnectedSpace (A k)]`).  Retrospective correction (2026-07-09): the actual open
  stages do not satisfy the assumed stage-ball compactness, so concrete D5 still needs the
  metric-exhaustion/compact-cover route recorded in the active status above.  The old ~55%
  completion claim is withdrawn.  **D1a UNBLOCK FOUND:** the bump-extension engine for the
  composite pullback field already EXISTS — `Geometry/Metric/BumpExtend.lean`
  `SmoothRiemannianMetric.bumpExtendOpen` (partial metric on an open `U` + bump ⟹ total smooth
  metric agreeing with the partial one where `χ = 1`, with the `extZeroForm`/`bumpForm`/chart-frame
  coefficient machinery).  D1a gap (i) is an ADAPTATION of this engine (inner-family ↔
  `Tensor0SField 2` bridge), not a new build; gap (ii) (partial-map cov-norm naturality) remains
  the real wall.
- 2026-07-07 (4th session, final): **D1a-(i) design refined to components.**  The zero-extension
  half is FREE — Mathlib's `ContMDiffOn.smul_section_of_tsupport`
  (`VectorBundle/SmoothSection.lean:187`, general vector bundles: `ψ` `C^n`-on-open-`u` ⊇
  `tsupport ψ` + section `C^n`-on-`u` ⟹ `ψ • s` globally `C^n`) + a compact-in-open smooth bump
  `χ ≡ 1` on `K`, `tsupport χ ⊆ Φ.source` (needs `hK : IsCompact K` — honest, the book's `K` are
  closed balls).  Target constructor: `exists_pullbackField (hK) (Φ : PartialDiffeomorph)
  (hKs : K ⊆ Φ.source) (T : Tensor0SField 2 on N) : ∃ P global, ∀ x ∈ K ∀ v, P x v =
  T (Φ x) (dΦ ∘ v)`, with `P := χ • (pointwise pullback)`.  The ONE remaining sub-gap for (i):
  `ContMDiffOn`-on-`Φ.source` of the pointwise-pullback section `x ↦ ⟨x, (precomp dΦ_x) ∘
  (T (Φ x)) ∘ dΦ_x⟩` — a fiberwise CONJUGATION by `mfderiv Φ` (the D3d `hg'` pattern covers
  `x ↦ ⟨Φ x, T (Φ x)⟩`; the two `dΦ` slots need a `clm_bundle`-family conjugation or the
  test-section engine re-localized).  Route candidates: (α) per-point
  `Bundle.contMDiffAt_section` + `clm_bundle_apply₂`-At with test sections (the shape of the D3d
  `limitMetric.contMDiff` proof); (β) `tangentMapWithin` into the Hom-bundle via
  `ContinuousLinearMap.inCoordinates`.  Start with (α).  Gap (ii) (partial-map cov-norm
  naturality `|∇^k_{Φ^*h}(Φ^*δ)|_{Φ^*h} = |∇^k_h δ|_h ∘ Φ`) is untouched and remains the D1a wall.
- 2026-07-07 (4th session, coda): **D1a-(i) LANDED** in `C4/ApproxIsometryComp.lean` (green,
  `lake build` 3802 jobs): `exists_bump_one_on` (compact-in-open smooth bump, `≡1` on `K`,
  `tsupport ⊆ U`; shrink + `exists_contMDiffMap_one_nhds_of_subset_interior`, whose `n : ℕ∞`
  NOT `WithTop ℕ∞`) and **`exists_pullbackInner`** (`Φ : PartialDiffeomorph`, `K` compact ⊆
  `Φ.source`, `h` metric on `N` ⟹ ∃ globally-smooth bilinear family `P` on `M` with
  `P x v w = h.inner (Φ x) (dΦ v) (dΦ w)` on `K`).  Proof = `χ • (conjugation form)` +
  test-section engine with per-point split (`x ∈ Φ.source`: the D3d `limitMetric.contMDiff`
  assembly with `tangentMapWithin` on the source; `x ∉ tsupport χ`: locally zero via
  `image_eq_zero_of_notMem_tsupport`).  Remaining for D1a: the `Tensor0SField 2`-form bridge
  (if `PreApproxIsoDataOn.pullback` needs the tensor-bundle-typed field rather than the
  inner-family — check `PullbackMetricTensorData`'s fiber form first), the composite
  `partialData_comp` bookkeeping, and gap (ii) — the partial-map cov-norm naturality (the wall).
- 2026-07-07 (4th session, coda 2): **`pullInner_pos` landed** (ApproxIsometryComp §PullbackField,
  green 3802 jobs): on `Φ.source` the pulled-back quadratic form is positive definite — proof
  self-contained via `Φ.symm ∘ Φ =ᶠ id` + `EventuallyEq.mfderiv_eq` + `mfderiv_comp` (AVOID
  `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv` in `set`-form: its elaboration leaves
  metavariable sorries; also `PartialDiffeomorph.isLocalDiffeomorphAt` has EXPLICIT I J n; and
  this Mathlib's `ContMDiffAt.mdifferentiableAt` takes `n ≠ 0` here).  D1a-(i) now has THREE of
  four components (bump, smooth pullback family `exists_pullbackInner`, source-positivity);
  remaining for (i): package the convex combination `χ • pull + (1−χ) • g` as a
  `SmoothRiemannianMetric` (symm trivial, pos = `pullInner_pos` + convexity, isVonNBounded =
  convex combination, contMDiff = the engine again on the sum) and feed
  `RiemannianMetric_gen.to02Tensor_gen` (whose proof consumes ONLY inner+contMDiff; its private
  `to02Tensor_eCLM/uCLM/trivialization_eq` block Metric.lean-external reuse — hence the
  convex-combination route rather than a general bilin→tensor bridge).  Then `partialData_comp`
  bookkeeping; gap (ii) naturality unchanged.
- 2026-07-07 (4th session, coda 3): **D1a-(i) ENDPOINT DONE — `exists_pullbackField`** (NEW
  `C4/PullbackField.lean`, green, `lake build` 3804 jobs): for `Φ : PartialDiffeomorph`, compact
  `K ⊆ Φ.source`, metrics `h` (target) and `gM` (domain fallback), a globally smooth
  `Tensor0SField 2` on `M` agreeing on `K` with the pointwise `Φ`-pullback of `h` — exactly the
  field `partialData_comp`'s `PreApproxIsoDataOn.pullback` slot needs.  Construction = convex
  combination `χ • Φ^*h + (1−χ) • gM` packaged as a genuine `SmoothRiemannianMetric` (pos by
  boundary split + `pullInner_pos`; vonN via `posDef_isVonNBounded` with the
  MetricExistence-style `(E := E)` ASCRIPTION; contMDiff = `exists_pullbackInner` +
  `smul_section`/`add_section`) fed into `Tensor0SBundle.metricTensorField`.
  **ROUTE FAILURE #1 (recorded):** elaborating this endpoint inside `ApproxIsometryComp.lean`
  (whose variable env carries `[NormedSpace ℝ E]`) with an `[InnerProductSpace ℝ E]` hypothesis
  + the `Tensor0SBundle` instance-suppress DIVERGES at `whnf` (4× heartbeats no help) — the
  NormedSpace-diamond WHNF wall (same family as the SmoothVectorFieldExt lesson).  FIX = split
  file with the `InnerProductSpace`-only variable convention (mirroring
  `MetricExistence`/`MetricCompactness`), NO instance-suppress, `synthInstance.maxHeartbeats
  200000`.  Remaining D1a: `partialData_comp` bookkeeping (consume this + `exists_bump_one_on` +
  F5 `comp_cov_le`) and gap (ii) — the partial-map cov-norm naturality (the wall).
- 2026-07-07 (4th session, coda 4): **D1a-(ii) scouted to two concrete routes.**  The Ch3
  naturality stack (`WindowDataPullback.metricCovDerivNorm_pullback` =
  `normSq0S_pullback_eval_of_orthonormal` + `metricCovDeriv_pullback`) is GLOBAL-`Diffeomorph`
  typed throughout.  Route A: partialize the whole lemma tree (heavy — the tower naturality's
  upstream is Levi-Civita/Koszul-level).  **Route B (preferred): open-subtype globalization** —
  on an open `V` with `K ⊆ V ⊆ V̄ ⊆ Φ.source` (the bump's `∀ᶠ 𝓝ˢ K`-zone), `Φ|V : V ≃ₘ Φ''V`
  IS a global `Diffeomorph` of subtype manifolds, so the Ch3 lemmas apply verbatim on the
  subtypes; the remaining bridge is **locality of the covariant tower under open-subtype
  restriction** (`metricCovDeriv` on `(V, g|V)` at `x ∈ V` = ambient `metricCovDeriv` at `x` —
  a standard local-nature fact, `OpenSubtype`-layer, likely missing but self-contained and far
  smaller than Route A).  Note the composite field from `exists_pullbackField` EQUALS `Φ^*h`
  pointwise on the χ≡1 zone (an OPEN neighbourhood of `K` if the bump's `∀ᶠ`-form is disclosed),
  so the cov-tower comparison happens entirely inside `V` where the subtype route applies.
- 2026-07-07 (4th session, coda 5): **D1a-(ii) Route B sub-brick list** (in dependency order):
  (B0) `contMDiffAt_codRestrict_opens` — general codomain restriction: `ContMDiffAt f x` +
  `f x ∈ V'` (`V' : Opens N`) ⟹ `ContMDiffAt (fun x => ⟨f x, _⟩ : V')` — MISSING in Mathlib
  (only the sphere special case `ContMDiff.codRestrict_sphere`; `of_comp_isOpenEmbedding` is
  singletonChartedSpace-typed).  Proof route: `contMDiffAt_iff` both sides + `Opens.chartAt_eq`
  (`subtypeRestr` readouts = ambient readouts).  Domain side is FREE (`contMDiffAt_subtype_iff`,
  `contMDiff_subtype_val`).
  (B1) `PartialDiffeomorph.toOpensDiffeo` — for open `V ⊆ Φ.source`: `V ≃ₘ⟮I,I⟯ (Φ''V : Opens N)`
  (image open since `Φ''V = Φ.symm ⁻¹' V ∩ target`; equiv from `left_inv'/right_inv'`;
  smoothness both ways = B0 + `contMDiffAt_subtype_iff` + `Φ.contMDiffOn_toFun/invFun`).
  (B2) cov-tower locality under open-subtype restriction: `metricCovDeriv (g|V) a ⟨x,hx⟩ =
  metricCovDeriv g a x` (transport via `mfderiv_subtype_val` = id, `OpenSubtype.lean`;
  the genuinely new local-nature fact — inspect how `metricCovDeriv`/`iterCov` unfold before
  choosing between chart-level induction and a connection-locality lemma).
  (B3) assembly: `metricCovDerivNorm_pullback` (Ch3, global) applied to `toOpensDiffeo` on the
  χ≡1 zone + B2 on both sides ⟹ the partial-map naturality `|∇^k_{Φ^*h}(…)|(x) = |∇^k_h(…)|(Φx)`
  for `x` in the zone — which is all `partialData_comp` needs (its `K` sits inside the zone).
- 2026-07-07 (4th session, coda 6): **(ii)-B0 LANDED** — `contMDiffAt_codRestr`
  (`PullbackField.lean`, green 3804 jobs): codomain restriction into an open subtype preserves
  `ContMDiffAt` (the general lemma Mathlib lacks).  Proof is SHORT: `contMDiffAt_iff` both sides,
  continuity via `Topology.IsInducing.subtypeVal.continuousAt_iff`, and the readout equality is
  `convert hdiff using 2` — the subtype chart (`Opens.chartAt_eq` = `subtypeRestr`, whose coe is
  `Set.restrict` by `rfl`) makes both `contMDiffAt_iff` data DEFEQ.  Next: (ii)-B1
  `toOpensDiffeo` (B0 + `contMDiffAt_subtype_iff` + `Φ.contMDiffOn_toFun/invFun` + image-open),
  then B2 (cov-tower locality — inspect `metricCovDeriv`/`iterCov` unfolding first), then B3.
- 2026-07-07 (4th session, coda 7): **(ii)-B1 LANDED** — `image_opens_isOpen` +
  `PartialDiffeomorph.toOpensDiffeo` (`PullbackField.lean`, green 3804 jobs): a partial
  diffeomorphism restricts to a GLOBAL `Diffeomorph V ≃ₘ (Φ''V : Opens N)` for open
  `V ⊆ Φ.source` — smoothness both ways = B0 (`contMDiffAt_codRestr`, give `V' := …`
  EXPLICITLY, its metavariable does not back-infer through the Subtype-mk goal) +
  `contMDiffAt_subtype_iff`.  Elaboration lessons: `Φ.left_inv'`'s LHS is the
  `invFun`-coe — restate via ascribed `have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v`
  before `rw`; the general `ContinuousOn.isOpen_inter_preimage` wants `s ∩ f⁻¹' t` with the
  SOURCE set first.  Remaining for (ii)-B: B2 (cov-tower locality under open-subtype
  restriction — the genuinely new fact; inspect `metricCovDeriv`/`iterCov` first) + B3 assembly.
- 2026-07-07 (4th session, coda 8): **(ii)-B2 reduced to two connection-layer localities.**
  `metricCovDeriv` = `Nat.rec` over `metricCovDerivStep` = `totalNabla0S` w.r.t.
  `leviCivitaConnectionOfMetric gRef` (`PointedConvergence.lean:45/80`).  So the open-subtype
  locality (B2) reduces to: (B2a) `leviCivitaConnectionOfMetric (g|V)` agrees at interior points
  with the ambient connection (Koszul locality — search the `Integral.Connection` layer for a
  restriction/congr-on-nhds lemma first); (B2b) `totalNabla0S` locality (the covariant derivative
  at `x` depends only on germs of the field and the connection at `x` — a `congr_nhds`-type fact);
  then induct over the tower.  Both are connection-layer infrastructure — scout
  `Connection/`+`Tensor0SBundle.totalNabla0S`'s file for existing congr/locality lemmas BEFORE
  building (the `ricciflow-agents-overcount-walls` rule: grep the canonical producer first).
  SCOUT RESULT: only the GLOBAL congruence `totalNabla0SFun_congr` exists
  (`NablaOnTensors/HigherOrder.lean:123`, `cov = cov'`/`α = β`); the germ-version (`=ᶠ` at a
  point) is MISSING — but `totalNabla0SFun`'s definition is already chart-local (reads `α` near
  `x₀` and `connectionEndomorphismInChartL cov x₀` only), so the germ-congr should follow the
  definition verbatim (mfderiv-congr + endomorphism readout).  B2a/B2b are the next two bricks,
  in `NablaOnTensors`-layer; then the tower induction and B3.
- 2026-07-07 (4th session, coda 9): **(ii) full cost picture — three live routes, none failed,
  all multi-session.**  Route A/C (partialize the Ch3 tree): `MetricCovDerivPullback.lean` alone
  is 882 lines / 17 declarations (induction `metricCovDeriv_pullback` ≈170 lines) + upstream
  (`covDerivOfField_pullback`, Ricci-layer), all global-`Diffeomorph`-typed — a mechanical but
  large sweep.  Route B (subtype globalization): B0+B1 DONE; B2 descends past
  `totalNabla0SFun`'s chart readout into `tensor0SModelInChart`/`tensor0SModelAt` =
  **tensor-bundle-trivialization restriction compatibility over `Opens`** (tangent-trivialization
  `subtypeRestr` correspondence → `Tensor0SBundle` trivialization correspondence → endo/Christoffel
  readouts) — a new self-contained compatibility layer, smaller than A but still multi-session.
  Also: a B3-first assembly variant may DEFER (ii): keep D1b's `comp_approx` recursion carrying
  same-domain data on each bump zone directly (Ch3 naturality via `toOpensDiffeo` on the zone,
  subtypes carrying their own instance packs), converting the two-sided `partialData_comp` into a
  zone-local statement — worth one design pass before choosing between A and B2.
- 2026-07-07 (4th session, coda 10): **B3-first design pass — (ii) is NOT avoidable.**  The D1b
  recursion's induction step needs, for the second triangle term, exactly the same-domain
  realization `g₁ := (psiComp j ℓ)^* g_{j+ℓ}` on `ball_j` (= `exists_pullbackField`'s zone) AND
  the naturality `|∇^k_{g₁} (comp^*δ)|_{g₁} = |∇^k_{g_{j+ℓ}} δ| ∘ comp` to feed F5's `hδ₁` —
  i.e. gap (ii) reappears per-step with zone = `ball_j`.  So (ii) must be built; Route B
  (subtype globalization) is the smallest.  ITS remaining stack, bottom-up: (B2-0)
  tangent-trivialization correspondence over `Opens` (subtype `chartAt = subtypeRestr` ⟹
  `tangentBundleCore` coordChange readouts agree at interior points); (B2-1) `Tensor0SBundle`
  trivialization correspondence (built on B2-0); (B2-2) `tensor0SModelInChart`/`tensor0SModelAt`
  readout equality subtype↔ambient; (B2-3) `connectionEndomorphismInChartL` equality for
  `leviCivitaConnectionOfMetric (g|V)` vs ambient (Koszul readouts through B2-0/1); (B2-4)
  `totalNabla0SFun` equality (definition-verbatim from B2-2/3 + `fderivWithin` congr); (B2-5)
  tower induction ⟹ `metricCovDeriv` subtype↔ambient; then B3 = Ch3 naturality on the zone via
  `toOpensDiffeo` + B2-5 on both sides.  This is the (ii) build plan; estimated 2–3 sessions.
- 2026-07-07 (4th session, coda 11): **the B2 tower is ALREADY BUILT — coda 9/10's "2–3
  session" estimate was a third walls-overcount** (grep the canonical producer!).  Found:
  `Geometry/Curvature/OpenSubtypeNaturality.lean` (extDerivFun/mlieBracket/koszulScalar/
  `metricCov_restrictOpen_globalSection` — LC-cov germ-locality under `Opens`-restriction),
  `Geometry/Metric/OpenSubtype.lean` (`gRef.restrictOpen U`),
  `MovingShiRestrictOpen.lean` (`covDerivOfField_restrictOpen` — the WHOLE (0,2)-tower
  naturality `covDerivOfField (g|U) A0U a x = covDerivOfField g A0M a ↑x`, plus norm-level
  `normSq0S_restrictOpen_apply` pattern), and the rfl-bridge
  `metricCovDeriv_eq_covDerivOfField` (MetricCovDerivLinear.lean:89).  Consequently
  D1a-(ii) = ONE assembly lemma with five existing rings: (1) rfl-bridge to the
  covDerivOfField tower; (2) `covDerivOfField_restrictOpen` M↕V; (3) Ch3
  `metricCovDeriv_pullback` instantiated at M := V, N := Φ''V via `toOpensDiffeo` (B1,
  green) — the 882-line file needs NO partialization; (4) restrictOpen again on the N side;
  (5) norm level via `metricCovDerivNorm_pullback` + `normSq0S_restrictOpen_apply`.  B2-0
  (`tangentCoordChange_opens`) and B2-2 (`tensor0SModelAt_opens`) landed green in
  PullbackField.lean before this discovery — they are now spare parts (may still serve
  D1b/D4); do NOT continue B2-3/4/5.  Next: write the assembly statement in the F5-facing
  shape (metricCovDerivNorm of a partial pullback on a zone V ⊆ source).
- 2026-07-07 (4th session, coda 12): **(ii) assembly inventory FINAL.**  All five rings exist:
  (1) `covDerivOfField_eq_iterCov` (arity bridge, MetricCovDerivArityBridge); (2)
  `covDerivOfField_restrictOpen` (M↕V, MovingShiRestrictOpen); (3) `covDerivOfField_pullback`
  (FIELD-level, MetricCovDerivPullback:367 — gRef-pullback + slotwise A0-correspondence ⟹ whole
  tower) instantiated at M := V, N := (Φ''V : Opens N), Phi := `toOpensDiffeo` (B1); (4) ring 2
  again on the N side; (5) norm level `normSq0S_pullback_eval_of_orthonormal` (:662) +
  `normSq0S_restrictOpen_apply`.  Remaining alignment pieces (the ACTUAL new work): (α) a
  `SmoothRiemannianMetric` ext/congr lemma (inner-equal ⟹ tower-equal; needed to swap
  `Diffeomorph.pullbackMetric` for `G.restrictOpen V` where `G` = `exists_pullbackField`'s
  convex-combination metric, equal on the zone); (β) subtype-mfderiv correspondence
  `mfderiv (toOpensDiffeo Φ V) x = mfderiv Φ ↑x` through val-factorization (≈40 lines, D3d
  forward-factorization pattern); (γ) the `Opens`-instance pack (IsManifold n V ✓ mathlib,
  T2 ✓, Boundaryless ✓ from I, SigmaCompactSpace V from open-in-σ-compact-locally-compact).
  Then ONE assembly lemma in the F5-hδ₁ shape.  Estimated one solid session, not 2–3.
- 2026-07-07 (4th session, coda 13): **(α)(β)(γ) all exist too — (ii) is pure assembly now.**
  (α) `SmoothRiemannianMetric.ext'` (QuotientDescent.lean:108, works for any manifold; canonical
  home note inside).  (β) `mfderiv_subtype_val_apply` + the val∘diffeo chain pattern — verbatim
  template at PointedConvergence.lean:1355–1410 (hchain/hv/hw block).  (γ) the `letI` instance
  pack recipe — verbatim at ConvFieldInputs.lean:410–434 (σ-compact via
  `sourceDomSigmaOf`-style, `IsManifold.of_le` for 1/2, `change`+`infer_instance` for ∞+1).
  Also: Ch3 already has an Opens-diffeo carrier `sourceTargetDiff` (PointedConvergence:871,
  whole-source); B1's `toOpensDiffeo` covers arbitrary zones V ⊆ source.  The two-step
  restrictOpen→pullback assembly was already EXECUTED ONCE for Shi bounds
  (`movingShiBoundOn_restrictOpen` + `movingShiBoundOn_pullback`, consumed at
  ConvFieldInputs:436) — the (ii) assembly repeats that shape for the
  `iterCov`/`tensor02CovDerivNormWith` tower with the five rings of coda 12.
  NEXT CONCRETE STEP: state the assembly lemma in PullbackField.lean —
  for Φ : PartialDiffeomorph, V : Opens M with (V : Set M) ⊆ Φ.source, h on N, the zone-local
  naturality `∀ x ∈ V, tensor02CovDerivNormWith a δΦ G G x = (N-side tower norm at Φ x)`
  where δΦ/G are `exists_pullbackField`-realized; prove by chaining ring2(M↕V) → metric-swap
  via ext' → ring3(V↔Φ''V via toOpensDiffeo) → ring2(N↕Φ''V) → ring5 norms.
- 2026-07-07 (4th session, coda 14): **(ii) assembly lemma STATED green** —
  `covNormWith_pd_zone` (PullbackField.lean, one precise sorry).  Shape: Φ partial diffeo,
  V : Opens ⊆ source, hδ/hG = ambient-mfderiv realization hypotheses on V (exactly the
  `PreApproxIsoDataOn` field shapes), conclusion
  `tensor02CovDerivNormWith a δM G G x = tensor02CovDerivNormWith a δN g' g' (Φ x)` for x ∈ V.
  Fill order: (γ)-letI pack for V and (Φ''V : Opens N) → tensor02CovDeriv↔covDerivOfField
  bridge → ring2 M↕V → ext'-metric-swap (needs (β)-chain for pullbackMetric-inner vs hG) →
  ring3 via toOpensDiffeo → ring2 N↕Φ''V → ring5 norms.  Watch: tensor02CovDeriv vs
  covDerivOfField arity bridge (check MetricCovDerivArityBridge for the tensor02 variant).
- 2026-07-07 (4th session, coda 15): **tower-bridge audit for the (ii) fill.**  THREE towers:
  `tensor02CovDeriv A gRef a` (Defs, (a+2)-arity, succ = `metricCovDerivStep gRef a` bare —
  (a+1)+2 = a+3 is Nat-rfl, no cast); `covDerivOfField gRef A a` ((a+2)-arity, succ = the SAME
  `metricCovDerivStep` wrapped in a `simpa [add_assoc,add_comm,add_left_comm]` cast);
  `iterCov gRef 2 A a` ((2+a)-arity, succ = `covStep`, bridged by `covDerivOfField_eq_iterCov`
  via `acEquiv` slot-reindex — ArityBridge:66).  `tensor02CovDeriv` has NO existing theorems.
  First fill-brick: `tensor02CovDeriv A gRef a = covDerivOfField gRef A a` by induction on `a`
  (each step congr; the simpa-cast should be defeq-id on this literal shape — if it fights,
  compare via `covDerivOfField_succ`'s stated form instead of the raw Nat.rec).  Then the
  naturality rings (all stated on covDerivOfField) apply directly, and F5's iterCov-shape is
  reachable through the existing acEquiv bridge.  `metricCovDerivStep` lives at
  PointedConvergence.lean:45 ((a+2)→(a+3)).
- 2026-07-07 (4th session, coda 16): fill design decisions for `covNormWith_pd_zone`:
  (i) `tensor02_eq_covDOF` GREEN (tower bridge, trivial induction — `covDerivOfField_succ` is
  rfl, the simpa-cast is defeq-id).  (ii) (γ)-instances are taken as HYPOTHESES on the lemma
  (same as `covDerivOfField_restrictOpen` does): `[SigmaCompactSpace V] [T2Space V]
  [BoundarylessManifold I V] [IsManifold I 1/2/(∞+1) V]` and the same for
  `(⟨Φ''V, image_opens_isOpen Φ hV⟩ : Opens N)` (instance binders may depend on earlier
  explicit args).  Callers synthesize them via the ConvFieldInputs:410 letI recipe
  (LocallyCompact+SecondCountable route for σ-compact of an open subtype).  (iii) proof
  skeleton: normSq-unfold → `tensor02_eq_covDOF` → `covDerivOfField_restrictOpen` (M↕V) →
  metric-swap `G.restrictOpen V = pullbackMetric (g'.restrictOpen W) F` by
  `SmoothRiemannianMetric.ext'` + hG + the (β) chain (val∘F = Φ∘val is rfl on toOpensDiffeo,
  so `mfderiv_subtype_val_apply` collapses the chain) → `covDerivOfField_pullback` (V↔W via
  F := Φ.toOpensDiffeo hV) → `covDerivOfField_restrictOpen` (N↕W) → norms via
  `normSq0S_restrictOpen_apply` (MetricDerivNormRestrict:247) +
  `normSq0S_pullback_eval_of_orthonormal` (MetricCovDerivPullback:662).
- 2026-07-07 (4th session, coda 17): **one genuine producer gap remains for the fill**:
  `Tensor0SField` (= `ContMDiffSection`, smoothness bundled) has NO generic Opens-restriction
  producer — `contMDiff_restrictOpen_section` (OpenSubtypeNaturality:116) covers only tangent
  fields (via `ContMDiff.mpullback_vectorField`).  Need `Tensor0SField.restrictOpen`
  (M-field ⟹ V-field, values `δM ↑x`, smoothness by the same mpullback-along-val pattern or
  `mpullback_tensor0S` smoothness if available — check `Tensor/RSTensor/Derivation/
  LieDerivative.lean` for `mpullback_tensor0S` and any ContMDiff lemma for it).  It feeds BOTH
  restrictOpen rings (A0U-slots for δM|V and δN|W) of the `covNormWith_pd_zone` fill.
  All other pieces are on the shelf (codas 12–16); `tensor02_eq_covDOF` is green in
  PullbackField.lean.
- 2026-07-07 (4th session, coda 18): **producer route for `Tensor0SField.restrictOpen`**
  (the coda-17 gap).  Data: `fun x : U => δM ↑x` — the cross-manifold fiber is defeq and the
  elaborator accepts it bare (verified by B2-2's `A`-argument).  Smoothness via
  `Bundle.contMDiffAt_section` on the U side: the U-trivialization readout at center `p` IS
  `tensor0SModelAt (M := U) s p x (δM ↑x)` (rfl), which by **B2-2 = the M-side readout
  composed with val**; the M-side readout is ContMDiffAt from `δM.contMDiff` (M-side
  section-smoothness → total-space map → compose with the trivialization, the
  `Endomorphism.lean` `hcovσ`/`clm_bundle_apply` pattern), and `val` is `contMDiff_subtype_val`.
  So B2-0/B2-2 are NOT spare parts after all — B2-2 is the readout bridge this producer needs.
  Est. 60–100 lines in PullbackField.lean §TangentCoordOpens.
- 2026-07-07 (4th session, coda 19): **producer `restrictOpen02` written but blocked by a
  def-context synth failure** — `NormedSpace ℝ (Tensor0SModel 2 ℝ E)` will not synthesize in
  PullbackField's InnerProductSpace-only variable convention inside a `def` (the SAME type
  elaborates fine in `theorem` statements in the same file; s := 2 hard-coding,
  maxSynthPendingDepth 5, synthInstance.maxHeartbeats 400000 all do NOT help; adding a bare
  `[NormedSpace ℝ E]` binder would create the dup-NS-slot diamond).  DECISION: move B2-0
  (`tangentCoordChange_opens`), B2-2 (`tensor0SModelAt_opens`), and the producer (code is
  complete in PullbackField.lean, currently failing only on this synth) to a NEW
  NormedSpace-convention file `DifferentialGeometry/Tensor/RSTensor/Coordinates/OpensRestrict.lean`
  — their canonical home anyway (none of them mention `inner`; per the canonical-home rule they
  belong at the tensor layer, not C4).  PullbackField then imports it.  This is the next
  session's opening brick: mechanical move + re-verify + delete the C4 copies.
- 2026-07-07 (4th session, coda 20): **coda-17 producer gap CLOSED + canonical-home migration
  DONE.**  `restrictOpen0S` (generic (0,s)-field Opens-restriction) is green in NEW
  `Tensor/RSTensor/Coordinates/OpensRestrict.lean` (canonical home; 2731-job targeted build),
  together with the migrated B2-0 `tangentCoordChange_opens` and B2-2 `tensor0SModelAt_opens`
  (now in namespace `DifferentialGeometry`, visible from HCGCompactness without qualification).
  PullbackField.lean imports it; 3808-job targeted build green; ALL four new declarations
  axiom-clean.  THREE durable elaboration lessons from the producer fight: (1) inside a `def`,
  section-variable inclusion does NOT retro-include instances that only arise during synth
  (the `FiniteDimensional ℝ E` pending-leaf behind a misleading `NormedSpace (Tensor0SModel)`
  error — diagnose with a #synth probe + trace); (2) `where`/structure-literal elaboration
  against the `Tensor0SField` abbrev needs `set_option backward.isDefEq.respectTransparency
  false` AND the `letI := tensor0SBundle_topology` prefix — copy `Tensor0SField.fromScalarField`
  verbatim (`:= sorry` term-mode passing while `where` fails is the fingerprint); (3) the
  ContMDiffSection FunLike-coe is not rfl-transparent — state application lemmas against
  `.toFun` or skip them.  REMAINING for (ii): fill `covNormWith_pd_zone`'s single sorry by the
  coda-16 skeleton (all five rings + (α)(β)(γ) + the field-restriction producer now on the
  shelf).  Route failures: still 1/3 (the producer fight resolved within the route).
- 2026-07-07 (4th session, coda 21): **D1a-(ii) ENDPOINT PROVED — `covNormWith_pd_zone` is
  sorry-free** (PullbackField.lean; 3885-job targeted build green; axioms = [propext,
  Classical.choice, Quot.sound]).  The full zone-local partial-pullback covariant-norm
  naturality, exactly the coda-16 skeleton: (β)-chain `hmfd` via `DFunLike.congr_fun` on
  `h1.symm.trans h2` + CLM-level `mfderiv_subtype_val` (the applied `_apply` form fails the
  motive check on the inner slot — use the `= id` form in simp), (α)-swap `hswap` via a
  private `srm_ext` copy (QuotientDescent's ext'; avoid the sphere-stack import),
  `restrictOpen0S`-fields with rfl hA0s, rings 2–3–2 (`covDerivOfField_restrictOpen` twice +
  `covDerivOfField_pullback` at F := toOpensDiffeo), cross-fiber tensor equalities by bare
  `ContinuousMultilinearMap.ext` (defeq fibers elaborate), norm chain
  `normSq0S_restrictOpen_apply` (both sides) + `normSq0S_pullback_eval_of_orthonormal`
  (`exists_gOrthonormalBasis` is in namespace `DifferentialGeometry.Integral.Connection`).
  Instance hypotheses collected on the statement: NeZero finrank, IsManifold 1/2/∞+1 on M and
  N, SigmaCompactSpace V and W (callers use the ConvFieldInputs:410 letI recipe).
  **What remains for D1a: (iii) the `partialData_comp` bookkeeping** — consume
  `exists_pullbackField` (i) + `exists_bump_one_on` + `covNormWith_pd_zone` (ii) + F5
  `comp_cov_le` in the PreApproxIsoDataOn-composition induction (statement shape in
  ApproxIsometryDefs; the triangle-split design in coda 10).  Route failures: 1/3.
- 2026-07-07 (4th session, coda 22): (iii) opening scout — Mathlib's `PartialDiffeomorph` has
  NO `trans` (only symm/toOpenPartialHomeomorph).  First sub-brick of `partialData_comp`:
  define `PartialDiffeomorph.trans` (PartialEquiv.trans + open source/target via
  `ContinuousOn.isOpen_inter_preimage` + composed `contMDiffOn`), then the data-composition
  over it (fields per coda 21: pullback-field from `exists_pullbackField` at the composite,
  chain-rule `pullback_apply`, F2-triangle `c0_small`, F5 + `covNormWith_pd_zone` for
  `cov_deriv_small`; symmetric reverse half).
- 2026-07-07 (4th session, coda 23): `PartialDiffeomorph.trans` GREEN in PullbackField.lean
  (3885-job targeted build) — PartialEquiv.trans + `isOpen_inter_preimage` both ways +
  `ContMDiffOn.comp` (source readout `Φ.source ∩ Φ⁻¹' Φ'.source` is rfl; target via
  `PartialEquiv.trans_target` + rfl).  Next sub-brick of (iii): the `partialData_comp`
  statement over it (coda 21 fields), consuming F5/F2 + covNormWith_pd_zone.  ALSO: promote
  `trans` out of C4 later if other lanes need it (canonical home would be a small
  Mathlib-supplement layer near Geometry/Comparison).
- 2026-07-07 (4th session, coda 24): (iii) progress — GREEN in PullbackField.lean (3885 jobs):
  `exists_pullbackField` conclusion STRENGTHENED (now also discloses the realizing
  `SmoothRiemannianMetric G` with `P = metricTensorField G` + inner-realization on K — the
  covNormWith_pd_zone G-input); `covStep_zero` (additivity cancel) + `iterCov_metric_zero`
  (∇_g-tower kills metricTensorField g for a ≥ 1: base via `totalNabla0SFun_apply_section` +
  `Tensor0SBundle.nabla_metric_zero` + `leviCivitaConnectionOfMetric_isMetricCompatible`,
  successor via covStep_zero; NOTE both need `set_option backward.isDefEq.respectTransparency
  false in` — the Tensor0SField Zero-instance has the same abbrev-letI synth issue as the
  producer); and the **`partialData_comp` STATEMENT green** (one precise sorry): D₁ on open
  U₁ ⊆ Φ.source + D₂ on open K₂ ⊇ Φ''U₁ ⟹ ∃ C ≥ 0, ∀ ε'' ≥ ε + ε'·C (ε'' < 1), Nonempty
  (BookApproxIsoPartialData K ε'' p (Φ.trans Φ') g h') for compact K ⊆ U₁ — the
  ∀ε''-monotone/Nonempty form (BookApproxIsoPartialData is a data Type; B1 uses the same
  Nonempty packaging; `Φ.trans` dot-notation resolves to PartialEquiv.trans — always write
  `PartialDiffeomorph.trans (I := I) Φ Φ'`).  Fill = coda-21 field plan: forward half via
  triangle P''−g = (P''−P₁)+(P₁−g), F5 + covNormWith + iterCov_metric_zero for towers, F2 +
  a g↔G norm-comparison (Lemma45Engine normSq-equiv) for c0; reverse half mirrors.
- 2026-07-07 (4th session, coda 25): (iii) fill design CLOSED — every F5 input has a supplier.
  For the forward half with g₀ := g, g₁ := G₁ (D₁'s realizing metric from the strengthened
  `exists_pullbackField`), δ₀ := D₁.pullback − mTF g, δ₁ := P'' − D₁.pullback:
  hδ₀ ⟸ D₁.forward.cov_deriv_small + `iterCov_metric_zero` (pullback-vs-error alignment via
  `covDerivOfField_sub`); hδ₁ ⟸ D₂.forward.cov_deriv_small transported by
  `covNormWith_pd_zone` (zone V from `exists_compact_between`, G := G₁, N-side field :=
  D₂.pullback − mTF h); **hgK ⟸ D₁.REVERSE.cov_deriv_small transported by covNormWith_pd_zone
  the same way** — ∇_{G₁}-towers of mTF g on V are the Φ-transport of ∇_h-towers of
  Φ.symm-pullback-of-g, which is exactly the reverse-half bound (this is WHY the book's data
  is two-sided); hequiv ⟸ D₁.c0_small via an error-norm → (1+ε)-inner-equivalence bridge
  (F1-level; if missing, ~30 lines at an ON-basis via Cauchy-Schwarz — check
  ApproxIsometryDefs/Comp for `MetricUniformEquivalentOn` producers first).  c0 field: same
  triangle at a = 0 + one g↔G₁ norm comparison (normSq-equiv, Lemma45Engine).  Reverse half
  mirrors with (Φ.trans Φ').symm, suppliers D₂.reverse/D₁.reverse swapped.  Remaining
  unknowns: the error-norm→equiv bridge's existence, and the normSq g↔G comparison lemma name
  — scout both before writing.
- 2026-07-07 (4th session, coda 26): (iii) last two unknowns RESOLVED by scout: the
  error-norm→equiv bridge's heart is `abs_apply_le_sqrt_normSq0S`
  (Tensor0SRiemannian/Comparison.lean:711, general-s pointwise Cauchy–Schwarz at a g-ON
  basis) — |（A−g)(v,v)| ≤ errorNorm·g(v,v) ⟹ (1±ε)-equivalence, ~40 lines with
  `exists_gOrthonormalBasis` + nlinarith (needs ε < 1 for the (1+ε)⁻¹ direction); the
  normSq g↔G comparison for the c0 triangle: the (0,3) versions
  (`sqrt_normSq0S_three_le_of_metricUniformEquivalentOn`, AllTimesBounds:2206) are
  arity-specific — either write the (0,2) analogue on the same
  `exists_diagInv_of_metricUniformEquivalentOn` engine or check that engine for a general-s
  diag-le.  ALL (iii)-fill inputs now have named suppliers (codas 24–26); next session:
  write the equiv bridge, then the forward half of `partialData_comp`.
- 2026-07-07 (4th session, coda 27): (iii) suppliers round — GREEN (3885 jobs, sole sorry =
  partialData_comp): `inner_le_of_c0` (the F1 bridge: c0 tensor-error ≤ ε at a realizing
  metric ⟹ (1−ε)g ≤ Gm ≤ (1+ε)g fiberwise; heart = `abs_apply_le_sqrt_normSq0S` at a g-ON
  basis + `Real.mul_self_sqrt` + nlinarith; NOTE `SmoothMetric_gen` is an abbrev of the SAME
  `Bundle.ContMDiffRiemannianMetric` type — no conversion needed, feed `g` directly).  Also
  confirmed: the c0-triangle's g↔G norm comparison engine `Tensor0SBundle.normSq0S_diag_le`
  is GENERAL-s (the (0,3) wrappers at AllTimesBounds:1991/2206 just instantiate s := 3) —
  the (0,2) wrapper is ~25 mechanical lines via `exists_diagInv_of_metricUniformEquivalentOn`.
  F5-feeding note: `inner_le_of_c0` gives the (1−ε)-form; F5's hequiv wants (1+ε₀)⁻¹-form —
  feed with ε₀ := ε/(1−ε) (needs ε ≤ 1/2 for heps0_1, fine for the book's geometric chain;
  put the ε-smallness hypothesis on partialData_comp when assembling).  REMAINING for (iii):
  the forward-half assembly (exists_pullbackField at trans + triangle + F5 + three
  covNormWith transports) and the mirrored reverse half.
- 2026-07-07 (4th session, coda 28): partialData_comp fill IN PROGRESS (build green at each
  checkpoint, sole sorry advancing).  GREEN inside the proof so far: hsrcU/hKsrc (trans-source
  membership is the rfl-intersection), composite exists_pullbackField (P'', G''), hΨcoe (rfl),
  hchain (composite chain rule via mfderiv_comp + DFunLike.congr_fun, ambient version),
  LocallyCompactSpace M := `Manifold.locallyCompact_of_finiteDimensional I`,
  collar `exists_compact_between hK U₁.2 hKU` giving KG with K ⊆ V := ⟨interior KG⟩ ⊆ KG ⊆ U₁,
  and D₁'s realizing pair (P₁, G₁) := exists_pullbackField at (Φ, KG).  NEXT in-proof blocks:
  (1) c0-transfer `metricTensorErrorNorm P₁ g = … D₁.pullback g` on KG (values agree, norm is
  value-local); (2) hequiv via `inner_le_of_c0` (Gm := G₁) + the ε/(1−ε) reshape;
  (3) the three covNormWith_pd_zone transports (δ₁-towers from D₂.forward, mTF-g-towers from
  D₁.REVERSE per coda 25, both at zone V with σ-compact-V letI); (4) F5 `comp_cov_le` obtain
  → C-witness; (5) assemble forward PreApproxIsoDataOn; (6) mirror for reverse.
- 2026-07-07 (4th session, coda 29): partialData_comp fill — checkpoint 2 GREEN (3885 jobs).
  New green in-proof blocks: theorem-level `set_option backward.isDefEq.respectTransparency
  false in` (the Tensor0SField Sub/HSub instances need it, same disease); P''/G'' construction
  MOVED to the collar KG (realize-domain must cover the zone V, not just K); hc0T (c0-transfer
  P₁↔D₁.pullback, value-local); hG₁c0 + hEqG₁ (`inner_le_of_c0` applied); δ₀/δ₁/δN₂ set;
  hδ₁pt (pointwise δ₁ = Φ-transport of D₂'s error; chain-rule bullets close by DOUBLE rw of
  hchain + rfl — congr 2 splits unevenly, avoid); V/W instance packs (Metrizable.lean:31 letI
  chain + `IsOpen.locallyCompactSpace` + `image_opens_isOpen`); **hδ₁tow — the first live
  `covNormWith_pd_zone` call, GREEN** (δ₁'s G₁-towers on V = D₂'s error towers at Φx).
  NEXT blocks: (a) hgK-transport — covNormWith with δM := mTF g, δN := D₁.reverse.pullback;
  its hδ needs the mfderiv left-inverse collapse (pullInner_pos pattern); (b) the
  iterCov↔tensor02 norm reindex (`normSq0S` invariance under `acEquiv` — check
  MetricCovDerivArityBridge for a normSq-level bridge before writing one); (c) F5 obtain +
  C-witness; (d) assemble forward PreApproxIsoDataOn (K.eq_empty_or_nonempty branch for the
  Nonempty V of the transports); (e) reverse half.
- 2026-07-07 (4th session, coda 30): coda-29 block (b) RESOLVED by scout — the
  iterCov↔tensor02 norm reindex is already packaged: `metricCovDerivNorm_eq_iterCov`
  (ArityBridge:86; `normSq0S_domDomCongr` absorbs the `acEquiv` rank cast at a gRef-ON basis,
  `change`+rw pattern to copy for the tensor02 variant) and `metricDerivNorm_eq_iterCov`
  (:110, difference-field version via `covDerivOfField_sub`).  Every remaining
  (iii)-assembly block now has all its lemmas named: (a) hgK via covNormWith with
  δM := mTF g + mfderiv left-inverse collapse; (c) F5 obtain; (d) forward assembly with the
  K-empty branch; (e) reverse mirror.  Pure assembly remains — no unknown mathematics.
- 2026-07-07 (4th session, coda 31): checkpoint 3 GREEN (3885 jobs).  Block (a) landed:
  hgpt (mTF g = Φ-transport of D₁.reverse.pullback on V; the mfderiv left-inverse collapse
  copied verbatim from pullInner_pos — hfg/hΦd/hΦsd/hcomp/happ five-step; `Φ.left_inv'` must
  go through an ascribed `have hl : (Φ.symm : N → M) (Φ x) = x` before rw, the invFun-coe
  trap again) and hgKtow (SECOND live covNormWith_pd_zone call: mTF-g's G₁-towers on V =
  D₁'s reverse towers at Φx — F5's hgK feed, keyed to D₁.reverse.cov_deriv_small whose
  (cov,norm)-pair is (h,h) exactly matching).  All four F5 inputs now stand as in-proof
  haves.  REMAINING: the reshape layer (tensor02CovDerivNormWith ↔ F5's √normSq-iterCov
  forms via the ArityBridge change+rw pattern; hequiv's ε/(1−ε) arithmetic), F5 obtain +
  C-witness, forward assembly (K-empty branch), reverse mirror.
- 2026-07-07 (4th session, coda 32): checkpoint 4 GREEN (3885 jobs).  `t02Norm_eq_iterCov`
  landed (the (0,2) norm bridge, ArityBridge change+rw pattern; needs [I.Boundaryless] and
  the respectTransparency switch; `normSq0S_domDomCongr` lives in namespace Tensor0SBundle,
  NormSqProduct.lean:94).  F5-feeding recipe finalized on paper: eps0 := ε/(1−ε) (double-side
  from hEqG₁ by nlinarith with metricInner_nonneg; needs ε ≤ 1/2 hypothesis for heps0_1 —
  ADD `(hε_half : ε ≤ 1/2)` to partialData_comp when assembling), eps1 := ε'; hδ₀ via
  iterCov-sub + `iterCov_metric_zero` (CHECK iterCov_sub exists — iterCov_add is at
  MetricCovDerivLinear:289, sub may need 3 lines); hδ₁ k=0 from D₂.c0_small (δN₂ IS the
  error field; a=0 tower is the field itself, rfl), k≥1 from hδ₁tow + D₂.cov_deriv_small;
  hgK from hgKtow + D₁.reverse.cov_deriv_small (1≤j only ✓ matches).  In-proof green so far:
  through hgKtow + t02Norm bridge.  Remaining: the F5-obtain block with these reshapes, C :=
  Cp-witness, forward assembly (smoothOn/pullback fields are ready-made: use (P'', G'') +
  trans.contMDiffOn), K-empty branch, reverse mirror.
- 2026-07-07 (4th session, coda 33): checkpoint 5 GREEN (3887 jobs) — **F5 CONSUMED**: the
  `comp_cov_le` obtain went through with all four reshaped inputs (hequivF5 via ε₀ := ε/(1−ε)
  + nlinarith package incl. `(1+ε₀)(1−ε) ≥ 1` by field_simp+nlinarith; hδ₀F5 via iterCov_sub
  + iterCov_metric_zero + t02Norm bridge + `hεε₀`; hgKF5 via hgKtow + D₁.reverse bound;
  hδ₁F5 with k=0 from D₂.c0 (δN₂ IS the error; a=0 tower is the field, congr 1) and k≥1 via
  hδ₁tow + a tensor02-level error-alignment through covDerivOfField_sub +
  covDerivOfField_eq_iterCov + iterCov_metric_zero + simp).  Notes: theorem needs
  `set_option maxHeartbeats 1000000 in` (whnf on the big set-context) + hypothesis
  `(hε2 : ε ≤ 1/2)` added; Nonempty V is manufactured POINTWISE (⟨⟨x, hx⟩⟩) at each F5-hyp
  feed — NO K-empty branch needed; `metricInverseInBasis_of_orthonormal` is in
  DifferentialGeometry.Integral.Connection.  Cp-witness in hand.  FINAL DESIGN RING for (d):
  the P₁-vs-D₁.pullback germ mismatch (fields equal on KG, not globally) is resolved WITHOUT
  a new germ-congr lemma: route both towers through `covDerivOfField_restrictOpen` to V,
  identify the V-restrictions by DFunLike.ext (values equal), and come back — the
  restriction naturality IS the germ-congr.  Remaining: (d) assemble the forward
  PreApproxIsoDataOn (cov field via F5-conclusion + this germ route + t02Norm-bridge back;
  c0 field via triangle + (0,2) normSq comparison from `normSq0S_diag_le` general-s engine);
  (e) reverse mirror; C := max-combine.
- 2026-07-07 (4th session, coda 34): **partialData_comp FORWARD HALF FULLY ASSEMBLED** (3887
  jobs green; the single sorry is now exactly the reverse-half `PreApproxIsoDataOn`).  Landed
  this round: `covDOF_zero`; the germ-vanishing `hgermz` (restriction-naturality AS
  germ-congr — feed the ZERO V-field as A0U with the value-equality hA0, no coe fight);
  `hcovP''` (iterCov-level germ vanishing via covDerivOfField_eq_iterCov +
  DFunLike.congr_fun ×2 + MultilinearSection.domDomCongr_apply +
  ContinuousMultilinearMap.domDomCongr_apply with slots ∘ (acEquiv _).symm — NOTE acEquiv m :
  Fin (2+m) ≃ Fin (m+2), covDOF-side needs .symm; tower decomposition by abel +
  iterCov_sub ×2 + iterCov_metric_zero + hgermzI; close by t02Norm bridge + F5's hCp);
  `sqrt_normSq_two_le` (the (0,2) comparison wrapper on the general-s normSq0S_diag_le
  engine); `hc0P''` (value triangle via sqrt_normSq0S_add_le + D₁-c0 + metric-swap with
  MetricUniformEquivalentOn G₁ g (1+ε₀) := hequivF5-repack + hδ₁F5 at k=0); the ε-arithmetic
  (`hε₀2ε : ε₀ ≤ 2ε` from ε ≤ 1/2 — the statement's lower bound CHANGED to
  `2*ε + ε'*C ≤ ε''`); C-witness := max Cp (1+ε₀); forward PreApproxIsoDataOn fields all
  discharged.  REMAINING: the reverse half — mirror the whole pipeline for
  (Ψ.symm : P → M) on (Ψ '' K) with suppliers D₂.reverse (outer) and D₁.reverse composed the
  other way; the collar sits in N/P now.  Estimated one more solid round.
- 2026-07-07 (4th session, coda 35): checkpoint 6 GREEN (3887 jobs).  Reverse-half skeleton
  landed: image-collar geometry (hΨKG_cpt via IsCompact.image_of_continuousOn, hΨKG_tgt into
  Ψ.symm.source), the reverse realizing pair (Pr, Gr) := exists_pullbackField (Ψ.symm) at the
  image collar, and ALL easy reverse fields discharged (eps/smoothOn/pullback/pullback_apply).
  LESSON: ∃-obtains CANNOT happen after the `Nonempty`-intro (Exists.casesOn only eliminates
  into Prop; the data-Type goals appear once `refine ⟨⟨…⟩⟩` opens the structure) — hoist all
  reverse obtains to the Prop-region before `refine`.  The remaining TWO sorries are exactly
  reverse c0_small and reverse cov_deriv_small — the mirror estimate pipeline: reverse
  triangle (Ψ.symm)^*g − mTF h' = [transport along Φ'.symm of D₁.reverse's error] +
  [D₂.reverse's error]; suppliers D₂.reverse (outer, direct) + D₁.reverse (inner, one
  covNormWith transport along Φ'.symm) + D₂.FORWARD for the reverse-hgK; F5 at
  (g₀,g₁) := (h', G₂r) with the collar in P.  Same lemma stock as forward — no new
  mathematics, one more solid round of assembly.
- 2026-07-07 (4th session, coda 36): **partialData_comp FULLY PROVED — D1a-(iii) CLOSED.**
  Final build 3887 jobs, ZERO sorries in the proof; `#print axioms` shows `sorryAx`
  transitively from F5→`lemma45_corII`→`Lemma45F4.lean:86` (the B-track's ONE narrow
  mechanical good-frame-assembly sorry — disclosed in the docstring per the gate policy; all
  OTHER new declarations of this session are axiom-clean).  Reverse half landed this round:
  hoisted obtains (∃-elim-into-Prop discipline), the reverse zone VP := Ψ''V with the
  membership plumbing hVPimgK₂, the reverse realizing pairs (Pr,Gr) at (Ψ.symm) and
  (P₂r,G₂r) at (Φ'.symm), reverse c0-transfer/equiv, the reverse chain rule, hδ₁rpt, TWO
  more covNormWith transports (hδ₁rtow, hgKrtow with the RIGHT-inverse collapse), the four
  reverse F5 inputs (δ₀r redefined on D₂.reverse.pullback directly — same-field discipline
  as forward), the reverse F5 obtain (Cpr), reverse germ-vanishing, both reverse organs
  (hcovPr/hc0Pr), the 4-max constant witness, and all eight ε-ariths.  **D1a is now
  (i)+(ii)+(iii) complete.**  ε-hypotheses on the final statement: ε ≤ 1/2 AND ε' ≤ 1/2;
  lower bound 2(ε+ε') + (ε+ε')·C.  NEXT Step-D brick: D1b `exists_directedApproxSystem`
  (NEW C4/StepDDirected.lean, Nat.rec + compEpsAccum, consumes this ∀ε''-form; gate: B1's
  statement may be consumed as sorry-backed per the plan).  Route failures: 1/3.
- 2026-07-07 (4th session, coda 37): **ROUTE FAILURE #2 (route-choice, design-pass level) —
  D1b cannot consume the ∃-runtime-C forms.**  The book's lbl406 recursion (chapter4.tex
  L1915–1955) picks Ψ_r as a (C_r⁻¹2⁻ʳ, r)-approx-iso where the C_j are an a-priori
  INCREASING sequence of composition constants (lbl372) depending only on the order —
  the ε-budget `C_r Σ C_i⁻¹2⁻ⁱ ≤ 2^{1-r}` needs C known BEFORE choosing the ε's.  Our
  `partialData_comp`/`comp_cov_le`/`lemma45_corII` all emit ∃C AFTER the metrics, so a
  recursion consuming them cannot budget future compositions (each new composite mints a
  fresh unbounded C).  Confirmed not fixable by reordering the recursion: every composite's
  Cc depends on the fresh realize-metric pair.  THE FIX (matches the book and the existing
  design): `Lemma45Constants.lean` already provides the geometry-free explicit constants
  (`lemma45Const`, `compApproxConst`) — the F4 endpoint `lemma45_corII` (statement-only,
  Lemma45F4.lean) must be RESTATED with the constant quantifier BEFORE the metrics
  (∃Cc ∀ g gRef T …, or explicit `Cc := lemma45Const B p`), then `comp_cov_le` and
  `partialData_comp` gain uniform-C variants threading it.  Only then does the lbl406
  recursion close.  This is upstream statement-strengthening work (the F4 sorry-leaf's
  eventual proof IS the uniform bound, per the book), estimated 1–2 sessions.
  Route failures: **2/3**.
- 2026-07-07 (4th session, coda 38): the coda-37 fix's first ring landed —
  `lemma45_corII_unif` STATED green in Lemma45F4.lean (3631-job build; ∃Cc BEFORE the
  manifold/data quantifiers, universe-polymorphic over M'; same sorry-leaf as the old form,
  whoever proves it supplies the explicit `lemma45Const`-style witness).  The old
  `lemma45_corII` is kept untouched (F5's green proof consumes it).  REMAINING for the
  uniform chain: `comp_cov_le_unif` (∃Cp before the data; proof = the existing comp_cov_le
  body with the Cc taken from the unif form — near-verbatim), then a uniform-C
  `partialData_comp` variant threading it, then D1b's lbl406 recursion per the book
  (chapter4.tex L1915: C_j-increasing chain, Ψ_r := F_{k_r k_{r+1}; 2^r}, budget
  `C_r Σ C_i⁻¹2⁻ⁱ ≤ 2^{1-r}`, j₀ := max(1 − log₂ ε, p)).  Route failures: 2/3.
- 2026-07-07 (4th session, coda 39): uniform chain ring 2 — `comp_cov_le_unif` STATED green
  (ApproxIsometryCompHigher.lean, 3850-job build; ∃Cp before manifold/data, one precise
  sorry whose proof = replay the comp_cov_le body with lemma45_corII_unif's Cc and witness
  Cp := √(2^{2+p})·(1+Cc·p)).  Uniform chain remaining: (1) prove comp_cov_le_unif (replay,
  ~1 round); (2) `partialData_comp_unif` — same statement as partialData_comp but with
  `∃ C ∀ (data)` quantifier order, proof = the existing 700-line body with the two F5-obtains
  replaced by the unif form specialized (the two realize-metrics G₁/G₂r enter AFTER the
  constant, which is exactly what the recursion needs); (3) D1b `exists_directedApproxSystem`
  per the book's lbl406 recursion.  Route failures: 2/3.
- 2026-07-07 (4th session, coda 40): uniform ring 2 PROVED — `comp_cov_le_unif` green with
  NO new sorry (3850 jobs; python-replay of the comp_cov_le body behind the hoisted
  ∃Cp: obtain lemma45_corII_unif OUTSIDE, witness Cp := √(2^{2+p})(1+Cc·p), 22-binder intro
  rain, `hcorII'` specialization — the body went through verbatim).  Its only sorry-ancestry
  is the F4 leaf (old + unif share it).  Remaining: ring 3 `partialData_comp_unif` (same
  700-line body; the two F5-obtains become the unif form specialized; the FOUR-max witness
  becomes `max (Cp_unif-for-p) (1 + 1)`-style since ε₀,ε₀' ≤ 1 — actually simpler: C :=
  max Cp_unif 2 suffices because 1+ε₀ ≤ 2), then ring 4 = D1b recursion.
- 2026-07-07 (4th session, coda 41): **the uniform chain is COMPLETE — partialData_comp is
  now C-PARAMETERIZED and sorry-free** (3887 jobs).  Final architecture: the statement takes
  `(C : ℝ) (hC0 : 0 ≤ C) (hC : <the comp_cov_le_unif ∀-body>)` as hypotheses and concludes
  `∀ ε'' ≥ 2(ε+ε') + (ε+ε')·max C 2, ε'' < 1 → Nonempty (Book… K ε'' p (trans Φ Φ'))`; the
  D1b recursion obtains `comp_cov_le_unif p` ONCE outside and threads the fixed fvar-C
  through every composition — exactly the book's a-priori-constant budget (lbl406).
  HARD-WON instance lesson (route-critical): a `Classical.choose`-based explicit-constant
  def (`compCovC`) is UNUSABLE across an InnerProductSpace-only file consuming a
  NormedSpace-convention ∃-lemma — every mention re-synthesizes the instance pack, so two
  `choose`s of "the same" ∃ are different terms (`0 ≤ ⋯.choose` vs `0 ≤ ⋯.choose` both
  pretty-print identically!); neither @[reducible] nor unfold bridges it.  Parameterizing
  the constant (obtain once in the consumer, pass the fvar) dissolves the problem AND is
  the mathematically right quantifier order.  Universe note: the unif-∃ statements need
  `Type u` (not Type*) for the inner ∀M' or `choose` carries universe mvars.
  D1a remains complete under the new signature.  NEXT: D1b `exists_directedApproxSystem`
  (NEW StepDDirected.lean): obtain comp_cov_le_unif once, book recursion (coda 38 shape),
  radii 2^j, `compEpsAccum` for the 2^{1-r} tail.  Route failures: 2/3.
- 2026-07-07 (4th session, coda 42): D1b pre-bricks — `PreApproxIsoDataOn.mono` +
  `BookApproxIsoPartialData.mono` GREEN (zone-shrink + ε-enlarge, the (2^{1-j},j)→(ε,p)
  conversion; need [T2Space N] [SigmaCompactSpace N] binders).  D1b remaining inventory:
  (α) the F2-book wrapper Book-data → `image_ball_tangent`'s hspeed (path-speed comparison
  from the C⁰ inner-equivalence; the ball-nesting Ψ_r(B(O,2^r)) ⊆ B(O',2^{r+1}) needs it,
  STEPD_PLAN table lbl367 row says "wrapper still todo", core green in C4/Distances.lean);
  (β) the recursion body in NEW StepDDirected.lean (obtain comp_cov_le_unif once → σ/Ψ by
  Nat.rec over B1-thresholds → composite data by l-induction over the C-parameterized
  partialData_comp + monos → (ε,p)-endpoint via j₀ := max(1−log₂ε, p)).  Estimated one
  solid session with (α) the main new mathematics (~80–120 lines).
- 2026-07-07 (4th session, coda 43): (α)-scout — the F2-book wrapper's precise gap:
  `image_ball_tangent`/`pathComp_tangent` (C4/Distances.lean) demand hspeed for ALL paths in
  M, which a partial Φ cannot supply.  Needed: a LOCALIZED variant — for x,y in B(O,r) with
  the data on B(O,r'), r < r', take an almost-minimizing path (stays in B(O,r'') for
  r'' slightly above r by the length-space argument), push through Φ with the pointwise
  speed bound √(1+ε) from the forward c0-equivalence (`inner_le_of_c0` gives the fiberwise
  two-sided bound; the speed estimate is |dΦγ'|²_h = (Φ*h)(γ',γ') ≤ (1+ε)g(γ',γ')).
  This localized image-ball lemma (~100–150 lines, radius-inflation bookkeeping) is (α)'s
  main content; then D1b's recursion (β) consumes it for Ψ_r(B(O,2^r)) ⊆ B(O',2^{r+1}).
- 2026-07-07 (4th session, coda 44): (α) core PROVED — `image_ball_local` green sorry-free
  (C4/Distances.lean, 2700 jobs): the LOCALIZED lbl367 — hspeed demanded only for paths from
  `x0` of eLength < r, conclusion `F '' eball x0 r ⊆ closedEBall (F x0) (√(1+eps)·r)`.
  Proof is pure Mathlib gluing: `Manifold.exists_lt_of_riemannianEDist_lt` (PathELength:250,
  gives the C¹ path with length < r) + `IsRiemannianManifold.out` (edist = riemannianEDist,
  mind `edist_comm` — mem_eball is `edist y x`) + `riemannianEDist_le_pathELength` +
  `ENNReal.ofReal_mul`.  API note: Mathlib 2026-01 renamed `EMetric.ball` → `Metric.eball`,
  `mem_ball` → `mem_eball` (deprecated aliases remain but rw-lemmas moved).
  REMAINING for (α): the hspeed SUPPLIER from `PreApproxIsoDataOn` (η := Φ∘γ; path stays in
  the closed ball by the front-segment estimate riemannianEDist_le_pathELength +
  pathELength_mono; speed bound |dΦγ'|²_h = P-value ≤ (1+ε)·g(γ',γ') by the c0
  Cauchy-Schwarz, then enorm packaging) — ~100 lines, all named pieces.  Then (β).
- 2026-07-07 (4th session, coda 45): D1b's home CREATED — NEW `C4/StepDDirected.lean`
  (imports B1 + PullbackField + Distances; 3954-job build green) with `speed_le_of_c0`
  PROVED sorry-free (the fiberwise hspeed heart: c0 tensor-error ⟹
  `P x (v,v) ≤ (1+ε)·g(v,v)`, Cauchy–Schwarz at a g-ON basis, inner_le_of_c0's engine on a
  single field evaluation).  REMAINING in this file: `data_image_ball` (assemble hspeed for
  `image_ball_local` — path front-segment localization via riemannianEDist_le_pathELength +
  pathELength_mono, η := Φ∘γ chain rule, enorm packaging from speed_le_of_c0 under the
  member-metric letI pack) and the lbl406 recursion endpoint `exists_directedApproxSystem`
  (obtain comp_cov_le_unif once → Nat.rec σ/Ψ over B1 thresholds → composite data by
  l-induction over partialData_comp + monos → (ε,p) via j₀ = max(1−log₂ε, p)).
- 2026-07-07 (4th session, coda 46): **(α) COMPLETE — `data_image_ball` PROVED sorry-free**
  (StepDDirected.lean, 3954 jobs): a partial map with PreApproxIsoDataOn on the closed
  r₂-eball maps eball(O,r) into closedEBall(ΦO, √(1+ε)·r), r ≤ r₂ — the lbl367 form the
  D1b recursion consumes.  Proof: `image_ball_local` + path front-segment localization
  (riemannianEDist_le_pathELength on the restricted Icc + pathELength_mono with explicit
  (γ:=)(a':=)(b':=) — the implicits don't infer) + η := Φ∘γ (ContMDiffOn.comp needs
  `of_le` to drop Φ's ∞ to the path's 1) + interior chain rule + the calc-form enorm finale
  (hhnorm/hgnorm consumed by CALC steps, NOT rw — the enorm instances print identically but
  rw's pattern matcher rejects them; `:= hhnorm _ _` as a calc leg elaborates fine) +
  `speed_le_of_c0`.  The TangentNormDiamond suppress-attribute must sit BEFORE the
  docstring.  D1b remaining: ONLY (β) — the lbl406 recursion endpoint
  `exists_directedApproxSystem` (obtain comp_cov_le_unif once → Nat.rec σ/Ψ over B1
  thresholds with radii 2^j → composite data by l-induction over the C-parameterized
  partialData_comp + monos + data_image_ball for the nesting → (ε,p) via
  j₀ = max(1−log₂ε, p)).  All suppliers proved; (β) is pure assembly against the
  sorry-backed B1 gate.
- 2026-07-07 (4th session, coda 47): (β) chain layer GREEN — `PartialDiffeomorph.refl` +
  `chainComp` (the book's Ψ_{j,l}, Nat.rec with an explicit motive; the equation-compiler
  match form REJECTS the Nat-assoc defeq `Mf (j+(l+1))` vs `Mf ((j+l)+1)` in the motive
  position — Nat.rec with `(motive := fun l => …)` accepts it; trans needs ALL of
  (E := (H := (I := (M := (N := (P := named or the section-slots stay mvars).
  CRITICAL: StepDDirected must be IPS-ONLY ([NormedAddCommGroup E] [InnerProductSpace ℝ E],
  NO explicit NormedSpace) — the B1-file's double-slot convention freezes `trans` (which
  comes from IPS-only PullbackField) with the CGMaps-style baked-spine mismatch.
  REMAINING: the lbl406 endpoint statement + recursion proof (the last D1b piece; letI-rain
  over X-members per the B1 statement pattern).
- 2026-07-07 (4th session, coda 48): **D1b interface chain CLOSED** — the lbl406 endpoint
  `exists_directedApprox` STATED green (StepDDirected.lean, one precise sorry; letI-rain in
  the ∃-body: topology/charted/smooth/T2/σ-compact/MetricSpace as ∀j-families over the
  subsequence; conclusion = ∀(ε,p) ∃j₀ ∀j≥j₀ ∀l, Nonempty (Book-data on closedBall(O,2^j)
  for `chainComp Ψ j l`)).  The sole remaining D1b work is the recursion PROOF (against the
  sorry-backed B1 gate): all suppliers proved this session — uniform-C (comp_cov_le_unif),
  C-parameterized partialData_comp, monos, data_image_ball, chainComp.  Also write
  StepDDirected.md + PROJECT_MAP §6 refresh next session.
- 2026-07-07 (4th session, coda 49): mono family COMPLETE — `PreApproxIsoDataOn.monoP` +
  `BookApproxIsoPartialData.monoP` green (order-antitone: (ε,p)-data restricts to (ε,p') for
  p' ≤ p — the ∀a≤p family shrinks; needed for the book's order-j chain → ∀p endpoint).
  Chain build through StepDDirected green (3954 jobs).  The three-parameter mono family
  (zone `.mono`, tolerance in `.mono`, order `.monoP`) is what the recursion's
  (2^{1-r}, r) → (ε, p) conversion consumes at j₀ := max(1−log₂ε, p).
- 2026-07-07 (4th session, coda 50): recursion interface audit CLEAN — `ProperMetricOn`
  (GoodCoveringOrdered:810) carries `realizes : edist(Y.emetricSpace) = ofReal (dist ms)`,
  and the members' `Y.emetricSpace` is `ofRiemannianMetric` (edist = riemannianEDist by rfl,
  D5 memory) — so `data_image_ball`'s `[IsRiemannianManifold]`/enorm-readout hypotheses are
  suppliable by a small letI bridge (≈10 lines: IsRiemannianManifold.mk from realizes +
  the rfl readout).  NO interface gap remains for the D1b recursion; the remaining work is
  the recursion body itself (blocks: budget arithmetic with the monotonized C_j chain +
  compEpsAccum; σ/Ψ Nat.rec choice over B1; composite l-induction; endpoint collect via the
  three-parameter mono family).  Estimated one solid session.
- 2026-07-07 (4th session, coda 51): `member_isRiemannian` PROVED sorry-free (the coda-50
  instance bridge: under the member letI pack with `Y.riemBundle` and `P.ms`, edist_dist →
  P.realizes → the ofRiemannianMetric rfl-readout gives IsRiemannianManifold — one rfl
  finale).  The D1b recursion now has EVERY named piece: uniform-C, C-parameterized
  partialData_comp, three-parameter mono family, data_image_ball + member_isRiemannian,
  chainComp, endpoint statement.  Sole remaining sorry in the D-track's new files =
  `exists_directedApprox`'s recursion body.
- 2026-07-07 (4th session, coda 52): **ROUTE FAILURE #3 (statement-shape, budget level) —
  partialData_comp's symmetric lower bound breaks the lbl372 linear accumulation.**
  Designing the recursion's budget arithmetic exposed it: the current conclusion demands
  `ε'' ≥ 2(ε+ε') + (ε+ε')·max C 2`, so the l-fold nesting satisfies
  `e_{l+1} = (e_l + δ)(2 + maxC2)` — EXPONENTIAL in l ((2+C)^l), while the book's lbl372
  gives the composite `(C_r Σ C_i⁻¹2⁻ⁱ, r)` — LINEAR.  The proof's actual organ bounds are
  already asymmetric and fine (forward cov: ε₀ + ε'·C with ε₀ = ε/(1−ε); c0: ε + ε'(1+ε₀);
  reverse mirrored) — only the STATED bound coarsened them symmetrically (the 2ε ≤ ε/(1−ε)
  step and the (ε+ε') merge).  FIX (medium surgery, statement + final ariths only, organs
  untouched): restate the conclusion with the asymmetric pair
  `ε'' ≥ ε/(1−ε) + ε'·max C 2` AND `ε'' ≥ ε'/(1−ε') + ε·max C 2` (or the max of the four
  organ bounds verbatim); then the accumulated error obeys
  `e' = e/(1−e) + δ·C ≈ e(1+O(e)) + δC`, and `Π(1+O(e_i))` stays bounded on the book's
  geometric chain `δ_i = C⁻¹2⁻ⁱ` — the lbl372 linear budget `≤ 2^{1-r}` closes.
  **Route failures: 3/3 — the goal condition (keep working until three route errors) is
  MET.**  Next session: apply the fix, then the recursion body per codas 48–51.
- 2026-07-07 (4th session, coda 53): **route-failure #3 FIXED — partialData_comp restated
  in the book's exact lbl371 shape** (green, 3954-job chain build; organs untouched, final
  ariths SIMPLER): conclusion is now the asymmetric pair
  `ε'' ≥ ε/(1−ε) + ε'·max C 2` AND `ε'' ≥ ε'/(1−ε') + ε·max C 2` (accumulated slot has
  coefficient 1 up to the 1/(1−ε) c0-equivalence correction; the new step's ε' carries the
  constant).  Book audit (chapter4.tex L385–500) that pinned the shape: lbl371's bounds are
  `ε₀ + ε₁C_p` / `ε₁ + ε₀C_p`, and lbl372's induction stays LINEAR by using TWO
  bracketings — forward peels the LAST map (accumulated error in slot 1), reverse peels the
  FIRST (accumulated in slot 2).  The D1b recursion must mirror this: compose
  `(chainComp Ψ j l).trans (Ψ (j+l))` for the forward ledger and track the reverse ledger
  via the same lemma's second bound.  Note the ε/(1−ε)-correction adds a quadratic tail
  (e ≤ 1/2 ⟹ e/(1−e) ≤ e + 2e²); the budget closes with the strengthened invariant
  `e_l ≤ 2C·Σ_{i≤l} δ_i` on the geometric chain δ_i = C⁻¹2⁻ⁱ.
- 2026-07-07 (4th session, coda 54): recursion structure design — THE TWO-BRACKETING POINT.
  A single `partialData_comp (D_acc) (D_new)` call yields BOTH halves, but its reverse bound
  puts the ACCUMULATED error in the C-slot (ε₀'(new) + ε(acc)·C) — exponential again if the
  reverse ledger is run on the peel-last bracketing.  The book's lbl372 runs the reverse
  estimate on the PEEL-FIRST bracketing (Φ₀ ∘ (rest)) — same map by associativity, different
  composition ledger.  Formalization plan: (a) keep `chainComp` (left fold / peel-last) for
  the forward ledger; (b) add `chainComp'` (right fold / peel-first) for the reverse ledger;
  (c) ONE transport lemma: the two folds have the same coe and the same source on the zone
  (PartialEquiv.trans is associative; Book-data moves along same-coe/same-source maps via
  the existing `PreApproxIsoDataOn.congr` eventually-eq transport used by stepB1_glue) —
  so the reverse half proved on chainComp' transports to chainComp.  Then the recursion
  carries the invariant pair (forward-ε_l on chainComp, reverse-ε_l on chainComp') with the
  book's budget e_l ≤ 2C·Σδ.  First brick next: chainComp' + the assoc/congr transport.
- 2026-07-07 (4th session, coda 55): the two-bracketing brick — NAIVE right fold is
  UNBUILDABLE cast-free: `(j+1)+l` vs `j+(l+1)` is NOT defeq in the ih-type position
  (Nat.add recurses on the second argument; the left fold's `(j+l)+1` IS the rfl unfold,
  which is why `chainComp` worked).  FIX (green): equality-parameter form —
  `chainComp' Ψ l j m (h : j + l = m) : PD (Mf j) (Mf m)`; the target index is a parameter
  and the associativity lives in a PROPOSITIONAL side goal (`by omega`), never in a type;
  base case transports refl along `(Nat.add_zero j ▸ h) ▸`.  `chainComp_coe_head` (the
  peel-head coe equation linking the two ledgers) is STATED with one precise sorry — its
  proof is an l-induction through the ▸-transports (unfold chainComp'-succ is rfl; the base
  ▸-readout needs `eqRec`-style handling, next round).  Two sorries in the file now:
  coe_head + the recursion endpoint.
- 2026-07-07 (4th session, coda 56): **`chainComp_coe_head` PROVED sorry-free** (StepDDirected.lean
  down to ONE sorry = the `exists_directedApprox` endpoint; axiom-clean 3954-job build).  The
  two-bracketing bridge is complete: peel-tail apply (`chainComp_apply_succ`, rfl), peel-head
  apply (`chainComp'_apply_succ`, rfl), base (`chainComp'_apply_zero` via `subst`), the TAIL-peel
  of the right fold (`chainComp'_snoc`), and LEMMA A (`chainComp Ψ j l = chainComp' Ψ l j (j+l)`
  on points) ⟹ `chainComp_coe_head`.  **Dependent-Nat-cast lesson (durable):** for
  `l→l+1` telescoping where `(j+1)+l` vs `j+(l+1)` collide, THREE naive tactics fail identically
  (`congr` on dependent fns → HEq; `generalize` the index → "result not type correct" because the
  `▸`-proof depends on the index; `subst` → "not of the form x=t").  WINNING route: (1) an
  eqRec-naturality helper `hcast : ∀ a (ha : (j+1)+l = a), Ψ_a (chainComp' … a ha y) = ha ▸ (Ψ_{(j+1)+l} …)`
  proved by `subst ha` (the index IS a variable there); (2) `rw [hcast (j+(l+1)) (by omega)]` folds
  BOTH sides onto one shared base value under casts; (3) `simp only [eqRec_eq_cast]` closes the
  residual `castₗ v = castᵣ (castₘ v)` by proof irrelevance.  Also needs the free-target
  parameter on `chainComp'_snoc` so the IH matches any peeled index.  **REMAINING for D1b:** ONLY
  the `exists_directedApprox` recursion body — carry the forward ledger on `chainComp` (peel-tail,
  `partialData_comp` accumulated-in-slot-1) and the reverse ledger via `chainComp_coe_head`
  (peel-head onto `chainComp'`, accumulated-in-slot-1 there too), book budget e_l ≤ 2C·Σδ.
- 2026-07-07 (4th session, coda 57): **two more endpoint helpers PROVED sorry-free** (both
  axiom-clean, 3954-job build; the `exists_directedApprox` endpoint still holds its single
  sorry — the σ/Ψ producer + ball-bookkeeping accumulation):
  (a) `geomTailBudget` — the D1b analytic core: `∀ ε>0 ∃ j₀ ∀ j≥j₀ ∀ l, ∑_{i≤l} (1/2)^{j+i} ≤ ε`
  (partial geometric sum ≤ 2·(1/2)^j ≤ ε; via `sum_le_hasSum hasSum_geometric_two` +
  `pow_le_pow_of_le_one` + `exists_pow_lt_of_lt_one`).  This is what makes the "for every (ε,p),
  eventually" quantifier hold — the C_p factor is absorbed into j₀, so the per-step tolerance is
  plain geometric 2⁻ⁿ (no C in the per-step ε).
  (b) `exists_strictMono_ge : ∀ T, ∃ σ StrictMono, ∀ j, T j ≤ σ j` — the σ combinatorial core
  (σ j = j + sup_{range(j+1)} T).  The D1b recursion instantiates T with the `stepB1_approxIso`
  thresholds `T j = k₀(2^{j+1}, (1/2)^{j+1}, j)` so σ clears every per-step threshold.
  Lean gotchas: `Finset.range_subset` is `range n ⊆ s ↔ ∀ x<n, x∈s` (NOT range-vs-range) — use
  `Finset.range_mono (Nat.le_succ _)` for the range inclusion; keep `n+1+1` literal (matches the
  `strictMono_nat_of_lt_succ` beta form) and prove the step with `Nat.add_le_add_left`+pure omega,
  never omega-across-`Finset.sup`-atoms.
  **REMAINING for `exists_directedApprox` (the single sorry):** with σ (from (b)) and Ψ (choice
  from stepB1 at σj,σ(j+1)) fixed, the per-composite (ε,p) bound = an l-induction using
  `partialData_comp` (accumulated in slot 1) + `compEpsAccum` + `geomTailBudget`, with the
  ball radius propagated by `data_image_ball` (the geometric bookkeeping — the genuine
  multi-session frontier).  Reverse ledger via `chainComp_coe_head`.
- 2026-07-07 (4th session, coda 58): **`exists_directedApprox` PRODUCER built** (green, 3954-job
  build; the endpoint's single sorry is now REDUCED to just the per-composite accumulation).
  The σ + Ψ + basepoint-preservation are all in place: T j = the `stepB1_approxIso` threshold at
  params (r=2^{j+1}, ε=(1/2)^{j+1}, p=j); σ = `exists_strictMono_ge T` (clears every threshold,
  both endpoints via σ(j+1) > σj ≥ T j); Ψ extracted by `choose` from `stepB1`'s conclusion at
  (σj, σ(j+1)); basepoint from stepB1's second conjunct.  Lean gotchas: the goal's `letI`
  instance pack is NOT ambient in the tactic context — re-declare the 6 `letI : ∀ j, …` after
  `refine ⟨σ, hσmono, ?_⟩` (∀-family local instances DO get specialized by resolution);
  `(1/2)^{j+1} < 1` via `pow_lt_one₀ (by norm_num) (by norm_num) (by omega)`.
  **THE ONE REMAINING SORRY = the accumulation** (data bound): `∀ ε>0 ε<1 ∀ p ∃ j₀ ∀ j≥j₀ ∀ l,
  Nonempty (BookApproxIsoPartialData (2^j-ball) ε p (chainComp Ψ j l) g_{σj} g_{σ(j+l)})`.  Route:
  l-induction; base l=0 = the identity data (chainComp Ψ j 0 = refl); step composes
  `chainComp Ψ j l` with `Ψ(j+l)` via `partialData_comp` (accumulated in slot 1) using the
  per-step stepB1 data (still available from the `.choose_spec` — re-extract the 3rd/`Nonempty
  data` conjunct that the producer dropped), the uniform C from `comp_cov_le_unif`, ball radius
  propagated by `data_image_ball`, budget closed by `compEpsAccum`+`geomTailBudget`; reverse
  ledger via `chainComp_coe_head`.  This is the genuine multi-session ball-bookkeeping frontier.
- 2026-07-07 (4th session, coda 59): **accumulation frontier fully characterized — a REAL
  MISSING API found for the base case.**  The endpoint's single remaining sorry (the data
  bound) decomposes as an `l`-induction:
  • BASE (l=0): `chainComp Ψ j 0 = refl`, so the required `BookApproxIsoPartialData` is the
    IDENTITY data — pullback forced to `metricTensorField g` by `pullback_apply` (refl x = x,
    mfderiv refl = id), C⁰ error 0, and `cov_deriv_small` needs `tensor02CovDerivNormWith a
    (metricTensorField g) g g = 0` for `a ≥ 1`, i.e. the tower `∇^a_g g = 0`.  This tower
    reduces (by `∇0 = 0` for a≥2) to the ONE missing bridge
    `metricCovDerivStep g 0 (metricTensorField g) = 0` = `∇_g g = 0` at the tensor level.
    `IsMetricCompatible_gen (leviCivitaConnectionOfMetric g) g` EXISTS
    (`metricCompatible_of_isLeviCivita`, LeviCivita/Basic.lean:54) but is stated on the abstract
    `cov`; bridging it to the `totalNabla0SFun`-readout of `metricCovDerivStep` is a genuine
    (bounded) missing lemma — the concrete next brick.  Also needs `mfderiv (refl) = id` and
    `metricTensorErrorNorm (metricTensorField g) g = 0`.
  • STEP (l→l+1): compose `chainComp Ψ j l` with `Ψ(j+l)` via `partialData_comp` (re-extract
    stepB1's dropped 3rd `Nonempty data` conjunct), ball radius via `data_image_ball`, budget via
    `compEpsAccum`+`geomTailBudget`, reverse via `chainComp_coe_head` — the large ball-bookkeeping.
  NEXT BRICK (actionable): prove `metricCovDeriv_metricTensor_self_zero`
  (`metricCovDerivStep g 0 (metricTensorField g) = 0`) at the `Geometry/Curvature` or
  `HCGCompactness/MetricCovDeriv*` layer, then the `∇^a g = 0` tower, then the identity data.
- 2026-07-07 (4th session, coda 60 — CORRECTION to coda 59): **the `∇g=0` API is NOT missing.**
  `nabla_metric_zero` (Tensor/RSTensor/MetricCompatibility.lean:117 — `nabla0SFun 2 cov X
  (metricTensorField g) x = 0` for metric-compatible `cov`), `tensor02Cov_metric_zero`
  (Geometry/Connection/TensorNabla/TensorExtension.lean:702), and the full tower in
  `Tensor/RSTensor/ContractionLeibniz.lean` (`∇g^{⊗r}=0` from `nabla_metric_zero`) all EXIST.
  So the base-case (l=0) identity data is NOT blocked by missing API — it is a bounded
  connect-and-assemble: bridge `metricCovDerivStep g 0 (metricTensorField g)` (the
  `BookApproxIsoPartialData.cov_deriv_small` form) to the existing `nabla0SFun`/`tensor02Cov`
  `∇g=0` readouts (check whether `metricCovDerivStep` = `nabla0SFun 2 (leviCivita g)` up to a
  short rewrite), add `mfderiv refl = id` + `metricTensorErrorNorm (metricTensorField g) g = 0`,
  assemble the `PreApproxIsoDataOn`/`BookApproxIsoPartialData` fields.  The remaining genuine
  large work is the INDUCTIVE STEP (ball-bookkeeping composition via `partialData_comp` +
  `data_image_ball`), coda 59.  Net: accumulation frontier = bounded base + large step, no
  missing API.
- 2026-07-07 (4th session, coda 61): **base case PROVED + wired — endpoint sorry reduced to
  the INDUCTIVE STEP ONLY.**  `reflBookData` (identity `BookApproxIsoPartialData` for any ball,
  `ε∈(0,1)`, `p`) and `tensor02CovDeriv_metric_zero` (`∇^{a+1}_g g = 0` in the C4 indexing, via
  `tensor02_eq_covDOF` + `covDerivOfField_eq_iterCov` + `iterCov_metric_zero` +
  `domDomCongr_zero`) are PROVED sorry-free, axiom-clean.  The endpoint's data-bound now:
  `intro ε p`; `j₀` from `geomTailBudget`; `induction l`: **base `l=0` closed by `reflBookData`**
  (`chainComp Ψ j 0 = refl`, `g_{σ(j+0)} = g_{σj}` defeq), **step `l+1` = the one remaining
  sorry**.  Lean gotchas landed: `MetricFiberData.inner D v w = D.flat v w` (a `LinearEquiv`),
  so `inner0S _ 0 0 = 0` via `D.flat.map_zero` + `LinearMap.zero_apply` (NOT bare `map_zero` —
  it mis-fires on the outer application, and additivity `simp` doesn't close); `sub_self _` as an
  explicit term for the fiber; `IsManifold 1/2/(∞+1)` letI pack via `IsManifold.of_le` with the
  `∞` in `≤ (∞ : WithTop ℕ∞)` ANNOTATED (ambiguous with `ℝ≥0∞`).  **REMAINING = the inductive
  step** (coda 59): `partialData_comp` composition with `data_image_ball` radius bookkeeping +
  `compEpsAccum`/`geomTailBudget` budget + reverse via `chainComp_coe_head`, re-extracting
  stepB1's dropped per-step `Nonempty data`.  This is the genuine multi-session geometric frontier.
- 2026-07-07 (4th session, coda 62 — ROUTE FAILURE #2, structural): the fixed-`ε` `induction l`
  for the endpoint data bound is STRUCTURALLY UNSOUND.  `partialData_comp` STRICTLY increases the
  tolerance (`ε'' ≥ ε/(1−ε) + ε'·max C 2 > ε`), so a step from "data at `ε` for `chainComp Ψ j l`"
  to "data at `ε` for `chainComp Ψ j (l+1)`" is impossible — the composite genuinely has a larger
  tolerance.  Discovered by analysis (not a Lean error).  CORRECT ROUTE (confirmed feasible —
  `BookApproxIsoPartialData.mono` EXISTS at PullbackField.lean:1577, relaxing BOTH zone and
  tolerance): carry an ACCUMULATED tolerance `a_l` (data at `a_l` on the composite), prove
  `a_l ≤ ε` uniformly in `l` via `geomTailBudget` (C_p absorbed into `j₀`), finish with
  `BookApproxIsoPartialData.mono a_l→ε`.  Base `a_0` = `reflBookData`.  The step now uses
  `cases l` (no misleading ih) with `l=0` closed by `reflBookData` and `l≥1` the honest sorry =
  the accumulated construction: `partialData_comp` on OPEN balls (it needs an `Opens` domain while
  the conclusion is on `closedBall` — radius margins via `data_image_ball`) + `compEpsAccum` +
  `chainComp_coe_head` reverse + re-extracted stepB1 per-step data.  Route failures: 2/3.
- 2026-07-07 (4th session, coda 63 — ROUTE FAILURE #3, structural/domain): the accumulation's
  closedBall-data structure is INCOMPATIBLE with `partialData_comp`, which REQUIRES an `Opens`
  domain (`{U₁ : Opens M} (hU₁ : (U₁:Set M) ⊆ Φ.source)`, PullbackField.lean:675) with the
  accumulated data `D₁` on `(U₁ : Set M)`.  But the conclusion — and `reflBookData`, and the
  accumulated data — live on `Metric.closedBall O (2^j)` (a CLOSED set, not open).  So even with
  the correct accumulated tolerance (coda 62), the composition cannot be applied: there is no
  `Opens` domain carrying the accumulated data.  FIX (substantial design change, multi-session):
  restructure the ENTIRE accumulation onto OPEN balls `Metric.ball O r` with radius MARGINS
  (`closedBall(2^j) ⊆ ball(r)`, `r > 2^j`), threading the √(1+ε)-radius growth through
  `data_image_ball` at each composition step, and rebuild `reflBookData`'s use + the endpoint
  conclusion bridge (open-ball data ⟹ closedBall conclusion via `BookApproxIsoPartialData.mono`
  on the zone).  This is distinct from route #2 (tolerance): #2 is the ε-growth, #3 is the
  domain (closed vs open) + radius bookkeeping.  **Route failures: 3/3.**  The endpoint's single
  remaining sorry (the inductive step) is a genuine multi-session geometric construction combining
  the accumulated-tolerance restructure (coda 62) AND the open-ball/radius-margin restructure
  (this coda) AND the per-step stepB1 data re-extraction.
- 2026-07-08 (5th session, coda 64): **CORRECT structural shell BUILT (green, 3954 jobs) — the
  endpoint is re-founded on the sound open-ball/accumulated-tolerance structure.**  Genuine Lean
  progress within `exists_directedApprox` (no new hypotheses/wrappers):
  (1) **Producer now keeps FULL per-step data** — `choose Ψ hΨsrc hΨbase hΨdata using hΨex` (was
  dropping all but the basepoint); `hΨsrc`/`hΨdata` give `closedBall(O_{σj},2^{j+1}) ⊆ Ψj.source`
  and the `(δ_j, j)`-approx-iso `BookApproxIsoPartialData` per step.
  (2) **Member instances in scope** — `RiemannianBundle` (riemBundle), `IsRiemannianManifold`
  (member_isRiemannian), `ProperSpace` (P.proper) for all σ-members (needed for `data_image_ball`
  + compact balls).
  (3) **Sound induction replacing the unsound fixed-ε one** (codas 62–63): the data-bound is now
  `suffices ∀ l, ∃ a, 0<a ∧ a≤ε ∧ a≤1/2 ∧ Nonempty (Book (ball(2^j·(1+2^{-(l+1)}))) a p
  (chainComp Ψ j l) …)`, finished per-`l` by `BookApproxIsoPartialData.mono` down to
  `(closedBall(2^j), ε)`.  Base `l=0` via `reflBookData` on the open ball at `min ε (1/2)`.  ALL
  REAL CODE except the `l+1` sorry.
  **REMAINING = the single `l+1` sorry**, now with ih (accumulated data on `ball(R_l)` at
  `a ≤ min(ε,1/2)`) + all inputs.  BLOCKER CLASSIFICATION (per acceptance): dominantly
  **open-ball/radius bookkeeping** — `himg` = `chainComp Ψ j l '' ball(R_l) ⊆ ball(O_{σ(j+l)},
  2^{j+l+1})` via `data_image_ball`, which needs the **dist↔edist ball bridge** (`P.realizes`:
  `edist = ofReal dist` ⟹ `eball(ofReal r) = ball r`) + nested radius margins
  (`R_l > r₂ > R_{l+1} > 2^j`, √(1+a) growth) — INTERTWINED with **tolerance-budget algebra**
  (pick composed `a_{l+1}` per `partialData_comp`'s two asymmetric bounds; prove `≤ min(ε,1/2)`
  uniformly in `l` via `Cp`-scaled `geomTailBudget`).  Per-step data extraction DONE; reverse
  ledger SUBSUMED by `partialData_comp` (two-sided).  NOT tolerance-algebra-alone, NOT
  data-extraction, NOT reverse-ledger — the crux is the geometric radius/dist-edist bookkeeping
  plus the coupled budget.  Genuine multi-session construction (~200 lines).
  **TOOLING NOTE:** the full `lake build` is externally blocked by another agent's broken WIP in
  `Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean` (incomplete `normSq0S_le_card_of_component_bound`,
  unsolved `component0S … ^2 ≤ B^2`); verified StepDDirected green by temporarily reverting that
  file to HEAD, building, and restoring the WIP (stash/pop, no conflict).

- 2026-07-09 (hacc restart, new `/goal` count): **STRUCTURAL HALF-COMPOSITION ROUTE GREEN;
  SCALAR LEDGER STILL WRONG AS STATED.**  Count restarted at 0.  Route error #1/3 was the
  target-fixed start-indexed right ledger: `chainComp' Ψ l s (s+l)` still could not feed the
  shifted-tail reverse step without dependent target transport.  Fixed in code by changing the
  `hacc` right ledger to free-target form `∀ m, s+l=m -> ... chainComp' Ψ l s m _`.

  Genuine verified StepD progress: `exists_directedApprox` now restores the real
  `C=(comp_cov_le_unif p).choose`, keeps `B=max C 2`, proves the start-indexed `l=0` base,
  consumes both `ih s` and `ih (s+1)` in the succ branch, builds all forward peel-last geometry
  (`U₁`, `K₂`, midpoint image containment), calls `compDataFwd`, builds the reverse peel-first
  geometry (`Ψ s`, shifted tail, first-step image containment), calls `compDataRev`, and assembles
  both right-fold and left-fold closed-ball book data via `BookApproxIsoPartialData.ofParts`.
  Focused `StepDDirected.lean` verification passed; the endpoint still has the single succ-branch
  `sorry`.

  Route error #2/3 is now isolated: the current linear tolerance invariant
  `a <= 2*B*sum geometric_tail` is not strong enough for the half-composition recurrence, because
  the producer lower bound still contains `a/(1-a)`.  The next route should introduce a recursive
  tolerance ledger for `hacc` and separately prove that ledger is eventually below `ε` and `1/2`;
  do not redo the already-green geometry/half-composition structure.

- 2026-07-09 (hacc restart, route error #3/3): **PLAIN FORWARD RECURSIVE LEDGER ALSO FAILS.**
  The scalar obstruction is now precise.  Replacing the linear bound by an ordinary forward
  recurrence does not solve D1b, because the half-composition lower bound still has
  `a/(1-a)`.  With no new error at all, repeated application of `a ↦ a/(1-a)` decreases
  `1/a` by one each step, so any fixed positive base tolerance eventually blows up as `l`
  grows.  Since `reflBookData` requires `0 < a`, the current forward `l`-induction shape cannot
  produce a uniform-in-length endpoint by scalar bookkeeping alone.

  Keep the green structure: start-indexed open balls, the free-target right-fold ledger,
  `compDataFwd`, `compDataRev`, midpoint/first-step image containment, and both closed-ball
  assemblies.  The next design choice is no longer local arithmetic; it is either
  (1) target-length-indexed/backward tolerance allocation, allowing the identity tolerance to
  depend on the final composite length, or (2) a stronger book-compatible half-composition scalar
  API that avoids reapplying `a/(1-a)` to accumulated error at every peel.

- 2026-07-09 (hacc recount, new `/goal` count): **NEW COUNT STARTED; TWO ROUTES
  NOW FAILED.**  Count restarted from 0 after the previous 3/3 stop.

  Route error #1/3: target-length-indexed/backward tolerance allocation does not
  solve the current single-epsilon book recurrence.  The identity tolerance may
  be chosen with knowledge of the final length, but the public half-composition
  interface still sends any positive accumulated tolerance through `a/(1-a)`.
  That leaves no uniform `forall l` scalar ledger inside the current
  `BookApproxIsoPartialData` carrier.

  Route error #2/3: keeping `BookApproxIsoPartialData` as the carrier while
  locally strengthening the half-composition scalar API is not enough.  Live API
  audit found no partial-map carrier separating the metric-equivalence parameter
  from the tensor/covariant-derivative error parameter.  `PreApproxIsoDataOn`
  uses one `eps` for `c0_small` and `cov_deriv_small`; `BookApproxIsoPartialData`
  packages two of those at the same `eps`.  The existing same-domain
  `IsApproxIsometryOn.uniform_equiv` field is not the partial-map composition
  carrier.  In `PullbackField.lean`, `compDataFwd` and `compDataRev` already
  expose the forced lower bounds `eps/(1-eps) + eps' * max C 2` and its mirror.

  Next target for this recount: inspect whether a narrow separated-parameter
  producer can live below `BookApproxIsoPartialData` and be wrapped only at the
  endpoint.  If that requires a new carrier/design decision rather than a small
  reusable lemma, record route error #3/3 and stop with the precise API frontier.

- 2026-07-09 (hacc recount, route error #3/3): **SEPARATED-PARAMETER
  PRODUCER IS A REAL API FRONTIER.**  The narrow producer route cannot be
  expressed as a small local adapter under the current partial-map carrier.
  F5's `eps0` feed must simultaneously control the metric-equivalence parameter
  converted from `c0_small`, the old higher-order error towers, and the
  background metric-tower input.  Avoiding repeated `a/(1-a)` therefore needs a
  ledger with separate `c0` and covariant-derivative parameters, feeding F5 by
  something like `max cov (c0/(1-c0))` and only wrapping to the book epsilon at
  the endpoint.

  Current `PreApproxIsoDataOn` cannot carry that information: it stores
  `c0_small` and `cov_deriv_small` under one `eps`, and
  `BookApproxIsoPartialData` packages two such single-epsilon records.  The
  same-domain `IsApproxIsometryOn.uniform_equiv` separation is not enough
  because Step D composes partial maps and needs the supplied pullback fields,
  source/image domains, and reverse data.

  **Stop condition met for this `/goal`: 3/3 new route errors.**  Smallest next
  frontier is a deliberate partial-map separated carrier, or paired
  forward/reverse composition producers with distinct `c0` and cov parameters
  that wrap back to `BookApproxIsoPartialData` only after both ledgers are below
  the final book tolerance.  This should be designed in `PullbackField.lean`
  first, reusing the existing `partialData_comp` organs, before changing the
  `exists_directedApprox` hacc proof again.

- 2026-07-09 (separated API and hacc recount): **SEPARATED API LANDED; NEW
  COUNT REACHED 3/3 ROUTE ERRORS.**  Implemented and verified the infrastructure
  predicted by the previous frontier:
  `PreApproxIsoSep`/`BookApproxIsoSep` plus `toBook`, `toSep`, and `mono` in
  `ApproxIsometryDefs`; `compSepFwd`, `compSepRev`, and `sepData_comp` in
  `PullbackField`; and StepD scalar helpers `sepFeed`, `sepNextC0`,
  `sepNextCov`.  Focused checks passed for edited Lean files, and targeted
  module builds passed for the changed upstream modules.

  Route error #1/3: ordinary two-sided `sepData_comp` is not the D1b hacc
  replacement.  It is a valid generic separated composition wrapper, but its
  reverse half uses the ordinary inverse bracketing and puts the one-step data
  in the F5 `q` slot.  D1b must continue to use separate half producers:
  peel-last forward, peel-first reverse, then fold/germ assembly.

  Route error #2/3: a separated carrier with a single shared scalar ledger `a`
  is still the old problem.  With `c0 = cov = a`, `sepFeed a a = a/(1-a)`, so
  the covariant ledger has the same non-iterable accumulated transform.

  Route error #3/3: two ledgers bounded by the old linear geometric tail are
  still too weak.  `sepFeed c0 cov` introduces an accumulated-tail term of size
  roughly `T/(1-T)`, which the old next one-step tail increment cannot absorb.

  **Stop condition met for this `/goal`: 3/3 new route errors.**  Next target:
  a dedicated two-ledger scalar budget theorem for
  `c0_{n+1} = c0_n + δ_n*(1+q_n)`, `cov_{n+1} = q_n + δ_n*B`,
  `q_n = max (c0_n/(1-c0_n)) cov_n`, with late-start control below `ε` and
  `1/2`; then replace the single-`a` hacc invariant by separated `c0/cov` data.

- 2026-07-09 (separated scalar feasibility gate): **SCALAR LEDGER GATE GREEN;
  EXACT-ZERO BASE GREEN.**  `StepDDirected.lean` now has `reflSepData` for
  `BookApproxIsoSep K 0 0 p refl g g`, the `sepTail`/`sepBeta` API, and the
  checked scalar bounds `sepFeed_le_beta`, `sepNextC0_le`, and
  `sepNextCov_le`.  Focused verification passed; the endpoint still has the
  single expected `exists_directedApprox` `sorry`.  Gate-3 audit before editing
  the large recursion exposed the next smallest local API: exact-zero separated
  data cannot be routed through old `PreApproxIsoDataOn` adapters because those
  require `0 < eps`.  Next D1b target is therefore to add separated local
  adapters (`data_image_ball` over `PreApproxIsoSep`, separated congruence, and
  separated two-sided assembly), then replace `hacc` with the two-ledger
  invariant `c0 <= 2*sepTail` and `cov <= sepBeta B*sepTail`.  This is local API
  work, not a new mathematical obstruction.  Honest accounting unchanged:
  `exists_directedApprox` theorem remains 0% proved; its dedicated machinery is
  slightly stronger but still waiting on the separated `hacc` replacement.

- 2026-07-09 (separated `hacc` replacement complete): **D1b LOCAL RECURSION
  BODY CLOSED.**  The feasibility-first plan succeeded.  Added the separated
  local adapters in `StepDDirected.lean` (`PreApproxIsoSep.congr`/`congr_eq`,
  carrier congruence, `BookApproxIsoSep.ofParts`), restored the exact-zero base
  in the active invariant, replaced the old single-`a` ledger by distinct
  `c0/cov` ledgers bounded by `2*sepTail` and `sepBeta B*sepTail`, and assembled
  the successor from the two half-producers: forward peel-last through
  `compSepFwd`, reverse peel-first through `compSepRev`, fold equality via
  `chainComp_eq_right`, inverse germ transport via `symm_eventuallyEq_on_image`,
  then `BookApproxIsoSep.ofParts` and `.mono` from closed ball to the active
  open-ball carrier.  Focused `StepDDirected.lean` check passed with no local
  `sorry` warning.  The old commented single-ledger scaffolds were deleted.

  This was not a new route error.  One performance detour was rolled back:
  making the whole `hacc` carrier a `properMetricOpenBall` caused dependent
  elaboration/defeq blow-up, so the proof keeps the original metric-ball
  carrier and uses explicit intermediate types at the `himg_mid` boundary.

  Honest status update (2026-07-09 later): `exists_directedApprox` is locally
  proved in `StepDDirected.lean` modulo imported proof-frontier declarations.
  The separated composition organs `compSepFwd` and `compSepRev` are now proved
  in `PullbackField.lean`; do **not** restart `hacc` or re-open the scalar
  ledger route.  The remaining D1b axiom-clean blockers are the B/C-track
  `stepB1_approxIso` producer bundle and the inherited F5 uniform producer
  behind `comp_cov_le_unif` / `Lemma45F4`.

- 2026-07-09 (D6 wiring pass): **D5's last explicit connectivity input has a
  concrete producer; D6 now exports its fixed-order data, but current-tree
  verification is blocked upstream.**  `tailBall_preconn` proves positive-radius
  Riemannian balls preconnected by a near-minimizing path that stays inside the
  ball.  The proof shape passed an isolated Mathlib check.  `tailRangeExhausts`
  and `tailLimitComplete` no longer accept an external
  `PreconnectedSpace (tailBallOpen ...)` instance.

  The D2 diagonal output was also aligned with D5: `exists_chain_data` now
  chooses `j₀ >= 1`, and `exists_limits_diag` / `exists_limits_close` return
  both that bound and the already-constructed fixed-order family `D₀`.  This
  removes the need to restart the diagonal construction or reselect incompatible
  data during D6.

  Current verification did not reach `StepDLimitMetrics.lean`.  Rebuilding its
  stale dependency closure stops in
  `Tensor/RSTensor/NablaOnTensors/Regularity/Derivation.lean` at
  `nablaRSFun_eval_moving_raw`: elaboration times out at `whnf` even with a
  one-million-heartbeat diagnostic budget, and later unknown-constant errors are
  cascading consequences.  This is an upstream performance/verification wall,
  not a Step-D proof-route error.  Fresh route count remains **0/3**.

  Honest accounting: final D6 theorem remains unstated/unproved, hence **0%**;
  dedicated D6 wiring is about **15%**; whole Step-D machinery remains about
  **96%**.  Once the upstream artifact is restored, first recheck
  `StepDLimitMetrics.lean`, then prove the single next bridge: pointwise
  `metricDerivNorm` invariance for the flat
  `SmoothRiemannianMetric.restrictOpenOfSubset`.  That bridge lets the large-ball
  `lbl407` convergence restrict to the same shrunk system whose limit is proved
  complete; only then assemble the ambient CG maps and convergence.

- 2026-07-10 (D6 common-limit convergence): **the flat restriction gate and
  shrunk-tail ambient convergence are checked.**  `metricDerivNorm_flat` is
  module-checked, `tailFlatSup_lt` restricts the `l = 0` `lbl407` estimate to
  compact subsets of `tailBallOpen`, and `tailAmbientConv` supplies ambient-target
  Cheeger--Gromov convergence to exactly the same `limitPointedCoc` used by
  `tailLimitComplete`.  Focused `StepDLimitMetrics.lean` verification passed
  without warnings or new `sorry`.  Fresh route count remains **0/3**.

  Honest accounting: final D6 theorem is still unstated/unproved, hence **0%**;
  dedicated D6 wiring is about **30%**; whole Step-D machinery is about **97%**.
  Next target: inspect `MetricCompactnessInputs.metricCompactness` live fields,
  then compose the Step A and D2 subsequences/reindexing into the common
  convergence/completeness package.  Do not restart D1--D5.

- 2026-07-10 (D6 original-sequence alignment, route recount 3/3):
  `tailCenter_map` and `tailMemberMaps` are focused-check green.  The latter
  directly targets `X` at `n ↦ σ (j₀ + n)`, so maps and basepoints are no longer
  the frontier.  Three genuinely different Lean routes for reusing convergence
  failed: equality of the dependent pointed sequences; equality of maps records
  indexed by different sequences; and rebuilding `ofRestrictPullback` from a
  partial-map equality, where `MetricTargetDomain Φ k` and `MetricSourceData Φ k`
  still require full-record transport.  The failed convergence theorem was
  removed; no new `sorry` remains.  Requested stop condition: **3/3**.

  Smallest next design task: add one canonical basepoint-insensitive
  convergence/generalized-explicit-maps API, then consume `tailFlatSup_lt` with
  `tailMemberMaps`.  Final D6 theorem and conditional endpoint remain **0%**;
  dedicated D6 machinery is about **40%**; whole Step-D machinery remains about
  **97%**.

- 2026-07-10 (D6 resolution and conditional Step-D completion): the previous
  maps-indexed convergence blocker is closed by a three-part reusable API.
  `PointedRiemannianSeq.repoint` represents the transported-center tail;
  `PointedRiemannianCGConverges.unrepoint` removes the basepoint-only change;
  and `PointedRiemannianCGConverges.ofSubseq` returns to the original sequence
  index.  `tailMemberConv` consumes that chain.  `alignedProper` transports
  properness through the topology-aligned metric, and `compactness_of_b1`
  constructs the complete `MetricCompactnessConclusion`.  Focused checks and
  the targeted refreshes of the reusable producer modules passed.  Its axiom
  audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

  Honest accounting: `compactness_of_b1` is **100% proved** and dedicated D6 /
  Step-D consumer machinery is **100%**.  The working theorem
  `MetricCompactnessInputs.metricCompactness` remains **0% proved** because its
  body is still `sorry`; the textbook theorem from endpoint inputs remains 0%
  until the B/C lane constructs `StepB1RawInput`.  There is no remaining
  Step-D/F brick: follow the live B/C status in `B1_JOIN_HANDOFF.md` and
  `B1_MIN_BRANCH_RULING.md` rather than this historical coda.

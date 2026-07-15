# StepB1Producers.lean — B1 (`lbl397`) producer layer, notes

## Role
Producers for `stepB1_glue`'s inputs (`hloc`/`hinj`/`hbase`/approx-iso data) + the `lbl404`
abstract convergence endpoint.  Everything here is sorry-free/axiom-clean
(`[propext, Classical.choice, Quot.sound]`); full `lake build` green (3918 jobs, 2026-07-07).

## 2026-07-09 API correction

The false P-only `stepB1_approxIso` theorem was removed.  This producer layer now targets
`StepB1RawInput`; the checked consumer is `stepB1_of_raw`, and Step D's conditional consumer is
`directed_of_b1`.  These names reserve the textbook endpoint names for future theorems derived
from the real compactness inputs.  Producer completion remains 0%: the package makes the missing
B/C mathematics explicit but does not prove it.

Focused verification passed after the API/comment refresh.  The local unused `hη` argument of
`pullbackErrComp` was also removed; its only caller already carries the nonnegativity fact needed
for the surrounding estimate.

## Delivered (goal-session 2026-07-07, all green)

### (b) `lbl403` — CLOSED (with `Geometry/Coordinates/LocalDiffeoIFT.lean`)
- `hlocOn_of_chartNeumann` (finite order) / **`hlocOn_of_chartNeumann_infty`** (`∞` — B1's shape):
  chart-Neumann `‖id − dG‖ < 1` per point ⟹ `IsLocalDiffeomorphOn`, via the manifold forward IFT
  (incl. the `n = ∞` inverse-uniqueness upgrade in LocalDiffeoIFT).
- `chartRep_differentiableAt`: fixed-chart rep differentiable from `ContMDiffOn` (chart∘F∘chart⁻¹
  composition; needs `hFsub : F '' U ⊆` target-chart source).
- **`hlocHinj_of_chartNeumann`**: the combined `(hloc, hinj)` pair from chart-Neumann data —
  `stepB1_glue`'s exact entry (hinj via `injOn_of_fderiv_near_id` + `injOn_of_writtenInExtChart`).
- `injOn_of_dist_le` / `stepB1_hlocHinj`: metric-displacement route (now redundant for B1 but kept).

### `lbl404` — ABSTRACT LAYER 100% (the convergence route dissolves the Faà-di-Bruno wall)
**STALE-DOC finding: `COMPCONV_HANDOFF.md`/PROJECT_MAP's "lbl404 = MISSING Faà-di-Bruno brick" is
outdated — `MapCInfConvOnCompacts.comp` (parent `MapConvergenceComp.lean`) is DELIVERED (0 sorry).**
On top of it this file builds:
- `mapCInfConv_const`, `mapCInfConv_prodMk` (pair; `iteratedFDeriv_prodMk` +
  `ContinuousMultilinearMap.opNorm_prod`), `mapCInfConv_pi` (`Fintype` tuple; via own
  **`iteratedFDerivPi`** — proved by the `prodMk` trick: postcompose `ContinuousLinearMap.proj` with
  `ContinuousLinearMap.iteratedFDeriv_comp_left`, then `opNorm_pi` + `pi_norm_le_iff_of_nonneg`).
- **`averagedCInf_id`** — the `lbl404` abstract endpoint: weights `u k → u∞`, targets `v k → v∞`
  (both `MapCInfConvOnCompacts U`), all `C^∞`, pairs land in the domain `V` of the FIXED `C^∞`
  two-slot map `Φ` (chart cm), and the limit diagonal identity `Φ(u∞ y, v∞ y) = y` on `U`
  ⟹ `y ↦ Φ(u k y, v k y) → id` in `MapCInfConvOnCompacts U`.  `comp` + `prodMk` + `const` +
  `congr` (MapConvergenceDeriv).  **NO quantitative derivative-difference bounds needed** — 4th
  instance of a wall dissolving on restatement.
- C⁰/C¹ single-point engines (`norm_pair_sub_self_le`, `fderiv_pair_sub_id_le`) kept for the
  quantitative Neumann entry (lbl403's `‖dF−id‖<1` at finite k still uses the C¹ engine or the
  convergence endpoint at order 1).

### Diagonal / basepoint identities (cm-side cores)
- `centerOfMass_diag` (all-equal config ⟹ cm = the point; `centerOfMass.dist_le` at `ε = 0`),
  `chartCm_diag` (chart round-trip version), `diagEventuallyEqId` (the `=ᶠ id` `hdiag` producer
  for any total map agreeing with the chart cm on the diagonal over an open `V`).
- **`centerOfMass_delta`** ((d)-basepoint cm-core): δ-weights (only slot `i0` live) ⟹ cm = `pts i0`
  (energy at `pts i0` is 0, nonneg elsewhere, uniqueness pins).  The remaining (d) gap is ONLY the
  POU weight concentration `φ_k^α(O_k) = δ_{α0}` (`StepCAveragePOU`, other lane).

## Instantiation attack (2026-07-07, goal-round 3) — findings
- **(iii) DONE — `chartCm_contDiffOn`** (this file, `CmInfty` section, GREEN/axiom-clean): the
  `hΦc : ContDiffOn ℝ ∞` slot of `averagedCInf_id` is now produced from the C2 chain — the eight
  per-configuration hypotheses of `centerOfMass_contDiffAt` threaded `∀`-quantified over the open
  config region `V`, anchor `z₀ :=` the chart center itself.  Gotchas: needs the FULL
  `DiagExpIdentification` instance set (`RiemannianBundle` + `PseudoEMetricSpace` +
  `IsRiemannianManifold` + `CompleteSpace` ambient — `centerOfMass_contDiffAt`'s section context);
  `open scoped ENNReal` clashes with the ContDiff `∞` (drop it); the order lives in `WithTop ℕ∞`.
- **(i) STRUCTURAL: the POU weight facts are NOT derivable in-tree** — `rho` is an abstract
  parameter (`SmoothPartitionOfUnity` + `IsSubordinate`) throughout the C-track; the book's
  concrete weight formula (the `χ∘J` quotient, L1633–59) was never implemented.  Basepoint
  concentration `φ^α(O_k) = δ_{α0}` and weight convergence `φ_k → φ_∞` must enter as NEW honest
  inputs on `rho` (satisfiable via the book formula).  Do NOT rush the structure shape — it must
  match the concrete averaged-map `Φ`-shape; define it in the instantiation session (honest-input
  audit rule: shape + why-true note BEFORE consumers).
- **(ii) SHAPE GAP found AND CLOSED (same round)**: per-slot single-transition convergence is
  DELIVERED (`StepCTransitionRefine:192`), and the two-index ⇄ single-index gap is now bridged by
  TWO new green lemmas in this file: **`averagedCInf_id₂`** (the two-index `lbl397`-facing endpoint
  `∀ ε ∃ N ∀ k,ℓ ≥ N …`, hypotheses = diagonal-form convergence of weights/targets; proof = the
  `comp_cInf_id_on` contradiction/diagonalization against the single-index `averagedCInf_id`) and
  **`compDiagConvId`** (the producer of its `hu`/`hv` slots: single-index `B_k → B∞`, `A_ℓ → A∞`,
  `A∞∘B∞ = id` on `U` ⟹ every reindexed composition converges to `id`;
  `comp_tendsto_atTop` + `comp` + `congr`).  Remaining (ii) work = pure instantiation (plug the
  per-slot `normalTransition` families into `compDiagConvId`, then `mapCInfConv_pi`).
- **(ii) INSTANTIATION LAYER ALSO DONE (goal-round 4)**: **`targetsDiagConv`** (per-slot composite
  targets tuple → diagonal, = `averagedCInf_id₂`'s `hv` producer in `StepCTransitionRefine`'s exact
  output shape) and **`averagedTargets₂`** (the semi-concrete two-index endpoint: targets fully
  instantiated as per-slot `A_i^ℓ ∘ B_i^k` composites, weights atomic honest inputs, `Φ`/diagonal
  threaded; conclusion = the book's `lbl397` two-index threshold).  **Closing `lbl404` is now PURE
  DATA**: substitute the concrete `normalTransition` families (from `StepCTransitionRefine`) and
  the concrete POU weights (the missing lane) — no analysis left on the B side.
- **(i) weight-formula MACHINERY completed (goal-round 5)**: `mapCInfConv_mul` (pointwise products;
  `prodMk` + comp with global-`C^∞` multiplication) and `mapCInfConv_inv` (reciprocals of
  uniformly-below-bounded families; comp with `contDiffOn_inv ℝ` on `Ioi δ` — NOTE `𝕜` is an
  EXPLICIT arg of `contDiffOn_inv`, and dot-`.mono` fails on it).  With const/prodMk/pi/mul/inv/
  comp/congr + the two-index adapters, EVERY analytic ingredient of the book's weight quotient
  `φ^α = χ∘J⋅ψ^α∘J / (ψ⁰∘J + Σ χ∘J⋅ψ^γ∘J)` is in place.  The remaining weight work is the
  CONSTRUCTION itself: pick `ψ`/`χ` (Mathlib `ContDiffBump` + `ApproxIsometryComp.exists_bump_one_on`
  are the sources), define the quotient family, prove `sum = 1`/nonneg/denominator-positivity
  (needs a covering/positivity input shape — DESIGN DECISION) + basepoint concentration, and feed
  `mapCInfConv_*`.  That construction is the single remaining B-side brick (session-sized).
- **(i) NORMALIZED-WEIGHT LAYER DONE (goal-round 6)** — the "design decision" is DISSOLVED: the
  reusable abstraction `normWeights num i z := num i z / Σ_j num j z` now carries EVERYTHING the
  averaging consumes, with the input shape FIXED by its hypothesis slots (no design freedom left):
  `normWeights_sum` (`= 1` where the denominator is nonzero), `normWeights_nonneg`,
  **`normWeights_delta`** (basepoint Kronecker concentration — feeds `centerOfMass_delta`),
  `normWeights_contDiffOn` (`ContDiffOn.div`), and **`normWeightsConv`** (`C^∞`-on-compacts
  convergence from per-slot numerator convergence + the uniform denominator lower bound
  `δ < Σ num` — assembled from `mapCInfConv_pi` + the NEW **`mapCInfConv_clm`** (CLM
  postcomposition, summation CLM `Σ proj`) + `mapCInfConv_inv` + `mapCInfConv_mul` + `congr` on
  `div_eq_mul_inv`).  Remaining (i) work is PURE DATA: `num γ := χ∘J⁰ ⋅ ψ^γ∘J^γ` (factors:
  Mathlib `ContDiffBump` + `exists_bump_one_on`; factor convergence = comp engines on
  `StepCTransitionRefine`'s transitions; products = `mapCInfConv_mul`) and the denominator
  lower-bound fact (the covering positivity — an honest geometric input whose SHAPE is now pinned
  by `normWeightsConv.hlow`).  Gotcha: python-rewrite of the file invalidates the Edit-tool cache
  (use python for subsequent tail edits too); forward references — `normWeightsConv` must sit
  AFTER `mapCInfConv_mul`/`_inv`.
- **(i) `bumpNum` CONSTRUCTION LAYER DONE (goal-round 7)** — the book's numerators realized:
  `bumpNum χ ψ J i0 i z := if i = i0 then ψ_{i0}(J_{i0} z) else χ(J_{i0} z)⋅ψ_i(J_i z)` with
  `bumpNum_nonneg`, **`bumpNum_delta`** (cutoff vanishing at the basepoint kills every non-base
  numerator — with `normWeights_delta` + `centerOfMass_delta` the FULL `F(O_k) = O_ℓ` weight+cm
  chain is proved), `bumpNum_contDiffOn` (`ContDiff.comp_contDiffOn` + `.mul`; NB `simp [bumpNum]`
  does NOT unfold partially-applied defs — use `ContDiffOn.congr` pointwise), and **`bumpNumConv`**
  (fixed global-`C^∞` `χ`/`ψ` read along converging transition families: `comp` with a constant
  outer family on `univ` (needs `[ProperSpace E']`) + `mapCInfConv_mul`).  The full weight pipeline
  is now `bumpNum` → `normWeights` with EVERY analytic input discharged; what remains for `lbl400`
  weights is literally: pick `ψ`/`χ` = concrete `ContDiffBump` data, substitute the
  `StepCTransitionRefine` transition families for `J`, and supply the covering-positivity
  denominator bound (the one honest geometric input, shape pinned by `normWeightsConv.hlow`).
- **BOOK-MECHANISM CORRECTION (2026-07-09, superseding the old goal-round-8 reading)**:
  MSM135 Chapter 4 lines 1586–94 explicitly choose `χ = 0` in a neighborhood of the origin and
  `χ = 1` outside the base inner ball.  Hence the book-facing basepoint route is exactly
  **`bumpNum_delta`**: `J⁰(O_k) = 0` and the cutoff kills every non-base numerator.
  `bumpNum_delta'` remains a valid separation-based alternative, but it is not the mechanism used
  by the text.  Consequently `seqChartNorm_ge` is reusable alternative infrastructure rather than
  a required input for the book's basepoint identity.
- **WEIGHTS-SLOT PRODUCER DONE (goal-round 9)** — **`weightsSlot`**: the COMPLETE weight pipeline
  `w_k := normWeights (bumpNum χ ψ (J · k) i0)` (fixed `ContDiffBump` data + `k`-side transition
  families) chained `bumpNumConv → normWeightsConv → comp_tendsto_atTop` into `averagedTargets₂`'s
  exact two-index `hw` slot (weights are `k`-only, so the `ln` reindexing is vacuous).  Plus
  **`bumpNum_sum_low`**: the covering positivity reduces to "every `z ∈ U` has SOME single
  numerator `≥ δ`" (nonneg family + `Finset.single_le_sum`).  **The `lbl404` chain is now
  producer-complete end to end on the B side**: `averagedTargets₂ ∘ (weightsSlot, targetsDiagConv,
  chartCm_contDiffOn, diagEventuallyEqId/chartCm_diag)`; every remaining hypothesis is either
  concrete data (`ContDiffBump` instances, `StepCTransitionRefine` transitions) or the pinned
  covering/denominator input.  The book's basepoint identity uses the cutoff condition
  `χ(J⁰(O_k)) = 0` and `bumpNum_delta`; `bumpNum_delta'.hψ0` plus `netList_separated` is only an
  alternative route.

## Goal-rounds 9–15 (2026-07-07): the COMPLETE B-side chain, one route failure
All green/axiom-clean unless noted (`lake build` 3918 each round):
- R9 **`weightsSlot`** (full weight pipeline → `averagedTargets₂.hw`) + **`bumpNum_sum_low`**
  (covering positivity ⟸ single-numerator bound).
- R10 **`bumpNumDeltaOfNorm`** / **`bumpNumLowOfMem`** (both geometric inputs atomized to pure
  transition-norm bounds; `ContDiffBump` CoeFun needs `[HasContDiffBump E']`).
- R11 **`cmDeltaOfBump`** (basepoint chain welded end-to-end: norm-separation + own-slot
  membership + CenterInput ⟹ `cm = pts i0`).
- R12 **`edistLeOfEquivOn`** (reverse chart–metric bridge: segment + `NormalCoordMetricEquivOn`
  upper side ⟹ `eDist ≤ √2‖v‖`; WALL#0 the file-level `NormedSpace`+`InnerProductSpace`
  Module-diamond — fixed by a clean StepBInputs-matching variable set in the `PathBridge` section).
- R13 **ROUTE FAILURE #1**: the `hderiv` chain-rule atom (`segVelocityEnorm`) — three formulations
  died on the `TangentSpace 𝓘(ℝ,F)`-alias instance slot (chartJets-class wall); withdrawn, `hderiv`
  stays a pinned threaded atom for a fresh session with the slot-fighting toolkit.
- R14 **`normLowerOfSep`** ((a)-conversion: eDist lower + bridge upper ⟹ `λ/√2 ≤ ‖v‖`).
- R15 **`neumannOfDerivNorm`** (the formal `lbl404 → lbl403` interface: `mapDerivNorm 1 … ≤ ε` ⟹
  `‖id − dG‖ ≤ ε`).  Also confirmed (b)'s forward conversion is already served by
  `StepCProducers.hUx_of_sigma` (radial `√g(v,v) = dist` in-tree).

**The full B-side chain now reads**:
`weightsSlot + targetsDiagConv + chartCm_contDiffOn + diagEventuallyEqId → averagedTargets₂
→ (r ≤ 1 clause) → neumannOfDerivNorm → hlocHinj_of_chartNeumann → stepB1_glue`, with the
basepoint via `bumpNumDeltaOfNorm → normWeights_delta → centerOfMass_delta (cmDeltaOfBump)` and
the separation input via `netList_separated → realizes → normLowerOfSep`.  Remaining:
the `hderiv` atom (FAILURE#1), the conditional-endpoint assembly (`stepB1_approxIso_of_inputs`,
NetLimitData-context statement engineering), and the concrete data substitutions.

## Goal-rounds 16–18 (2026-07-07, count reset): the `(c)`/`lbl402` `C⁰` production chain
All green/axiom-clean (build 3918 each):
- R16 **`bilinPerturb`**: `|B(Av,Aw) − B(v,w)| ≤ ‖B‖·‖A−id‖·(1+‖A‖)·‖v‖‖w‖` (slot-split +
  `le_opNorm₂`).  Survey confirmed NO pullback-perturbation machinery existed in-tree — this
  starts (c), the last unstarted letter of the (a)–(d) decomposition.
- R17 **`quadPerturbTri`**: triangulated against a different base form —
  `|B₁(Av,Av) − B₀(v,v)| ≤ (‖B₁‖‖A−id‖(1+‖A‖) + ‖B₁−B₀‖)·‖v‖²`.
- R18 **`quadPerturbNeumann`**: Neumann-concretized coefficient `ε(2+ε)` (book regime `≤ 3ε`).
**The (c)-`c0` chart chain is COMPLETE**: `averagedTargets₂ (r ≤ 1) → neumannOfDerivNorm →
quadPerturbNeumann` + the `lbl394`/`lbl395` `‖B₁ − B₀‖` metric-closeness data = the pointwise
`PreApproxIsoDataOn.c0_small` bound in chart language.
Lean lessons: `abs_add` is RENAMED **`abs_add_le`**; `gcongr` beats `nlinarith` on
product-of-bounds coefficient goals (two instances) and auto-consumes context hypotheses (a
trailing `exact` after it errors "No goals").

## Goal-rounds 19–22 (2026-07-07): TENSOR-NORM BRIDGE (cross-layer brick #1) — COMPLETE mod seam (β)
All green/axiom-clean (build 3918 each):
- R19 `normSq0S_ortho`: g-orthonormal basis collapses `normSq0S_two_eq_coord`'s 4-fold sum to
  `Σᵢⱼ A(bᵢ,bⱼ)²` (δ satisfies `MetricInverseInBasis`; ite-collapse via
  `simp only [mul_ite, ite_mul, …, Finset.sum_ite_eq] + ring` — NOT `rw [Finset.sum_eq_single]`,
  whose side-goal order is a trap).
- R20 `sqrtNormSq_le_of_comp`: per-component `|A(bᵢ,bⱼ)| ≤ c` ⟹ `√normSq0S ≤ card·c`.
- R21 **`exists_gON`**: a `g`-orthonormal tangent basis exists at every point — NO instance
  surgery (`LinearMap.mk₂` wrap + `BilinForm.exists_orthogonal_basis` + `Basis.unitsSMul`
  normalization).  KEY: the lemma wants **`LinearMap.IsSymm`** (sesquilinear single-field
  structure) — the dot-notation `B.IsSymm` resolves to the WRONG (BilinForm) structure; mk₂ law
  goals come beta-unreduced (`show` first); `Units.smul_def` before `map_smul`; diagonal entry by
  explicit `inv_mul_cancel₀` calc (field_simp leaves residue).
- R22 `bilinPerturbTri`: two-slot version of `quadPerturbTri` (the `A(bᵢ,bⱼ)` shape).
**Chain**: `exists_gON` → components via `bilinPerturbTri`+`neumannOfDerivNorm` (+ metric-closeness
`‖B₁−B₀‖` data) → `sqrtNormSq_le_of_comp`+`normSq0S_ortho` → `metricTensorErrorNorm ≤ card·(…)` =
`PreApproxIsoDataOn.c0_small`.  Remaining seam (β): identify the pullback-error tensor's
orthonormal components with the chart-form values — i.e. `PullbackMetricTensorData.pullback_apply`
+ `mfderiv`-as-chart-`fderiv` (boundaryless) at the instantiation point.  That is the (c)-assembly
theorem's job (geometric hypotheses, fresh-session-sized), not a missing engine.

## Goal-rounds 22–23 (2026-07-07): seam (β) atom 1 — center-derivative identification
- R22 `bilinPerturbTri` (two-slot `quadPerturbTri`, the `A(bᵢ,bⱼ)` component shape).
- R23 **`mfderivNormalCenter`**: in normal coordinates centered at `y` and `F y`,
  `mfderiv I I F y = fderiv ℝ G 0` (`G := chart_{F y} ∘ F ∘ chart_y⁻¹`) — the two chart derivatives
  are the identity at their centers (`mfderiv_normalChartAt_self` / `_symm_zero`, both
  PRE-EXISTING in `NormalCoordinates.lean`), so the estimate transfers with no distortion.
  Hypotheses: `hG` (chart-rep differentiability at `0`) + `hev` (chart round-trip agreement near
  `y` — produced at assembly time from chart-source conditions).
  **TangentSpace-alias battle won by `ext v; rfl`**: the final `id ∘L (X ∘L id) = X` goal rejects
  `rw [id_comp, comp_id]` (alias `TangentSpace 𝓘(E) _` vs `E` is defeq-not-syntactic, motive
  fails) and stalls `simp`, but is pointwise-defeq.  This trick likely retro-solves the pre-reset
  `hderiv` FAILURE#1.
**Seam (β) remaining = ONE pointwise assembly** (`pullbackErr` at a point: `pullback_apply` +
`mfderivNormalCenter` + `bilinPerturbTri` + `exists_gON` + `sqrtNormSq_le_of_comp` +
`normSq0S_ortho`) — all engines exist, pure plumbing; then the ε-region/two-index quantified
version = the (c)-assembly theorem (fresh-session-sized, geometric hypotheses).

## Goal-rounds 24–25 (2026-07-07): **seam (β) CLOSED at the point level**
- R24 **`pullbackErrComp`** — the single-point `c0` assembly:
  `|(Φ^*h − g)(v,w)| ≤ (‖h_{Fy}‖·ε·(2+ε) + η)·‖v‖‖w‖` from the normal-chart Neumann `ε` and the
  POINTWISE metric closeness `η`.  Five engines chained: `pullback_apply` → `mfderivNormalCenter`
  (per-vector `DFunLike.congr_fun`, avoids the rw-motive alias trap) → `bilinPerturb` + inline
  triangle + Neumann concretization (`gcongr`).
  **Two structural findings**: (1) the metric-closeness hypothesis MUST be pointwise-scalar
  (`∀ v' w', |gn.inner (F y) v' w' − gk.inner y v' w'| ≤ η‖v'‖‖w'‖`) — the operator-norm mixed
  difference is type-illegal across the `TangentSpace` aliases (`HSub` synth fails; ascription
  does not unify) — and this is anyway closer to `lbl394/395`'s output; (2) the Tensor0S
  `attribute [-instance]` scrub KILLS the CLM-norm instances — scrub only `RiemannianBundle`-letI
  theorems.
- R25 `chartRoundTrip_ev` — the `hev` producer from eventual chart-source membership (openness +
  continuity at assembly time); coercion heads bridged by `show … from left_inv`.
**(c)-c0 status: single-point chain closed END-TO-END** (`chartRoundTrip_ev` → `pullbackErrComp`
→ `exists_gON` + `sqrtNormSq_le_of_comp`/`normSq0S_ortho` → `metricTensorErrorNorm` bound).
Remaining (c): the region/two-index ∀-wrapper + the `hG`-differentiability and Neumann/η input
production from the C-track convergences (the (c)-assembly session) + higher-order
`cov_deriv_small` (pinned).

## Goal-round 26 (2026-07-07): **(c)-c0 TOP single-point theorem `pullbackErrNorm` — DONE, axiom-clean**
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no sorryAx) for
`pullbackErrNorm` / `mfderivNormalCenter` / `exists_gON`.
- **`exists_gON_bd`** — coercivity-bounded orthonormal basis: from `cLow·‖v‖² ≤ g(v,v)` (the book's
  `λ`-equivalence / `lbl395` lower bound) the gON vectors satisfy `‖bᵢ‖ ≤ (√cLow)⁻¹`.  Tail proof:
  `inv_eq_one_div` + `le_div_iff₀ hs` + `nlinarith [h1, hsq, sq_nonneg (‖bᵢ‖·√cLow − 1)]` — the
  sqrt-rewrite chain route stalled; nlinarith with the completed-square hint wins.
- **`pullbackErrNorm`** — the top single-point `c0` bound:
  `metricTensorErrorNorm (Φ^*h) g y ≤ dim · (‖h_{Fy}‖·ε·(2+ε) + η) · cLow⁻¹`, welding
  `exists_gON_bd` + `pullbackErrComp` + `sqrtNormSq_le_of_comp`.  GOTCHAS: `metricTensorErrorNorm`
  wants the BARE `hpb.pullback` (already a `Tensor0SField`), not the eta-expansion; and
  `sqrtNormSq_le_of_comp` produces `card (Fin n)` not `n`, so state the bound as a `have hmain`
  and finish with `simpa using hmain`.
**(c)-c0 SINGLE-POINT LANE COMPLETE**: `chartRoundTrip_ev` → `pullbackErrNorm` is a fully-proved,
axiom-clean chain from honest chart-Neumann (`ε`), pointwise metric-closeness (`η`), and coercivity
(`cLow`) inputs to the `PreApproxIsoDataOn.c0_small` fiber-norm bound.  Remaining (c): the
region/two-index ∀-wrapper + production of the `hG`/`ε`/`η`/`cLow` inputs from the C-track
convergences (the (c)-assembly session) + higher-order `cov_deriv_small` (pinned).

## Goal-round 27 (2026-07-07): **`preApproxIsoDataOn_zero` — the C⁰ carrier endpoint, DONE**
The `p = 0` `PreApproxIsoDataOn` is now producible end-to-end.  With `p = 0` the `cov_deriv_small`
obligation is VACUOUS (`1 ≤ a → a ≤ 0` impossible — closed by `omega`, which derives `False` from
the contradictory Nat hyps and closes the real-valued goal), so the full carrier assembles from:
`hpb` (PullbackMetricTensorData) + `hsmooth` (ContMDiffOn K) + the `ε` bounds + the uniform
`hc0 : ∀ x ∈ K, metricTensorErrorNorm hpb.pullback g x ≤ ε` — the last being exactly the conclusion
of `pullbackErrNorm` quantified over `K`.  `pullback_apply` slot filled directly by
`hpb.pullback_apply` (global, restricts to `K`).  First-try green, axiom-clean.
**This welds rounds 16–26 into the actual Step B carrier at order 0.**  The remaining gap to a
`p ≥ 1` carrier is purely the higher covariant-derivative estimate `cov_deriv_small`
(`tensor02CovDerivNormWith a`), which is the pinned `hderiv`/higher-order lane — genuinely harder
(iterated `∇` of the pullback error), fresh-session-sized.  The `ε`-uniformity of `hc0` over a
compact `K` (sup of the per-point `pullbackErrNorm` bounds `< ε`) is the (c)-assembly session's
compactness obligation.

## Goal-round 28 (2026-07-07): **`bookApproxIsoData_zero` — the two-sided `lbl397` C⁰ carrier, DONE**
The canonical two-sided partial approximate-isometry carrier `BookApproxIsoPartialData … 0 Φ g h`
now assembles from a forward + reverse `preApproxIsoDataOn_zero` (on `K` and `Φ '' K`) plus
`source_sub : K ⊆ Φ.source`.  Green.  Instance note: `BookApproxIsoPartialData` demands on the
TARGET `N'` the full `[T2Space] [SigmaCompactSpace] [IsManifold I (∞+1)]` set (mirrors
ApproxIsometryDefs' N section) AND `[IsManifold I (∞+1) M']` on the source — add these to the local
`N'` binder.  This is the C⁰ endpoint the Step B / `lbl397` glue consumes.

## Goal-round 29 (2026-07-07): ⭐ **`stepB1_zero` — the order-0 B1 (`lbl397`) ENDPOINT, DONE**
First-try green, axiom-clean (`[propext, Classical.choice, Quot.sound]` for
`stepB1_zero`/`bookApproxIsoData_zero`/`preApproxIsoDataOn_zero`).  The full B1 conclusion at
`p = 0` now closes from honest chart-level inputs:
- inputs: `F` a local diffeo on open `U` + `InjOn F U` + basepoint fix, and the FORWARD + REVERSE
  `C⁰` pullback-error bounds on `closedBall Ok r` and its image;
- output: `∃ Φ : PartialDiffeomorph, closedBall ⊆ Φ.source ∧ Φ Ok = Oℓ ∧
  Nonempty (BookApproxIsoPartialData … 0 Φ g h)` — exactly the `lbl397` skeleton's conclusion.
- proof: one call to the fully-proved `stepB1_glue`, feeding `preApproxIsoDataOn_zero` for both
  `hfwd` and `hrev`.
Placed in a fresh `section StepB1Zero` with `M''`/`N''` carrying the union of CmDiag's 8 instances
(needed to instantiate `preApproxIsoDataOn_zero`) + glue's `[MetricSpace M''] [Nonempty M'']` +
`[IsManifold I (∞+1) ·]`.  NO metric/Riemannian instance diamond (CmDiag's `M'` had no pre-existing
metric-space instance, so adding `MetricSpace` is fresh).
**B1 at order 0 is COMPLETE end-to-end.**  The gap to the full `lbl397` (any `p`) is exactly the
higher covariant-derivative `cov_deriv_small` (`tensor02CovDerivNormWith a`, `a ≥ 1`) — the pinned
higher-order lane — plus, on the input side, producing `hloc`/`hinj` (have: `hlocHinj_of_chartNeumann`)
and the uniform `hc0` bounds (the (c)-assembly compactness obligation) from the C-track.

## Goal-round 30 (2026-07-07): DEDUP + the p≥1 cov_deriv frontier, precisely scoped
- **DEDUP**: round-21 `exists_gON` was a verbatim duplicate of the pre-existing
  `DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis`
  (`Geometry/Curvature/RicciOperatorNormBound.lean:38`, already in the transitive import closure).
  Deleted; `exists_gON_bd` now obtains from the canonical (full-qualified name — cross-namespace).
- **p≥1 cov_deriv (`cov_deriv_small` for `a ≥ 1`) — CORRECTION: substantially BUILT, NOT blocked.**
  An earlier note here (retracted) called this "blocked below missing Christoffel-vanishing API".
  That was WRONG — based on grepping only `Tensor/` and `Geometry/` and MISSING
  `C4/PullbackField.lean`, which is the actual home of the p≥1 machinery.  The FALSE-wall lesson
  (grep the canonical producer FILE, incl. the C4 sibling, before declaring a frontier).  Present:
  `Tensor0SBundle.nabla_metric_zero` (∇g=0, the tensor-level metric compatibility — EXISTS, used
  across ScalarBochner/AllTimesBounds/PullbackField); `iterCov_metric_zero` (`∇^a g = 0`, a≥1,
  PullbackField:487); `iterCov_sub` (cov-deriv linearity over `−`, :516); `covDOF_zero` (:529);
  **`covNormWith_pd_zone` (:272) = pullback-INVARIANCE of `tensor02CovDerivNormWith`** (source
  cov-deriv norm = target cov-deriv norm at `Φ x`); norm bridges `t02Norm_eq_iterCov` (:542),
  `inner_le_of_c0` (:571), `sqrt_normSq_two_le` (:617); `partialData_comp` (:667); the mono/monoP
  order-lemmas (:1561–1605).  The pointwise normal-coordinate / Christoffel-vanishing route is NOT
  needed — the pullback-invariance route transports cov-deriv bounds from the (identity-comparison)
  target, exactly as `metricDerivNorm_pullback` does for the metric side.  REMAINING p≥1 work =
  wiring these into a general-`p` `PreApproxIsoDataOn`/`stepB1` endpoint (mirroring the p=0
  `preApproxIsoDataOn_zero`/`stepB1_zero`) — this is PullbackField.lean's active lane; coordinate
  with it, do not duplicate.

## Goal-round 31 (2026-07-07): ⭐ **B1 endpoint GENERALIZED to any order `p` (`_of_bounds` family)**
Now that the p≥1 cov_deriv infrastructure is known to exist (`PullbackField.lean`), the whole p=0
carrier chain generalizes trivially by turning the vacuous `cov_deriv_small` into a hypothesis slot:
- `preApproxIsoDataOn_of_bounds` (any `p`; `hcov : ∀ a, 1≤a→a≤p→ ∀ x∈K, tensor02CovDerivNormWith a
  hpb.pullback g g x ≤ ε`) — `preApproxIsoDataOn_zero` is now its `p=0` wrapper (vacuous `hcov` by
  `omega`).
- `bookApproxIsoData_of_bounds` (two-sided, any `p`, forward+reverse `hcov`) — `_zero` wrapper.
- **`stepB1_of_bounds`** (the B1 `lbl397` endpoint at ANY `p`) — `stepB1_zero` is its `p=0` wrapper.
All green, axiom-clean.  The B1 conclusion `∃ Φ, … Nonempty (BookApproxIsoPartialData … p Φ g h)`
now closes at every order `p` from: chart-level `hloc`/`hinj`/basepoint + forward/reverse `C⁰`
(`hc0`) and `C^p` covariant-derivative (`hcov`) bounds.  The `hcov` inputs are produced by
`PullbackField.lean`'s pullback-invariance machinery (`covNormWith_pd_zone` transports them from the
identity-comparison target) — that is its active lane; the endpoint here CONSUMES them honestly.

## Goal-round 32 (2026-07-07): norm-bridge attempt — ROUTE FAILURE #1 (whnf performance wall)
The connector `tensor02CovDerivNorm_eq_metric`
(`tensor02CovDerivNormWith a (metricTensorField h) g g x = metricCovDerivNorm a h g x`) would feed a
`metricCovDerivNorm` bound (from `metricDerivNorm_pullback` invariance) into the
`tensor02CovDerivNormWith`-shaped `hcov` of `stepB1_of_bounds`.  Mathematically trivial (both sides
= `√(normSq0S g x (2+a) (iterCov g 2 (metricTensorField h) a x))` via `t02Norm_eq_iterCov` /
`metricCovDerivNorm_eq_iterCov` at a gON basis).  **But hits a `whnf` timeout at
maxHeartbeats 1000000 across 3 tactics** — the two heavy tensor-instance iterExprs are expensive to
unify.  `PullbackField.lean` (now Codex's lane per the 2026-07-07 migration) works at the iterCov
level directly to avoid this; the bridge should be owned there, not forced via the direct route.
File deleted, not left in the tree.

## Three cross-layer bricks remain (historical 2026-07-07 snapshot)
1. **tensor-norm bridge**: `metricTensorErrorNorm`/`normSq0S` (= `inner0S`, fiber metric layer)
   ↔ the chart bilinear-form `|·|` of `quadPerturbNeumann` — Tensor0S component/orthonormal-basis
   plumbing (`Tensor0SMetric.lean` stack).
2. **`hderiv` atom** (FAILURE#1 of the pre-reset count): the `mfderiv(exp∘(·•v))` chain-rule +
   enorm identification — TangentSpace-alias instance-slot fight (chartJets toolkit).
3. **conditional endpoint** `stepB1_approxIso_of_inputs`: the NetLimitData-context input-bundle
   statement + assembly of the now-complete chains (MetricCompactnessInputs precedent).

## What lbl404 still needs (instantiation layer, all gated outside this file)
(i) POU weights: convergence `φ_k → φ_∞` + basepoint concentration (StepCAveragePOU lane);
(ii) targets per-slot convergence `v_α k → diag` (instantiate `comp_cInf_id_on` on the concrete
`J`-transitions; C⁰ base = `stepCJoin`); (iii) `Φ_cm` as `ContDiffOn ∞` on an open config region +
the `CenterInput` family (from the C2 `centerOfMass_contDiffAt` chain + `contDiffOn_infty`; the
quantitative variant additionally awaits the lbl430-bounds brick `j ≥ 2`).
  Bridge recipe (names verified): `contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s`
  (Mathlib ContDiff/Defs:532) + per-order `(centerOfMass_contDiffAt … n …).contDiffWithinAt` at each
  point of the open config region (StepCSmoothness:900; threads CmHessianInput/StrictDistInput/
  smallness per configuration).

## Lean lessons (this file)
- Tensor0SBundle instance shadow: any theorem touching `RiemannianBundle`/`TangentSpace` instances
  needs the `attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in` prefix (StepCSmoothness pattern) — without it the
  `letI RiemannianBundle` fails synth and everything downstream cascades (`this` vs named-instance
  `dist` mismatches are the SYMPTOM, not the cause).
- `riemannianEDist_self` lives in namespace `Manifold` (Mathlib PathELength).
- `centerOfMass.dist_le`-style letI-typed hypotheses: prove under your own identical `letI` block;
  defeq acceptance works (the eq_of_all_eq precedent).
- Pi difference is `rfl` (`(f - g) = fun y i => f y i - g y i`); `simp [Pi.sub_apply]` "no progress".
- `MapCInfConvOnCompacts.comp` needs `[ProperSpace F]` on the middle space — carry
  `[ProperSpace (P × Q)]` as instance hypothesis in the abstract endpoint.

## 2026-07-09: radial separation brick closed

The historical item 2 above is now closed at the correct layers:

- `GaussLemmaPullback.mfderiv_exp_radial` is the public one-dimensional radial chain rule.
- `StepBInputs.radialEnorm_normal` turns it into the exact `normalCoordMetric` extended-norm
  equality formerly threaded as `hderiv` by `edistLeOfEquivOn` / `normLowerOfSep`.
- `normLowerOfSepExp` specializes the generic distance estimate to the actual radial exponential
  curve.  From segment containment in the named exponential ball and a Riemannian-distance lower
  bound, it directly produces `lam / sqrt 2 ≤ ‖v‖`; both `C¹` regularity and the velocity identity
  are now discharged internally.

Focused checks passed for the exponential layer, `StepBInputs`, and the full
`StepB1Producers` file; the two upstream modules were refreshed successfully.
The targeted `StepB1Producers` module refresh exceeded the tool wall-clock twice (the longer
attempt reached three minutes) without emitting a Lean diagnostic; the focused full-file check
remains the successful proof verification for this edit.

Honest progress accounting: this radial separation sub-brick is 100% complete.  The proposed
producer theorem constructing `StepB1RawInput` is still unstated/unproved (0%), and therefore the
textbook B1 theorem is still 0%; its dedicated machinery remains about 50%.  Step B overall stays
about 50%, Chapter-4 machinery stays about 59–60%, and the conditional Theorem 3.9 endpoint stays
0%.  The next real B/C producer frontier is concrete finite-hat/POU instantiation (including
basepoint concentration) plus the uniform all-order bounds, not another radial derivative lemma.

## 2026-07-09: concrete net-center chart separation

The good-covering-to-weight chain now reaches the exact Euclidean norm bound:

- `GoodCoveringSeq.seqCenter_zero`, `seqCenter_dist_ge`, and
  `seqCenter_edist_ge` expose the base slot and `lambda D 0` separation for a
  nonzero live sequence center.
- `seqChartNorm_ge` combines that concrete Riemannian separation with
  `normLowerOfSepExp`, the normal-chart round trip, and the named exponential
  ball containment.  Its conclusion is the `lambda D 0 / sqrt 2 <= norm J`
  estimate immediately preceding `bumpNumDeltaOfNorm.hfar`.

Focused checks passed for `GoodCoveringSeq` and the full `StepB1Producers`
file; the missing `StepCAveragePOU` artifact encountered downstream was
refreshed successfully.  The `GoodCoveringSeq` exported module refresh also
passed.

Precise remaining design gap: `StepCProducers.stepCJoin` consumes an arbitrary
bundled `SmoothPartitionOfUnity rho`, while the book-weight convergence and
basepoint concentration chain in this file is built for the explicit chart
family `normWeights (bumpNum ...)`.  No theorem currently constructs a global
`SmoothPartitionOfUnity` whose chart readouts are those explicit weights, and
`normWeights`/`bumpNum` occur nowhere outside this file.  Closing this requires
one deliberate interface choice: construct the special global POU (including
extension-by-zero, subordination, and denominator positivity), or generalize
the Step-C averaging consumer to an explicit smooth/nonnegative/sum-one/
subordinate weight package.  Do not hide this mismatch behind a new weight
concentration hypothesis.

Honest accounting remains unchanged at the rounded scale: the new sequence
separation machinery is complete, but the `StepB1RawInput` producer and the
textbook B1 theorem remain 0%; Step-B dedicated machinery is about 50%,
Chapter-4 machinery about 59--60%, and the conditional Theorem 3.9 endpoint 0%.

## 2026-07-09: explicit-weight interface decision

The preceding interface choice is now resolved in favor of a lightweight
`centerAverage.WeightDataOn` consumer bridge, while retaining the bundled POU
entrypoints as compatibility wrappers.  This is forced by two live facts:

- the averaging core uses only pointwise nonnegativity, a positive slot,
  sum-one, and active-set membership; it does not consume global POU smoothness;
- MSM135 makes the explicit weights subordinate to the radius-`5 lambda`
  `B_k^alpha`, whereas the existing `StepCPartition.hatBall` is the
  radius-`4 lambda` covering ball.  Packaging the book weights as the current
  hat-subordinate `SmoothPartitionOfUnity` would assert the wrong support.

The book-mechanism audit also corrected the old goal-round-8 note: Chapter 4
chooses `chi = 0` near the origin, so `bumpNum_delta` is the actual basepoint
route.  `bumpNum_delta'`, `bumpNumDeltaOfNorm`, and `seqChartNorm_ge` remain
valid separation-based alternatives, not required book inputs.

The explicit package bridge has now landed and passed focused verification.
`normWeights_pos` supplies the positive slot from nonnegative numerators and a
nonzero denominator; `num_ne_of_weight_ne` reduces active membership of a
normalized weight to active membership of its numerator; `normWeights_data`
assembles the generic `WeightDataOn`; and `bumpWeights_data` specializes it to
`normWeights (bumpNum ...)`.  Denominator positivity and
numerator-support-to-active-ball membership remain visible geometric inputs.

The concurrent `StepB1ApproxIso` cleanup removed C-track transitive imports, so
this producer now imports its actual dependencies (`StepBInputs`,
`GaussLemmaPullback`, `StepCAveraging`, `StepCSmoothness`, and `GoodCoveringSeq`)
directly.  In particular, the owner of `radialCurve_contMDiffAt2` is no longer
reached accidentally through the C-track import closure.  The first
two verification attempts encountered transient missing `.olean` files while
those concurrently edited upstream modules were rebuilding; after the named
artifacts stabilized, the full focused file check passed.

Honest rounded accounting is unchanged: `StepB1RawInput` producer 0%, textbook
B1 theorem 0%, Step-B dedicated machinery about 50%, Chapter-4 machinery about
59--60%, and the conditional Theorem 3.9 endpoint 0%.

## 2026-07-09: book-cutoff denominator reduction

Added `bumpNum_sum_one`.  It isolates the two geometric cases in the MSM135
basepoint modification: where the cutoff is `1`, an ordinary covering inner
bump gives a unit numerator; where the cutoff is not `1`, membership in the
base slot's inner bump gives the uncut base numerator `1`.  Nonnegativity then
raises this to a lower bound of `1` for the full modified numerator sum.

This does not assume the missing geometry.  The remaining concrete producer
must still prove that the ordinary inner bumps cover and that the cutoff's
non-one locus lies inside the base inner bump.  Focused verification passed
after the stale upstream artifacts in the shared build tree were refreshed.

The rounded accounting remains unchanged: this closes the algebraic
denominator reduction, not the `StepB1RawInput` producer or textbook B1
theorem; both remain 0%.

## 2026-07-13 finite-Pi calculus extraction

The generic `iteratedFDerivPi` proof was moved to
`Analysis/Calculus/PiDeriv.lean` as `iteratedFDeriv_pi`. This file now imports
and consumes the lower-layer theorem; no Step-B1 producer statement changed.
Focused verification passed.

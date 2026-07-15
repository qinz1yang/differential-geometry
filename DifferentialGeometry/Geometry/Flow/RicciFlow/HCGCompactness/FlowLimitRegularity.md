# FlowLimitRegularity — the `hsmooth` brick (joint (t,x) C^∞ of the AA limit `gInf`)

Route + status note for the LAST hard input of `isSolutionOn_of_reg` (FlowLimitBuild.lean):
`hsmooth : MetricFamilySmoothOn D {base := {metric := gInf}}.family`.
Planned producer: `metricFamilySmoothOn_of_pde` (this brick; multi-session).

## Findings that fix the architecture (2026-07-03 session)

1. **The ⊤-bug is FIXED.**  `MetricFamilySmoothOn` (MetricFamily.lean:545) now reads `∞`:
   `coeff` is `ContDiffOn ℝ ∞` on `D.regular`, `frameCompSmooth` takes a
   `IsLocalFrameOn I E (∞ : WithTop ℕ∞)` frame and concludes `ContMDiffOn … ∞` on
   `D.regular ×ˢ u`.  The held ⊤→∞ cascade was applied; no blocker here.
2. **ESR (`Evolution/ExtendedSolutionRegularity.lean`) reduces all 4 fields to chartGram
   data** via `metricFamilySmoothOn_of_chartGram`: inputs = chartGram joint `C^∞`
   (`ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ) ∞` of `chartGramMatrix (g t) x₀ x i j` on
   `Ioo a b ×ˢ baseSet x₀`) + chartGram joint `C⁰` on `Ico a b ×ˢ baseSet`.  Reuse
   blockers: whole file under `[CompactSpace M]` (proof bodies do NOT appear to use it —
   the file sets `linter.unusedSectionVars false`, so this is unaudited; the chain
   `metricCLMSection_jointContMDiffOn_of_chartGram` (ConjugatingFlowProperties.lean:3570)
   + private `inCoordinates_metric_eq_chartGram_sum` needs an `omit`-and-rebuild audit)
   and `closedOpen a b`-hardcoding (the HCG endpoint `X.D` is a GENERAL
   `RealTimeInterval`).  `metricTensorCont_of_chartGram`
   (Curvature/Realized/MetricFamilyContinuity.lean:177) is already compactness-free and
   time-set-general.
3. **`chartGramMatrix g α x i j = g.inner x (chartBasisVecFiber α i x) (… j x)`** (rfl,
   ChartGram.lean:217) — so `metricLimit_pde` (LimitSolutionEquation.lean:213, HasDerivWithinAt
   `−2·ricciTensor` on `Icc β ψ`, pointwise in `(x, v, w)`) applies VERBATIM to chartGram
   entries, and `ricciChartFrameComp_jointContinuousOn`
   (RicciContinuityInMetricTime.lean:1266) is exactly the joint-continuity producer for the
   PDE right-hand side, from inputs h0/h1/h2 = joint continuity of the spatial chart-jets
   of `gInf` of orders ≤ 2.
4. **Brick 5 supplies** (windowGInfAll_pt, MetricPreconvWindowAllPt.lean:100): ∀ compact K,
   ∀ order p, ∀ ε > 0, tail-uniform smallness `metricDerivNorm a (gSeq(φ k) t) (gInf t) gRef x < ε`
   uniformly over `t ∈ Icc β ψ`, `a ≤ p`, `x ∈ K`.  Each `gInf t` is a
   `SmoothRiemannianMetric` (per-time spatial C^∞ is free).  The sequence terms are
   jointly smooth on windows (they carry `IsSolutionOn`, locally, through the Brick-4/5
   bump-extension identification).
5. **The analytic kernel Mathlib lacks is now BUILT and VERIFIED**:
   `Analysis/Calculus/TimeSliceBootstrap.lean` — `hasFDerivAt_of_slice` (joint
   differentiability from time-slice PDE + continuous RHS + spatial slice),
   `contDiffOn_succ_of_pde` (step: R, W jointly C^q ⟹ G jointly C^{q+1}),
   `contDiffOn_one_of_pde` (first bootstrap step, joint C¹),
   `contDiffOn_inf_of_pde` (C^∞ from jointly-C^∞ R, W).  Codomain-generic (applies at
   every jet level).
6. **Route ruling**: limit-side PDE bootstrap (option 3 of the plan's REGULARITY-ROUTE
   NOTE).  Spacetime-AA (the book's route) is heavier: the formalized eq-(3.4) layer
   (`covOrderBound_of_soln`, RicBound.lean) bounds SPATIAL covariant orders only — mixed
   `∂ₜ^q∇^p` sequence bounds are NOT formalized, so sequence-level AA would need new
   bound infrastructure AND the same conversion/jets machinery.

## The bootstrap (chart-scalar level) — statement chain

Fix a chart anchor `α`, `J` an open interval inside a window interior
(`Icc β ψ ⊆ D.carrier`, `J ⊆ Ioo β ψ ∩ D.regular`), `V ⊆ interior (extChartAt I α).target`
open.  Let `G i j : ℝ × E → ℝ`, `G i j (t,y) := chartGramOnE (gInf t) α i j y` and
`R i j (t,y) := −2 · (chart Ricci of gInf t)`, so that (metricLimit_pde + rfl-bridge (3))
`∂ₜ G = R` pointwise (HasDerivAt at interior times via `Icc_mem_nhds`).

Jets: `W_k[i,j] (t,y) := iteratedFDeriv ℝ k (fun y' => G i j (t, y')) y`.

- **A(0) (the C⁰ layer)**: ∀ k i j, `W_k[i,j]` jointly continuous on `J ×ˢ V`.
  Source: locally-uniform convergence of the spatial chart-jets of `gSeq → gInf`
  (from Brick 5's covariant smallness + a locally-uniform covariant→chart-jet
  conversion) + joint continuity of the sequence jets (sequence flows jointly smooth).
  - Order 0 needs NO conversion tower: Cauchy–Schwarz `abs_apply_le_sqrt_normSq0S`
    gives `|chartGram_u − chartGram_{u'}|(x) ≤ metricDerivNorm 0 u u' gRef x ·
    ‖frame_i‖_gRef ‖frame_j‖_gRef` with the frame-norm factor CONTINUOUS in x (hence
    locally bounded) ⟹ locally-uniform convergence ⟹ `metricTensor_cont` + `coeff_cont`
    (the C⁰ half of `MetricFamilySmoothOn`).
  - Orders 1, 2, …: SUB-FRONTIER (a): the conversion `jet2Diff_le_dNorm`
    (RicciFromJets.lean:830) is anchored at a single point `x` (`extChartAt I x x`); the
    bootstrap needs constants locally bounded in the base point (neighborhood version of
    the P3 tower conversion, or a re-derivation at chart level).  This is bounded work,
    not a wall: the constants are built from finitely many continuous frame/gRef data.
- **A(q) ⟹ A(q+1)** (apply `contDiffOn_succ_of_pde` AT EACH JET LEVEL k):
  - spatial partial of `W_k` = curry-reshuffle of `W_{k+1}` (Mathlib
    `iteratedFDeriv_succ_eq_comp_left`), ContDiffOn q by A(q) at k+1;
  - time partial of `W_k` = `jet_k R` needs:
    - **SUB-FRONTIER (b), the SWAP**: `HasDerivAt (s ↦ W_k (s,y)) (jet_k R (t,y)) t`.
      Route: FTC representation `G t y = G t₀ y + ∫_{t₀}^t R s y ds` (from the pointwise
      PDE + continuity of R in s), then differentiate under the interval integral in `y`
      (`intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip`, dominated via
      continuity on compacts), then FTC again.  Induct on k.  One dedicated file
      (`TimeSliceSwap.lean`-shaped, next to TimeSliceBootstrap).  Standard, bounded.
    - **SUB-FRONTIER (c) — THE WALL**: ContDiffOn q of `(t,y) ↦ jet_k R` for ALL k, given
      A(q).  R is ALGEBRAIC in `W_0, W_1, W_2` and `invGram`:
      `chartRicciTensor_eq_secondOrder_add_firstOrder` (RicciDiffAffine.lean:163),
      `chartChristoffel = ½ invGram·(∂g-combos)`, `∂(invGram) = −invGram·(∂g)·invGram`.
      For k = 0: pure CLM/product/inverse algebra — ContDiffOn q by `ContDiffOn.mul/add` +
      matrix-inverse smoothness; NO wall.  For k ≥ 1: functional Leibniz/Faà-di-Bruno for
      `iteratedFDeriv` of products/composites at ALL orders.  Options:
      (i) Mathlib `FaaDiBruno.lean` (`HasFTaylorSeriesUpToOn.comp`,
      `FormalMultilinearSeries.taylorComp`): jets of the composite are `taylorComp`
      entries = continuous-multilinear algebra in the factor jets — clean but a real
      formalization sub-project; (ii) functional Leibniz for `iteratedFDeriv` of products
      (check for `iteratedFDerivWithin_mul`-shape in current Mathlib) + the finite
      recursion for `jet_k invGram`; (iii) restate A(q) with jets replaced by an
      inductively-generated closed family.  DECIDE when reached; this is the one place a
      GPT-Pro consult may be warranted.
- **Endpoint**: A(q) ∀ q at k = 0 gives `ContDiffOn ℝ ∞ G (J ×ˢ V)` (`contDiffOn_infty`);
  alternatively finish with `contDiffOn_inf_of_pde` once hR/hW are jointly C^∞.

## Back-transfer and assembly

- Chart-level → manifold: `ContDiffOn.comp_contMDiffOn` with
  `(t,x) ↦ (t, extChartAt I α x)` (C^∞ on the chart source), then
  `chartGramOnE ∘ extChartAt = chartGramMatrix` on the source (`PartialEquiv.left_inv`).
  This is the REVERSE of ESR's `chartGramOnE_jointContDiffOn` and dodges its
  product-manifold `whnf` wall (composition INTO the model, never out of it).
- Localization: `D.regular` is an arbitrary open ⊆ ℝ — cover by `Ioo`s; `ContMDiffOn` and
  the field statements are local, so the `Ioo`-windowed bootstrap glues
  (`contMDiffWithinAt` is local in both factors).  Windows `Icc β ψ ⊆ D.carrier` around
  each regular time come from `regular_mem_nhds`.
- 4-field assembly: mirror `metricFamilySmoothOn_of_chartGram` WITHOUT `[CompactSpace M]`
  on general `D` (new builder in this file's .lean, or de-compactify ESR by `omit` after
  the audit).  `coeff` = time-slice of the joint statement (ESR's CLM-section recipe);
  `coeff_cont`/`metricTensor_cont` = the C⁰ layer (compactness-free
  `metricTensorCont_of_chartGram` already fits); `frameCompSmooth` =
  `metricFrameComp_jointContMDiffOn_of_chartGram`-analogue (CLM-section gate + 
  `clm_bundle_apply₂`).

## Session ledger

- 2026-07-03: architecture fixed (this note); analytic kernel
  `TimeSliceBootstrap.lean` LANDED + VERIFIED (4 endpoints axiom-clean) — the first
  bootstrap step (joint C¹ from continuous partial data + PDE) and the parametrized
  induction step are proved; C^∞ endpoint proved modulo jointly-C^∞ inputs.
  Remaining sub-frontiers: (a) neighborhood-uniform covariant→chart conversion
  (bounded), (b) the swap lemma (bounded, standard), (c) jets-of-algebra closure (the
  wall — route options listed above), plus the compactness/general-D plumbing of the
  ESR reduction (audit + omit, bounded).
- 2026-07-03 (same session): **C⁰ layer order-0 LANDED + VERIFIED**
  (`FlowLimitRegularity.lean`, targeted build green, all 4 endpoints axiom-clean, no
  sorry): `chartGram_sub_le` (anchor-free CS difference bound; the CS factor =
  `gRef`'s own chart-Gram diagonal), `chartGramBound_contOn`, `chartGramLim_contOn`
  (the locally-uniform-limit transfer; compact-neighborhood-in-baseSet +
  `TendstoUniformlyOn.continuousOn` + `mono_of_mem_nhdsWithin`), and the endpoint
  `metricTensorContLim` = the `Tensor0SFamilyContinuousOnSet` package for `gInf` on a
  window — the `metricTensor_cont` field (and `coeff_cont` by evaluation) of
  `MetricFamilySmoothOn`, i.e. the C⁰ HALF of `hsmooth`, from honest Brick-5-shaped
  inputs (`hconv` order-0 + per-k joint chartGram continuity).  Gotchas: EVT is
  `IsCompact.exists_isMaxOn` (+`isMaxOn_iff`); `TendstoUniformlyOn.continuousOn` takes
  `∃ᶠ` (use `.frequently`); `ContinuousWithinAt.mono_of_mem_nhdsWithin` (renamed);
  `omit`/`set_option … in` must PRECEDE the docstring; the `[IsManifold I (∞+1) M]`
  linter-vs-omit disagreement is resolved by declaring the lemma before that
  `variable` line.  A(0) at orders ≥ 1 (jets) still needs sub-frontier (a).

## Honest size estimate

C⁰ layer order-0 ≈ 1 session; conversion (a) ≈ 1–2; C¹ instantiation for gInf ≈ 1 (after
(a)); swap (b) ≈ 1; wall (c) ≈ 2–5 (or consult); reduction plumbing ≈ 1.  Full `hsmooth`
≈ 6–10 focused sessions.  `hsmooth` itself: statement not yet formed (0%); its dedicated
machinery after this session: kernel done, ≈ 15–20% of the brick.

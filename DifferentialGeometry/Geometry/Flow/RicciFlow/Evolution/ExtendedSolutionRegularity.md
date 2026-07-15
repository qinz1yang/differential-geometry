# ExtendedSolutionRegularity — notes

Builders toward `IsSolutionOn Shat` of `extends_of_rmBounded` (`MaximalTime.lean:291`), reusable for
`ham3_short_isSolution`. Plan: `~/.claude/plans/streamed-wobbling-honey.md` (P0-first). Gate brick
`metricCLMSection_jointContMDiffOn_of_chartGram_Ioo` banked + green.

## 2026-06-17 — P0 (chart-Gram jet bridge): DE-RISKED (FEASIBLE, not a wall); scaffold laid

**Strategic finding (the point of "P0-first"):** P0 — the shared analytic gate for `ricciCont`/`rm04Cont`/
`nablaRicCont` — is **feasible with no wall**. There is **no existing producer**: the precedent
`ricci_continuous_in_metric_time` (`ShortTimeAssembly/RicciContinuityInMetricTime.lean:1153`) *takes* the
`iteratedFDeriv(chartGramOnE)` continuity as a hypothesis (`hC2`); it never derives it from manifold
smoothness. So P0 is genuinely new, but every Mathlib ingredient exists.

**P0 statement** (now in this file, type-correct, body = `sorry`):
`chartGram_iteratedFDeriv_jointContinuousOn_of_contMDiffOn` — from
`hsmooth : ∀ x₀ i j, ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ) ∞ (chartGramMatrix (g ·) x₀ · i j) (Ioo a b ×ˢ baseSet)`
and `Sp ⊆ Ioo a b ×ˢ chartLeviCivitaGoodSet α`, produce (∀ k i j)
`ContinuousOn (fun q => iteratedFDeriv ℝ k (Integral.DivergenceTheorem.chartGramOnE (g q.1) α i j) (extChartAt I α q.2)) Sp`.
This is EXACTLY the `h0`/`h1`/`h2` shape consumed by `chartRicci_jointContinuousOn` /
`chartRiemann_jointContinuousOn` / `ricciChartFrameComp_jointContinuousOn` (RicciContinuityInMetricTime.lean
~1221/1240/1265).

**Single isolated sub-frontier** = the Mathlib-only core `contOn_partial_iteratedFDeriv_of_contDiffOn`
(also `sorry` here): for `F : ℝ × E → ℝ` jointly `C∞` on open `U`,
`(t,y) ↦ iteratedFDeriv ℝ k (F(t,·)) y` is `ContinuousOn U`.

**Proof route (confirmed ingredients):**
- (ii core) full `iteratedFDerivWithin ℝ k F U` continuous via `ContDiffOn.continuousOn_iteratedFDerivWithin`
  (`Mathlib/.../ContDiff/Defs.lean:760`); `U` open ⇒ `iteratedFDeriv = iteratedFDerivWithin`. The PARTIAL =
  full restricted to the `E`-slice along the affine `y ↦ (t,y) = (· + (t,0)) ∘ inr`, via
  `ContinuousLinearMap.iteratedFDerivWithin_comp_right` (`ContDiff/Basic.lean:439` — **valid for `ContDiffOn`**,
  not just global `ContDiff`) + `iteratedFDerivWithin_comp_add_right` (`ContDiff/FTaylorSeries.lean:675`,
  translation invariance). The result is `(iteratedFDeriv F (t,y)).compContinuousLinearMap (fun _ => inr)` —
  a continuous-linear image of the jointly-continuous full derivative, hence jointly continuous. Only k≤2
  needed by the consumer (verify nablaRicCont doesn't force k=3).
- (i reading) read `hsmooth` through the chart inverse `contMDiffOn_extChartAt_symm` + ContMDiffOn↔ContDiffOn
  for model spaces, getting `F (t,y) := chartGramMatrix (g t) α ((extChartAt I α).symm y) i j =
  chartGramOnE (g t) α i j y` as `ContDiffOn ℝ ∞` jointly on `Ioo a b × (extChartAt I α).target`.
- (iii) precompose with `x ↦ extChartAt I α x` (continuous on `chartLeviCivitaGoodSet α`); the global
  `iteratedFDeriv` = the within one at good-set/target-interior points (openness).

Effort: ~150-line fiddly analysis. The `iteratedFDerivWithin_comp_right` is affine-slice (translation +
`inr`), the main bookkeeping. NOTE the global-vs-within `iteratedFDeriv` subtlety (chartGramOnE is total on E
but `C∞` only on the chart target; good-set points map to the target interior, so global = within there).

**Build/import note:** added `import …ShortTimeAssembly.RicciContinuityInMetricTime` (no cycle — it does not
import this file). That pulls in modules whose `.olean`s were stale (`LeviCivita.Basic` etc.); a targeted
build of this module refreshes them before the focused check passes.

**Status:** interface + isolated core sub-frontier laid down (both `sorry`). NEXT: grind the core
`contOn_partial_iteratedFDeriv_of_contDiffOn` proof (the affine-slice route above), then (i)+(iii) to close P0.
Then P1/P5 (independent of P0), then P6/P7 consume P0.

## 2026-06-17 (cont) — core (ii) PROVEN; P0 reduced to 2 isolated sub-frontiers (file GREEN)

**✅ `contOn_partial_iteratedFDeriv_of_contDiffOn` — PROVEN (sorry-free).** The genuine analytic frontier
(parametric partial `iteratedFDeriv` continuity) is closed. Proof = (A) full `iteratedFDerivWithin ℝ k F U`
continuous via `ContDiffOn.continuousOn_iteratedFDerivWithin` + `iteratedFDerivWithin_of_isOpen`; (B) slice
identity `iteratedFDeriv k (F(t,·)) y = (iteratedFDeriv k F (t,y)).compCLM inr` via the affine decomposition
`z ↦ (t,z) = (·+(t,0)) ∘ inr` + `ContinuousLinearMap.iteratedFDerivWithin_comp_right` +
`iteratedFDerivWithin_comp_add_right` (the `(t,0)+ᵥ s' = U` set-eq via `vadd_eq_add`/`add_comm`/`abel`);
(C) assemble via `compContinuousLinearMapL.continuous`. Took 2 attempts (the (B) `vadd`/`comm` normalization).

**⏳ Two isolated sorries remain in P0** (file builds green):
1. `chartGramOnE_jointContDiffOn` (step (i), the math frontier): joint `ContDiffOn` of the chart-pulled Gram
   over `ℝ × E`. The route (compose `hsmooth` with `(id, extChartAt symm)`, then `ContMDiffOn → ContDiffOn`)
   hits a **Lean `whnf`/instance performance wall** on the PRODUCT manifold `ℝ × E`: `ContMDiffOn.contDiffOn` /
   `contMDiffOn_iff_contDiffOn` over `𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)` times out even at 1M heartbeats (prod `ChartedSpace`
   vs `chartedSpaceSelf` — needs `← modelWithCornersSelf_prod` **and** `← chartedSpaceSelf_prod` alignment, or a
   bespoke partial-`ContDiff` argument bypassing the manifold composition). Also: drop `set U` (it makes
   membership `.1`/`.2` projections fail).
2. `chartGram_iteratedFDeriv_jointContinuousOn_of_contMDiffOn` (P0): the assembly (apply the PROVEN core to the
   (i) helper, then precompose with `Ψ q = (q.1, extChartAt I α q.2)`) is written in a comment in the `.lean`
   and is correct, but the **final `hcore.comp hΨcont hΨmaps` defeq** (`core ∘ Ψ` vs the goal) `whnf`-loops
   unfolding `chartGramOnE` (times out at 1M). FIX: a `change`/`show` blocking the `chartGramOnE` unfold, an
   opaque alias, or `ContinuousOn.congr` with the per-point eq proven by a guarded `rfl`. The named lemmas it
   uses are correct: `ContinuousOn.prodMk`, `continuousOn_extChartAt (I := I) α`,
   `chartLeviCivitaGoodSet_mem_extChartAt_source`, `chartLeviCivitaGoodSet_extChartAt_mem_interior`.

**STUCK (>3 attempts) on P0's two manifold-plumbing sub-frontiers** (prod-model conversion + final-defeq whnf) —
both are Lean performance/instance issues, NOT mathematical obstructions. The mathematical content of P0 (the
analytic core) is done. Recommended next: resolve (1) the `ℝ × E` `ContMDiffOn → ContDiffOn` conversion (the
`chartedSpaceSelf_prod` alignment) — that likely also informs (2)'s whnf fix.

## 2026-06-17 (cont) — ROOT STRUCTURAL FINDING: `MetricFamilySmoothOn` `⊤` is a stale bug for `∞`

**The blocker for the `smoothMetric` field is NOT a proof wall — it is a public-structure bug.**
`MetricFamilySmoothOn.coeff` and `.frameCompSmooth` (`Curvature/Realized/MetricFamily.lean:488,505`) demand
smoothness level **`⊤`**.  In the current Mathlib (`ContMDiffOn`/`ContDiffOn` parameter `WithTop ℕ∞`):
`∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)` is **C∞**, while `⊤ : WithTop ℕ∞` is the **analytic** level `ω`, and
`∞ < ⊤` (NOT defeq: `∞ = some none`, `⊤ = none`).  Every brick gives `∞` (`_hsmooth` from
`ricci_flow_extends_construction`; the gate brick `metricCLMSection_…_Ioo`; `hframe.contMDiffOn`).  So the two
fields are **unconstructible from honest C∞ Ricci-flow data** — which blocks `extends_of_rmBounded` itself (its
new `(ω, ω+ε)` interior can only be `∞`).  The structure's OWN docstring says the intent is C∞
("joint `C∞` on the open slab… consumers use finite-order via `.of_le`"); `MetricCovDerivTimeDeriv.lean:627`
even does `(…).of_le le_top` to immediately drop the `⊤` to its real target `∞`.  Conclusion: `⊤` is a
leftover from pre-`WithTop ℕ∞` Mathlib (where `⊤ = ∞`); the fix is `⊤ → ∞` in both fields.

**Why this currently builds green:** `frameCompSmooth` is ALWAYS threaded as a *hypothesis* (`hS : IsSolutionOn`),
never inhabited from data.  The whole metric-smoothness tower is `⊤`-consistent end to end (producers thread
`⊤`, leaf consumers drop `⊤ → finite/∞` via `le_top`).  My builder is the FIRST to inhabit it from real `∞`
data, exposing that the `⊤` tower is uninhabitable.

**Cascade scope of the `⊤ → ∞` fix (~7 files, ~35 edits, MECHANICAL but care needed):**
- `MetricFamily.lean`: 2 struct fields + `metric_smooth_coeff_of_metricFamilySmoothOn` return (`:516`).
- Producers: `Core.lean` `isSolutionOn_timeShift` (~5 edits, incl. affine-map `⊤→∞`), `ParabolicRescaling.lean`
  `paraSol` (~6 edits).
- Re-exposers: `Metric/Basic.lean` `coordMetricSmooth`/`coordMetricSmoothAt` (`:82,:101`).
- `InverseSmooth.lean` (~15–20 sites): **CARE** — keep `⊤` on the genuinely-analytic `ContinuousLinearMap.inverse`
  facts (`:539,:667,:775`); change `⊤→∞` only on the metric-dependent compositions (analytic∘C∞ = C∞).
- Leaf consumers (drop `le_top`/adjust bound): `MetricCovDerivTimeDeriv.lean:627` (remove `.of_le le_top`),
  `CoordinateRegularity.lean:891,1143` (`.of_le` bounds).

**DEFERRED — pending user green light + collaborator coordination.**  The working tree has a large UNCOMMITTED
HCG `C4/` refactor in flight (collaborator moving the whole `HCGCompactness/*` tree); the cascade touches
HCG-consumed files (`InverseSmooth`, `MetricCovDerivTimeDeriv`).  Running it now would collide.  Asked the user
(A: do the cascade / B: defer + work other fields); awaiting decision.  Per "don't rewrite public defs without
ask" + active collaborator on the shared tree, NOT executing unilaterally.

**SAFE PROGRESS made in this file (no shared files touched):**
- ✅ `metricFrameComp_jointContMDiffOn_of_chartGram` **now concludes `∞` and is GREEN** (was the `⊤`-blocked
  `frameCompSmooth` sub-field).  Route confirmed end to end: gate brick (mono'd, with explicit type to pin the
  `.mono` target set) + `hframe.contMDiffOn i/j ∘ contMDiffOn_snd` + `ContMDiffOn.clm_bundle_apply₂` +
  `rw [Bundle.contMDiffWithinAt_totalSpace]; exact hpx.2`.  This **de-risks the whole `frameCompSmooth` plug-in**:
  once the field is `∞`, this lemma slots straight in.
- ✅ `metricVariationEquationOn_of_pde` (P3 `equation` field builder) — from raw `hpde`
  (`HasDerivWithinAt … (Ici a)` on `Ico a b`) to `MetricVariationEquationOn { base := { metric := g } }`.
  Inverse of `ricciFlowPDE_Ici_of_solution`: `t.2 : ↑t ∈ Ioo a b` (defeq via `closedOpen.regular = Ioo`) →
  `Ioo⊆Ico`, `HasDerivWithinAt.mono Ico_subset_Ici_self`, then
  `simpa [SolutionFamily.ricciAt, metricRicciAt, metricRicciAt_apply_eq_ricciTensor]`.  Needed
  `import …Basic.Core` (my two ShortTime* imports don't pull in the solution-package layer).

**USER DECISION (2026-06-17): HOLD the `⊤→∞` cascade until the collaborator's C4 refactor commits.**  The
working tree is mid-refactor (`HCGCompactness/* → C4/*`, incl. `MetricCovDerivTimeDeriv`) and the build is
unstable; the public-structure cascade would collide.  Bank P3 + `metricFrameComp@∞` now; apply the cascade
atomically once C4 lands, then build P1 + P9.

**HOLD LIFTED + CASCADE EXECUTED (2026-06-17, "C4 more or less done, keep working"):**  All 7 cascade files
were clean (not collaborator-dirty) and `MetricCovDerivTimeDeriv` was NOT moved by C4 (still at its original
path), so no path collision.  Applied `⊤→∞`: MetricFamily (2 fields + extractor); Core `isSolutionOn_timeShift`
(coeff+frameComp blocks, affine helpers); ParabolicRescaling `metricFamilySmooth_para` (7 sites);
Metric/Basic `coordMetricSmooth`/`coordMetricSmoothAt`; MetricCovDerivTimeDeriv (dropped `.of_le le_top`);
InverseSmooth (made `contMDiffOn_finset_sum` **n-polymorphic**, then the COORD chain `coordFrameGramCLM`/
`coordFrameGInvCLM`/`coordInvSmooth`/`coordInvSmoothAt` `⊤→∞` with `(hinvAt.of_le le_top)` for the analytic
`inverse`∘`∞`-gram compose — the GENERIC-frame chain `frameGramCLM`/`frameGInvCLM`/`gInv_spacetimeSmooth`/
`*_mdiffAt` STAYS `⊤` since it's built on the `⊤` `hreg` hypothesis package, not `coordMetricSmooth`).
CoordinateRegularity `.of_le (by simp)` left for the build to validate.  Full build verifying.

### Cascade VERIFIED + follow-on fixes (2026-06-18)
The `⊤→∞` cascade compiles: a full build reached **9324/9325 modules green**; `ParabolicRescaling`,
`MetricCovDerivTimeDeriv`, `Core`, `MetricFamily`, `Metric/Basic`, `CoordinateRegularity` all built.
Follow-on misses found + fixed:
- **InverseSmooth:491** — I had missed the `coordFrameGramCLM_spacetimeSmooth` conclusion (`⊤→∞`); it
  caused both the 501 (`smul` `∞` vs goal `⊤`) and 557 (`inverse∘gram` level) errors.  One-line fix.
- **P3:317** — `(hpde …).mono Set.Ico_subset_Ici_self` left the `Ico` upper bound `b` unconstrained
  (no expected type); fixed by annotating `h`'s type with `Set.Ico a b`.
- **CoordinateRegularity:892/1143/1199** — the three `.of_le (by simp)` consumers of
  `coordMetricSmoothAt`/`coordInvSmoothAt` (now `∞`).  `by simp`/`exact_mod_cast le_top` FAIL on
  `(n : WithTop ℕ∞) ≤ ∞` (since `∞ = ↑⊤` is NOT the WithTop top).  **Correct idiom:
  `WithTop.coe_le_coe.mpr le_top`** (`↑n ≤ ↑⊤ ⟺ n ≤ ⊤`).  GREEN.
- **ESR missing imports** — P3's `metricRicciAt_apply_eq_ricciTensor` (ns `DifferentialGeometry`,
  module `Curvature/MetricLeviCivitaReconcile`) and P1's `metricTensorCont_of_chartGram` (ns
  `Integral.Connection`, module `Curvature/Realized/MetricFamilyContinuity`) were NOT transitively
  imported by ESR (the earlier `.mono` error had masked P3's).  Added both imports.  `metricTensorField`
  is `Tensor0SBundle.metricTensorField` (module imported, just needed qualifying).

### P1 `metricFamilySmoothOn_of_chartGram` — all 4 fields written (verifying)
- `frameCompSmooth` ⇐ `metricFrameComp_jointContMDiffOn_of_chartGram` (`∞`) — one-liner.
- `metricTensor_cont` ⇐ `metricTensorCont_of_chartGram` with a `ℝ×M`→subtype adapter
  (`hcont`.comp the subtype inclusion `q ↦ (q.1.1, q.2)`, MapsTo via `q.1.2`/membership).
- `coeff_cont` ⇐ replicate `tensor2_eval_contOn`: `hcontTensor.eval_continuous` (fixed `x`, `vec2 X Y`)
  + `Tensor0SBundle.metricTensorField_apply` congr.
- `coeff` ⇐ gate-brick CLM section `metricCLMSection_…_Ioo` restricted to `t↦(t,x)`
  (`contMDiffOn_id.prodMk contMDiffOn_const`), `clm_bundle_apply₂` over `IM=𝓘(ℝ,ℝ)` with const base `x`
  and const vectors `X,Y`, `Bundle.contMDiffWithinAt_totalSpace`.2 to extract the scalar, then
  `ContMDiffOn.contDiffOn` (the clean ℝ→ℝ equivalence, NOT the P0 prod-model wall).
Input shapes match `ricci_flow_extends_construction`'s `_hsmooth`/`_hcont` exactly (`CinftyLimitGlue.lean:650-659`).

### P1 ✅ DONE — all 4 fields GREEN (targeted build, sorry-free)
`metricFamilySmoothOn_of_chartGram` compiles; only the 2 pre-existing **P0** sorries remain in this file
(`chartGramOnE_jointContDiffOn` ~196, `chartGram_iteratedFDeriv_…` ~219 — the chart-Gram jet bridge,
unrelated to P1).  Two Lean-perf hurdles resolved on the way:
- **`set_option maxHeartbeats 1000000 in`** on the theorem — the `coeff` bundle defeq
  (`clm_bundle_apply₂` over `IM=𝓘(ℝ,ℝ)` + `ContMDiffOn.contDiffOn`) and the `metricTensor_cont`
  adapter's `chartGramMatrix` defeq are heavy-but-finite (NOT the exponential P0 prod-model wall); 1M
  clears them.  (Perf caveat, not a math frontier; the lemma is settled API.)
- **adapter typeclass-stuck** — `(hcont x₀ i j).comp ?_ ?_` left the intermediate function/space as
  metavars → stuck `TopologicalSpace` synthesis.  Fix: a fully-typed `have hincl : ContinuousOn (fun q
  : {t // t ∈ Ico a b} × M => ((q.1 : ℝ), q.2)) {q | q.2 ∈ baseSet x₀}` pins the metavars, then
  `(hcont x₀ i j).comp hincl (fun q hq => ⟨q.1.2, hq⟩)`.
- **`set_option … in` placement**: must go BEFORE the docstring (`set_option … in` / `/-- … -/` /
  `theorem`), not between `-/` and `theorem` (else "unexpected token set_option; expected lemma").

**Remaining for `IsSolutionOn Shat` (the capstone, still 0% as a stated theorem):** `equation` (DONE,
`metricVariationEquationOn_of_pde`), `smoothMetric` (DONE, P1); still need the P0-gated curvature-continuity
fields (`ricciCont`/`rm04Cont`/`nablaRicCont`/`scalarCont`/`scalarTime`), the new per-metric producers
(`ricciNormSpace`/`ricciNormGrad`/`smoothConnection` — unbuilt fiber-norm-smoothness layer), and the P9
assembly `isSolutionOn_of_extendData` + the `MaximalTime.lean:291` call site.

### ✅✅ P0 FULLY DONE (2026-06-18) — the documented prod-model wall CRACKED; ESR is sorry-free
`ExtendedSolutionRegularity.lean` is now **entirely sorry-free** (read-only `lake env lean`: no errors, no
sorries).  Both P0 pieces proven at **default heartbeats**:
- **`chartGramOnE_jointContDiffOn` (step i)** — the prior multi-session wall (`ContMDiffOn(prod-manifold ℝ×M)
  → ContDiffOn(ℝ×E)` whnf timeout even at 1M).  **KEY FIX (self-model route):** build the chart map
  `σ = (fst, extChartAt.symm ∘ snd)` over the **self-model `𝓘(ℝ, ℝ×E)`** from the START — `hσ1 :=
  (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn`, `hσ2 := hsymm.comp hsnd hmaps2` (typed `hsnd`/`hmaps2`
  to pin the metavar set — inline lambdas leave `s` a metavar → `hp.2` projection fails), `hσ := hσ1.prodMk
  hσ2`, then `(hsmooth α i j).comp hσ … |>.congr (fun p _ => rfl)` and **`.contDiffOn`**.  Because everything
  is over the self-model `𝓘(ℝ,ℝ×E)`, the final `.contDiffOn` reads off cleanly — NO prod-manifold→model
  conversion, NO whnf wall.  (Do NOT `set S` — opaque prod-set membership breaks `hp.2`.)
- **`chartGram_iteratedFDeriv_jointContinuousOn_of_contMDiffOn` (step ii, assembly)** — apply the proven core
  `contOn_partial_iteratedFDeriv_of_contDiffOn hUopen hF k` (hF = step i), precompose with `Ψ q = (q.1,
  extChartAt I α q.2)` (`continuous_fst.continuousOn.prodMk ((continuousOn_extChartAt α).comp
  continuous_snd.continuousOn (chartLeviCivitaGoodSet_mem_extChartAt_source …))`; MapsTo via
  `chartLeviCivitaGoodSet_extChartAt_mem_interior`), then **`.congr (fun q _ => rfl)`** — the **per-point
  `rfl`** (eta + projection) keeps `chartGramOnE` opaque, dodging the function-level whnf loop the old comment
  warned about.

**Net: P0 unblocks `ricciCont`/`rm04Cont`/`nablaRicCont` (3 fields) — they consume exactly these h0/h1/h2.**
Remaining capstone fields: those 3 (now buildable via `chartRicci_jointContinuousOn` etc. + the P0 jets +
union-glue), `scalarCont`/`scalarTime` (from `ricciCont`), `ricciNormSpace`/`ricciNormGrad`/`smoothConnection`
(new per-metric producers), and P9 assembly.

### Ready-to-apply `⊤→∞` patch (verified-correct; apply atomically post-C4)
1. `MetricFamily.lean`: `coeff` (`:488`) `⊤→∞`; `frameCompSmooth` (`:505`) `⊤→∞`;
   `metric_smooth_coeff_of_metricFamilySmoothOn` return (`:516`) `⊤→∞`.
2. `Core.lean` `isSolutionOn_timeShift` (`:767–834`): the coeff/frameComp blocks — change the `have … : ContDiffOn/
   ContMDiffOn … ⊤` annotations AND the affine-map helpers (`haff`/`hmapSmooth`) to `∞` (affine maps are `C∞`,
   so `contDiff*`/`contMDiff*` lemmas re-prove at `∞`); the `refine ⟨…⟩` obligations auto-track `∞`.
3. `ParabolicRescaling.lean` `metricFamilySmooth_para`: coeff block (`:406–422`: `haff_global`,`hcomp` `⊤→∞`) +
   frameComp block (`:457–…`: `hOld`,`htime`,`hcomp/hscale` `⊤→∞`).
4. `Metric/Basic.lean`: `coordMetricSmooth` (`:82`) + `coordMetricSmoothAt` (`:101`) conclusions `⊤→∞`.
5. `InverseSmooth.lean` (~15–20 sites): **KEEP `⊤`** on the genuinely-analytic `ContinuousLinearMap.inverse`
   facts (`:539,:667,:775`); change `⊤→∞` ONLY on metric-dependent compositions (`:111–126,:143,:490,:510,:550,
   :569,:577,:585,:594,:733,:753,:781,:827,:834,:840,:847,:874,:880,:907,:912`) — analytic∘C∞ = C∞.
6. Leaf consumers: `MetricCovDerivTimeDeriv.lean:627` REMOVE `.of_le le_top` (source becomes `∞` = target);
   `CoordinateRegularity.lean:891,1143` adjust the `.of_le` bound proofs (`le_top` → `∞`-valid: `by simp`/`by
   exact_mod_cast le_top` if needed).
7. Full build to verify (signature of `extends_of_rmBounded` unchanged; expect only `hglue` DeTurck `sorry`).

### Post-cascade plan (P1 linchpin + P9 assembly) — against the `∞` contract
- **P1 `metricFamilySmoothOn_of_chartGram`** (this file): `frameCompSmooth` ⇐ `metricFrameComp_jointContMDiffOn_of_chartGram`
  (DONE, `∞`); `coeff` ⇐ time-slice of the gate brick (fix a frame, restrict to a `{t}×u` slice, `.contDiffOn`);
  `coeff_cont` ⇐ evaluate `_hcont` (chartGram `C⁰` on `Ico`) at chart-basis vectors; `metricTensor_cont` ⇐
  `metricTensorCont_of_chartGram` (+ `ℝ×M`→subtype adapter).
- **P9 `isSolutionOn_of_extendData`** assembles all 10 from: P1 (`smoothMetric`), `metricVariationEquationOn_of_pde`
  (`equation`, DONE), P5 union-glue for `ricciCont`/`rm04Cont`/`scalarCont` (P0-gated), P0 for interior
  `nablaRicCont`, and new per-metric producers for `ricciNormSpace`/`ricciNormGrad`/`smoothConnection` (NOT in
  `paraSol` as producers — they're threaded from `hS`; for the `(ω,ω+ε)` interior they need genuine
  smooth-metric⇒curvature-differentiability lemmas).

**REMAINING TRUE FRONTIERS (beyond the held cascade):** P0 prod-model `ContMDiffOn(ℝ×E)→ContDiffOn` whnf wall
(stuck >3×; feeds `ricciCont`/`rm04Cont`/`nablaRicCont`); new per-metric curvature-differentiability producers
for `ricciNormSpace`/`ricciNormGrad`/`smoothConnection` on the extended carrier.

### Field-by-field status of the 10 `IsSolutionOn Shat` fields (2026-06-17 exhaustion)
| Field | Status |
|---|---|
| `equation` | **BUILT** = `metricVariationEquationOn_of_pde` (env-verify pending the C4 olean churn) |
| `smoothMetric.frameCompSmooth` | **BUILT route** = `metricFrameComp_…@∞` (verified green); slots in once field is `∞` |
| `smoothMetric.metricTensor_cont` | brick banked (`metricTensorCont_of_chartGram`) |
| `smoothMetric.{coeff,coeff_cont}` | **HELD** — `coeff` needs `⊤→∞`; cascade held pending C4 |
| `ricciCont`/`rm04Cont`/`nablaRicCont` | **P0-gated** (jet bridge stuck >3× on `ℝ×E` whnf wall) + union-glue |
| `scalarCont`/`scalarTime` | derive from `ricciCont` → P0-gated |
| `ricciNormSpace`/`ricciNormGrad` | **missing fiber-metric-smoothness API**: all 3 routes (existing lemma / Mathlib RiemannianBundle on the (0,s)-tensor bundle / componentwise) reduce to the UNBUILT cotangent→tensor inner-product spatial smoothness. Only the TANGENT `metric_inner_contMDiffAt` (`Curvature/Riemann/Basic/Field.lean:299`) exists; the cotangent/`inner0S`/`normSq0S` (`Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean:454`) extension is missing. `gradientFun_smooth` (`Operator/GradientRegularity.lean:128`) exists, so `ricciNormGrad` follows once `ricciNorm` is smooth. Building this fiber-norm-smoothness layer is a real multi-lemma sub-project (cotangentInner smooth ⇐ inverse-metric smooth [InverseSmooth, `⊤`, downgrade] → tensor0S inner smooth → `normSq0S` smooth). |
| `smoothConnection` | threaded from `hS` in `paraSol`; for Shat's `(ω,ω+ε)` interior needs a new per-metric `ConnectionFamilySmoothOn` producer (not yet investigated in depth) |

**Conclusion:** every remaining field is blocked on exactly one of: the **held `⊤→∞` cascade** (user decision, await C4), the **P0 whnf wall** (stuck >3×), or the **unbuilt fiber-metric-smoothness layer** (a substantial sub-project warranting its own green-light). No field is completable now without one of those. Verification is additionally env-blocked while C4's build churns the `.olean` tree.

### 2026-06-18 (cont) — P9 assembly LANDED: 4/10 fields VERIFIED; the "blockers" above are now mostly resolved

The 2026-06-17 table above is SUPERSEDED. The `⊤→∞` cascade is DONE, P0 is DONE, and `isSolutionOn_of_extendData`
(P9) is now written in this file with **4 of 10 fields proved + verified** (focused `lake env lean` green, only
the expected `sorry` warning for the remaining 6). Two reusable bricks were banked first:

- **`Tensor0SFamilyContinuousOnSet.of_union_closedOpen`** (P5) + **`.congr`** — both in
  `Curvature/Realized/MetricFamily.lean`, verified. `of_union_closedOpen` glues `Ico a c` (closed-left half,
  from `_hS`) with `Ioo a b` (interior) over `a < c` (the `c ≤ b` hyp was unnecessary — dropped).
  `.congr` transports family continuity along a pointwise-equal family (carries `_hS`'s `[α,ω)` curvature onto
  `Shat` via `hagree`).
- **`normSq02_smooth`** (new, `Tensor/RSTensor/MetricTrace/Connection.lean`, next to `trace02_smooth`,
  verified GREEN first try): `ContMDiff (fun x => normSq0S g x 2 (A x))` for `A : Tensor0SField ∞ 2`. The
  **fiber-norm-smoothness layer the 2026-06-17 table said was unbuilt is now BUILT** — mirrors `trace02_smooth`
  exactly (coord formula `normSq0S_two_eq_coord` + private `gInvComp_contMDiffAt` ×2 + `tensor0S_eval_coordinateFrame_contMDiffAt` ×2).

**`isSolutionOn_of_extendData` signature** (this file): takes `{α omega b}` `(hαb : α<b) (hαω : α<omega)`, `g_ext`,
the original `S`+`hS` on `closedOpen α omega`, `hagree : ∀ s<omega, g_ext s = S.base.metric s`, and the
construction outputs `hsmooth`/`hcont`/`hpde` (chart-Gram `C∞` on `Ioo α b` / `C⁰` on `Ico α b` / PDE on `Ico α b`).
Produces `IsSolutionOn {base:={metric:=g_ext}}` on `closedOpen α b`. Reusable for `ham3_short_isSolution` too.

| Field | Status (2026-06-18) |
|---|---|
| `smoothMetric` | **✅ VERIFIED** = `metricFamilySmoothOn_of_chartGram g_ext hαb hsmooth hcont` |
| `smoothConnection` | **✅ VERIFIED** = per-metric `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (g_ext t)` (public, `Connection/LeviCivita/Smooth/Connection.lean:106`; NOT the private `lcConnectionSmooth`) + `simpa [SolutionOn.family, SolutionFamily.connection, …connectionAt]` |
| `equation` | **✅ VERIFIED** = `metricVariationEquationOn_of_pde g_ext hαb hpde` |
| `ricciCont` | **✅ VERIFIED** = P6 `ricciCont_interior_of_chartGram` (interior) + `_hS.ricciCont` `.congr`'d via `hagree` (half on `Ico α omega`) glued by `of_union_closedOpen`; `SolutionOn.ricci`↔`metricRicciAt` via `simp [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]` |
| `ricciNormSpace` | **✅ VERIFIED** = `(normSq02_smooth (g_ext t) (metricRicci (g_ext t))).mdifferentiableAt (by simp)` then `.congr_of_eventuallyEq` + `simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]` (do NOT add `SolutionOn.family_metric` — it's unused; `SolutionOn.family` + defeq suffices) |
| `ricciNormGrad` | **✅ VERIFIED** = `gradientFun_mdiffAt (g_ext t) hsmooth x` (`Operator/GradientRegularity.lean:137`) where `hsmooth : ContMDiff … (ricciNorm Shat t)` via `(normSq02_smooth …).congr` + the same simp |
| `scalarCont` | **✅ VERIFIED (2026-06-18) → 8/10.** The earlier "BLOCKED" was WRONG — `chartBasisFamily` (`ChartGram.lean:186`, `chartBasisFamily_apply`) IS the `chartModelBasis`-world `Module.Basis`, so the chart-trace composes natively. Built (all green): `metricScalar_chartTrace_eq` (`metricScalarAt = ∑ chartInvGramOnE · ricciTensor(cbv,cbv)`, via `metricTracePair0SAt_eq_sum_basis` with `chartBasisFamily` + `chartInvGramMatrix` as `Tensor0SBundle.MetricInverseInBasis_gen` [from `chartInvGramMatrix_mul_chartGramMatrix`] + `metricRicciAt_apply_eq_ricciTensor` + `chartInvGramOnE_def`/`extChartAt.left_inv`) and `chartScalar_jointContinuousOn` (∑ `jointInvGram` × `ricciChartFrameComp`), both in `RicciContinuityInMetricTime.lean` (needed `import …Curvature.MetricLeviCivitaReconcile`). Then `scalarCont_interior_of_chartGram` (ESR, ℝ-valued: `chartScalar` good-set `ContinuousAt`-patching) + `_hS` half (via `hagree`) + `continuousWithinAt_inter` open time-cover glue. **OLD (wrong) analysis kept below for the lesson:** ~~BLOCKED — missing API (gInv-construction mismatch).~~ Field needs JOINT `(t,x)` continuity of `metricScalarAt (g_ext t) x` on `Ico α b ×ˢ univ`. 3 routes investigated 2026-06-18, all need fresh infra: (R1) a `Tensor0SFamilyContinuousOnSet.metricTrace` closure from the verified `ricciCont` — does not exist, and the trace intrinsically needs gInv. (R2) chart-trace `metricScalarAt g x = ∑_ij gInv·ricciTensor(cbv_i,cbv_j)` [`metricScalarAt` is *def* `metricTracePair0SAt g (metricRicciAt g x)`; expand via `metricTracePair0SAt_eq_sum_basis (gInvBasisAt)` + `metricRicciAt_apply_eq_ricciTensor`] — but **`gInvBasisAt`'s gInv is `inverseMetricFlatModelInChart_component`** (`Coordinates/MetricCompatibility/Inverse.lean:456`) while the only joint-continuity machinery **`jointInvGram_continuousOn`** (private, `RicciContinuityInMetricTime.lean:492`) produces **`chartInvGramOnE`** (`VossWeyl.lean:66` = `chartInvGramMatrix∘extChart.symm`). These are two *different* inverse-metric constructions (flat-model CLM-inverse vs Gram-matrix-inverse); **no bridge lemma exists** `inverseMetricFlatModelInChart_component = chartInvGramOnE`. (R3) (0,0)-tensor keystone + `Tensor0SFamilyContinuousOnSet 0 ↔ ContinuousOn` conversion — conversion does not exist. **Smallest unblock:** prove `inverseMetricFlatModelInChart_component g α i j (extChartAt I α x) = chartInvGramOnE g α i j (extChartAt I α x)` (on the good set), then build public `chartScalar_jointContinuousOn` (∑ of `jointInvGram` × `ricciChartFrameComp`) in RicciContinuityInMetricTime, then scalarCont = interior (good-set local patching, ℝ-valued) + `_hS` half + glue. Genuine fresh sub-project (~1 focused session). |
| `scalarTime` | **✅ VERIFIED (2026-06-18) — sorry DISCHARGED → 9/10.** Field wiring as before (eq_or_lt split + nhds-germ). `scalarTime_interior_of_chartGram` now FULLY PROVEN via a **CMM-free time-`ContDiff` chain** (see the 2026-06-18 section below). Foundation: `partialDeriv_jointContDiffOn` (spatial `∂ₘ` of a jointly-`C∞` `G : ℝ×E→ℝ` is jointly `C∞`, via `ContDiffOn.fderivWithin` + eval-at-`(0,eₘ)`; the `fderiv`/CLM route sidesteps the `ContinuousMultilinearMap` `NormedSpace` instance wall that killed the `iteratedFDeriv` route). Slice the joint `chartGramOnE_jointContDiffOn` at fixed `y` (`chartTimeSlice_contDiffOn`) → `hp0/hp1/hp2` (chart-Gram time-jets), feed the mirror chain `gramBracket→gramBracketDeriv→partialDeriv_chartInvGramOnE→chartChristoffel→partialDeriv_chartChristoffel→chartRiemannTensor→chartRicciTensor` (all `_contDiff`, mirror of `RicciContInMetricAux`), inverse-Gram value via `chartInvGramOnE_contDiff_in_metric_at` (det/adjugate `ContDiff` from `matrixDet_contDiffOn`/`matrixAdjugate_contDiffOn` + `ContDiffOn.inv`). Assemble `metricScalarAt = ∑ chartInvGram · chartRicci` (`metricScalar_chartTrace_eq` + `ricciTensor_chartBasisVec_alpha_eq` bridge; **gotcha:** `RicciFlow.metricScalarAt` is an `abbrev` for `Connection.metricScalarAt` — `show Connection.metricScalarAt …` before the `rw`) → `.differentiableOn`. |
| `rm04Cont` | **✅ VERIFIED** (P7) — `metricRm04_chartBasisVec_alpha_eq` (NEW private lowering in ESR: `metricRm04At_eq_riemannCurvature04At` → `CovariantDerivative.riemannCurvature04At_apply_const` → `riemannCurvatureAux_tangentConst_eq_riemannOp` → `riemannOp_chartBasisVec_alpha_eq` → `map_sum`/`chartGramMatrix_apply`; lowers last slot to `∑_l chartRiemann(idx2,idx0,idx1,l)·chartGram(idx3,l)`) + `rm04Cont_interior_of_chartGram` (rank-4 keystone: `continuousOn_finset_sum` of `chartRiemann_jointContinuousOn` × `hsmooth.continuousOn.mono` [chartGram value direct, no jet bridge needed]) + `_hS.rm04Cont` half via `.congr`+`hagree` glued by `of_union_closedOpen`. **KEY namespace gotcha:** the field uses `Connection.metricRm04At` (Core abbrev), NOT Curvature's `metricRm04At` — qualify explicitly or the `metricRm04At_eq_riemannCurvature04At` rw fails to match; `riemannCurvature04At_apply_const` is in `…Connection.CovariantDerivative` (ESR doesn't open it → qualify `CovariantDerivative.`). |
| `nablaRicCont` | **FIELD WIRED; 1 ISOLATED FRONTIER-SORRY (the only remaining sorry in the file).** Interior-only (`D.regular`), no glue/half: wired via the rank-3 keystone `tensor0SFamilyContinuousOnSet_of_chartBasisComp` + good-set cover. The per-component goal = `ContinuousOn (fun q => totalNabla0SFun 2 (conn q.1.1)(ric q.1.1) q.2 (cbv tuple)) {q.2 ∈ goodSet}`. **THREE distinct Lean write-attempts FAILED (2026-06-18, all `lake build`-confirmed):** (1) `fun_prop` → *"No theorems found for `totalNabla0SFun`"* (NO continuity API exists for the covariant-derivative tensor); (2) manual `totalNabla0SFun_apply_section` + coordinate-frame `nabla0SFun_two_eval_coordFrame` reduction → *"simp made no progress"* (the goal is not in `Fin.cons (X x) slots` section form — `cbvf` is a *local* frame, not a global `ContMDiffSection`; and the only `nabla0SFun` formula is `coordinateFrameAt`/`finBasis`-world, namespace-inaccessible + does NOT unify with the keystone's `chartBasisVecFiber`/`chartModelBasis` frame, `chartModelBasis @[irreducible] ≠ finBasis`); (3) `exact hS.nablaRicCont` → *type mismatch* (covers only `Ioo α omega`, not the extension `Ioo α b`; original `S` vs candidate `Ŝ`). **FRONTIER** = build a `totalNabla0SFun` (∇Ric) chart-frame joint-continuity producer — the order-3 analog of `ricciChartFrameComp_jointContinuousOn` (∇Ric = ∂chartRic − Γ·chartRic at the chart frame): needs (a) an intrinsic-∇ → chart-frame bridge identity (NO scaffold in the `chartModelBasis` world; the cov-deriv-at-`chartBasisVecFiber` infra in `FrameInvariance.lean`/`RealizedCovGradJetInput.lean` is for `SmoothCcTensor`/Sobolev, not `totalNabla0SFun`), and (b) an order-3 `∂chartRic` continuity producer extending `RicciContInMetricAux` one ∂ deeper. Substantial separate layer (≈ the scalarTime layer in size, but harder — crosses the frame divide for a derivative). |

## 2026-06-18 — scalarTime DISCHARGED via CMM-free time-`ContDiff` chain → **9/10**

**The CMM wall (route 1, abandoned after 3 verification iterations).** The clean route — strengthen the P0
continuity core to `ContDiff` (`(t,y)↦iteratedFDeriv ℝ k (F(t,·)) y` jointly `C∞`) — walls on a typeclass
obstruction *in this file*: `NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _:Fin k => E) ℝ)` will not
synthesize, even after importing `Mathlib.Analysis.Normed.Module.Multilinear.Basic` (the instance's home) and
pinning `compContinuousLinearMapL (F := ℝ)`. The continuity core only ever needed the *topological* CMM
structure (`ContinuousOn`), so the normed-CMM instance is simply not wired up here. Reproduced 3×; classified
typeclass.

**The CMM-free route (route 2, WORKS).** Never form a `ContDiffOn` of a CMM-valued function. Work with
`ℝ`-valued `partialDeriv` (= `fderiv … (chartModelBasis E m)`, CLM-valued — and `E →L ℝ` *is* normed here).
Key brick `partialDeriv_jointContDiffOn`: for `G : ℝ×E→ℝ` jointly `C∞` on open `U`,
`(t,y) ↦ partialDeriv m (G(t,·)) y` is jointly `C∞` on `U` (full `fderiv ℝ G` is `C∞` via
`ContDiffOn.fderivWithin`+open-congr; partial = its eval at `inr eₘ = (0,eₘ)` via `ContDiffOn.clm_apply` +
the order-1 slice `fderiv (G(t,·)) y = (fderiv G (t,y)) ∘L inr`). It **composes** (apply twice for the 2-jet).
Then slice at fixed `y` → the `hp0/hp1/hp2` the chain consumes.

**Matrix-inverse `ContDiff`-in-time** (no Mathlib lemma exists; built here): `matrixDet_contDiffOn`
(`det_apply` + `ContDiffOn.sum`/`contDiffOn_prod` + `ContDiffOn.const_smul` for the `sign σ`),
`matrixAdjugate_contDiffOn` (`adjugate_apply` = det of `updateRow`, entries `C∞` by `updateRow_self`/`_ne`
cases), `chartInvGramOnE_contDiff_in_metric_at` (Cramer `G⁻¹=(det)⁻¹•adj` + `ContDiffOn.mul`/`ContDiffOn.inv`,
mirror of `chartInvGramOnE_continuous_in_metric_at`).

**The chain** = a `_contDiff` mirror of the `RicciContInMetricAux` continuity family (same value-`heq`
identities, `ContinuousOn.*` → `ContDiffOn.*`). Lives in ESR (consumer); the `gramBracket`/`gramBracketDeriv`/
`partialDeriv_chartChristoffel_eq` identifiers needed `open …IntrinsicSpectral.DeTurckCoefficients`.

## 2026-06-19 — `nablaRicCont` FIELD REMOVED → `isSolutionOn_of_extendData` SORRY-FREE

The remaining `nablaRicCont` sorry was NOT filled — the **field was deleted** from `IsSolutionOn`. Rationale
(user-prompted): `nablaRicCont` is `D.regular` (interior-only) continuity of `∇Ric`, a ≤3rd-order
differential expression in the metric — so it is *implied by* `smoothMetric` (interior C∞) AND a prior audit
confirmed it is **never consumed** (its only extractor `nablaRicFamilyContinuousOnSet` had no call sites; all
other uses were transport rebuilds / a `ricciRegOfSol` pass-through). It was a vestigial eager-bundled field.
Three `lake build`-confirmed attempts to *fill* it first established there is no `totalNabla0SFun` chart-frame
continuity API (see the nablaRicCont row); removal is the correct fix, not building that layer.

Clean removal (no compat shims), all 4 sites: `IsSolutionOn.nablaRicCont` (struct field),
`CanonicalRicciRegularOn.nablaRic_cont` (struct field) + `nablaRicFamilyContinuousOnSet` (extractor) +
`Regularity.lean` builder line; and the 3 producer supplies (`isSolutionOn_timeShift` in `Core`, `paraSol`
in `ParabolicRescaling`, `isSolutionOn_of_extendData` here). Full `lake build` green.

**STATUS (2026-06-19): `isSolutionOn_of_extendData` is COMPLETE and SORRY-FREE** (9 fields, all proven —
`IsSolutionOn` is now a 9-field structure). `IsSolutionOn Shat` is fully constructible. The only remaining
step for the `MaximalTime.lean:291` sorry is the 1-line call-site wiring
`exact isSolutionOn_of_extendData g_ext S _hS hagree _hsmooth _hcont hpde`. The twin `ham3_short_isSolution`
sorry is also unblocked (its `nablaRicCont` obligation is gone).

**Next:** (1) discharge `nablaRicCont` — the per-component order-3 `∇Ric` chart-frame joint *continuity*
(`totalNabla0SFun 2 (conn)(ricci)(cbv tuple)` on the good set). Needs (a) a `∇Ric` chart-frame bridge identity
`totalNabla0SFun … (cbv) = ∂(chartRic) + Γ·chartRic`-shape (NEW; analog of `ricciTensor_chartBasisVec_alpha_eq`),
and (b) an order-3 continuity producer `partialDeriv_chartRicciTensor` (extend the continuity chain one ∂ deeper,
consuming order-3 chart-Gram jets — `chartGram_iteratedFDeriv_jointContinuousOn` already gives any order). The
larger of the two original frontiers. (2) Wire `MaximalTime.lean:291`:
`exact isSolutionOn_of_extendData g_ext S _hS hagree _hsmooth _hcont hpde` (closedOpen.{carrier,regular} rfl).

Deferred polish: benign `show`→`change` at `ESR:501` (P6); 2 unused-simp-arg warnings in the scalarTime field
germ proofs.

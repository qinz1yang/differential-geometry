# ExtendShiInputs — Brick Y1 (Lemma-3.11 inputs for the interior-restart extension route)

Discharges `ricci_flow_interior_restart`'s `hell` + `hC3` hypotheses from a bounded-curvature solution,
reusing the HCGCompactness Lemma-3.11 engine instead of the retired bespoke chart-C³ producer (Brick W).

## DONE this session (2026-07-02), all verified green (targeted build)

1. **Import de-risk — THE key architectural result.** A new `Geometry/Flow/RicciFlow/` file importing
   `Evolution.ExtendViaUniqueness` + `HCGCompactness.AllTimesBounds` + `HCGCompactness.RicBound` **builds
   cycle-free** (full build green, 9459 jobs). This confirms in practice (not just theory) that the
   extension branch can consume Lemma 3.11 — the whole "rethink the route" redirection is sound.
2. **`ricciFlowPDE_Ici_of_soln` (sorry-free).** The solution's Ricci-flow metric PDE as a one-sided
   right-derivative on `Ico α ω` (= Brick X's `hpde` input, `g_fam := S.base.metric`). Ported down from
   `MaximalTime.ricciFlowPDE_Ici_of_solution` (private, above). Needed two private MaximalTime helpers
   (`hasDerivWithinAt_Ici_boundary`, `tensor2_eval_contOn`) re-derived here (self-contained; Y2 should
   move the MaximalTime privates down and reuse these).
3. **`hell_of_soln` (sorry-free modulo one hypothesis).** (A)'s `hell` for a solution: a one-liner
   `metricEquiv_of_ricBound (fun t => S.base.metric t) hαω hK (ricciFlowPDE_Ici_of_soln hS) hric`. The
   only input is `hric : |ricciTensor (S.base.metric t) x v v| ≤ K·(S.base.metric t).inner x v v` (the
   pointwise Ricci-vs-metric bound), taken as a hypothesis — its discharge is Y2 curvature algebra.

## Confirmed shapes / namespaces (for the remaining wiring)

- `hell` shape ≡ `DifferentialGeometry.HCGCompactness.MetricUniformEquivalentOn K gRef h C`
  (`1≤C ∧ ∀x∈K,∀v, C⁻¹gRef(v,v)≤h(v,v)≤C·gRef(v,v)`), `AllTimesBounds.lean:601`; window form
  `MetricUniformEquivalentOnWindow` (:612) = `∀ i t∈[β,ψ], …(gSeq i t)…`.
- covariant metric-deriv bound (chart-adapter INPUT): `MetricCovDerivOrderBoundOn K a h gRef C`
  (:691) = `∀x∈K, metricCovDerivNorm a h gRef x ≤ C`, `metricCovDerivNorm a h gRef x =
  sqrt(normSq0S gRef x (a+2) (metricCovDeriv h gRef a x))` (:661) = `‖∇^a_{gRef} h‖_{gRef}`; window form
  `MetricCovDerivOrderBoundOnWindow` (:773). Both namespaced `DifferentialGeometry.HCGCompactness.*`.
- Shi predicate `DifferentialGeometry.HCGCompactness.MovingShiBoundOn U β ψ gSeq N KShi` (`RicBound.lean:141`),
  `ricCovTower` (:117). Single-flow instantiation: `gSeq := fun _ t => S.base.metric t`.

## Layering refinement discovered (reshapes the endpoint)

`extends_of_rmBounded`'s hypothesis predicates `Rm04NormSqBoundedAt`, `Rm04RealizesSolutionConnectionOn`,
and `ExtendsPastEndpoint` are defined **only in `MaximalTime.lean`**, which is ABOVE this file
(MaximalTime imports ExtendShiInputs in Y2). So the Y1 endpoint **cannot consume them from below.**
Fix: the Y1 endpoint takes the RAW lower-layer content (the `normSq0S (Rm04 t x) ≤ C` bound, the
realization equation, `IsSolutionOn`), all visible here; Y2 (in MaximalTime) bridges
`Rm04NormSqBoundedAt → raw` at the call site. Also: much solution-PDE plumbing
(`ricciFlowPDE_…`, the two boundary helpers, the Rm04 predicates) is currently PRIVATE in MaximalTime;
the clean Y2 refactor moves it down here and has MaximalTime reuse it.

## Remaining Y1 (multi-session frontier — NOT done)

- **`hric` discharge**: `Rm04NormSqBoundedAt`/raw `|Rm|²≤C` ⟹ `|Ric(v,v)| ≤ K·g(v,v)` — pointwise
  curvature algebra (`|Ric| ≤ c(n)|Rm|` contraction + operator→quadratic). Grep the Rm04/Ricci-trace
  norm API (`ricciComp_eq_trace_rm04_frame`, `normSq0S`, `Rm04Realizes…`). Narrow but real.
- **Item 2 — Lemma 3.11 instantiation for `hC3`'s covariant input**: feed the single flow
  `gSeq := fun _ t => S.base.metric t` + the cited Shi producer through `metricCovOrderWindow_of_*`
  (`AllTimesBounds.lean:793/4168/4403`) to get `MetricCovDerivOrderBoundOnWindow`. READ those producers'
  exact hypotheses first (they may consume evolution predicates, not just Shi — that determines the
  cited Shi producer's shape, which is why it was NOT stubbed this session).
- **Item 4 — the static covariant→chart adapter (the one genuinely new lemma)**:
  `MetricCovDerivOrderBoundOn (a≤3) + MetricUniformEquivalentOn ⟹ ‖iteratedFDeriv k (chartGramOnE g α i j)
  (extChartAt I α x)‖ ≤ Λ` on a compact `Q ⊆ chartLeviCivitaGoodSet α`, `k ≤ 3`. STATIC recursion
  `∂ = ∇_{gRef} + Γ_{gRef}·(lower)` with FIXED `gRef = S.base.metric α` (its chart Christoffels bounded
  with all derivatives on `Q`); `iteratedFDeriv ↔ partialDeriv` via public
  `jet2_chartGram_d1/d2` (`Evolution/ChartRicciJetIdentity.lean`). NO time integration. `goodSet`
  non-compactness ⇒ compact-`Q` `hC3` shape + the sanctioned (A) patch. ~150 lines; the real work.
- **Item 1 — cited Shi producer** (sorry): shape it to match item 2's consumed hypotheses.
- **Item 5 — endpoint** `extendInputs_of_soln`: `⟨hell_of_soln …, hC3 …⟩` from the raw solution hyps.

## PLANNER ACCEPTANCE — ✅ Y1-partial ACCEPTED (Fable, 2026-07-03)
Verified: file 0-sorry (4 declarations as reported); `ExtendViaUniqueness.lean` untouched (sorries
= exactly (N) :85, (B) :201); `MaximalTime.lean` untouched (`hglue` :292); diff = this new pair
only. The import de-risk (cycle-free, full build green) closes the redirection's last architectural
risk. Remaining Y1 re-bricked below: **Y1b = the adapter (+ `hric` if room), Y1c = items 2→1→5.**

## BRICK Y1b — KICKOFF PROMPT for the next Opus 4.8 executor session

**Paste-pointer:** *"Work in `E:\testdifferential-geometry`. Read `CLAUDE.md`, `important_lesson.md`,
then `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` sections 'Remaining Y1' and
'BRICK Y1b' — implement the static covariant→chart adapter (item 4) with the DECIDED compact-`Q`
reshape, then `hric` if the session has room. Report back. Off-limits files per 'Rules' below."*

**DECIDED statement reshape (do this first, it is forced and sanctioned).** Bounds on all of
`chartLeviCivitaGoodSet α₀` are unproducible (not relatively compact; the reference data may blow up
at its boundary). Reshape, in `Evolution/ExtendViaUniqueness.lean`, keeping everything else fixed:
- **(N) `ricci_flow_unif_existence`**: the box's choice becomes `∃ S : Finset M, ∃ Q : M → Set M,
  (∀ α₀ ∈ S, IsCompact (Q α₀) ∧ Q α₀ ⊆ chartLeviCivitaGoodSet α₀) ∧ ∀ Λ, …`, and its data-bound
  clause quantifies `∀ x ∈ Q α₀` (was: `∈ goodSet α₀`). Faithful — parabolic theory wants data
  bounds on a compact chart cover; the box internally picks a compact refinement.
- **(A) `ricci_flow_interior_restart`**: `hC3` becomes
  `∀ S : Finset M, ∀ Q : M → Set M, (∀ α₀ ∈ S, IsCompact (Q α₀) ∧ Q α₀ ⊆ goodSet α₀) → ∃ Λ ≥ 1,
  ∃ t₂ ∈ Ico α ω, ∀ s ∈ Ico t₂ ω, [same bounds, on Q α₀]`; patch (A)'s proof (local — `hC3` is
  consumed only where the box's data hypothesis is discharged; the box now also supplies the
  compactness/subset facts to feed `hC3 S Q`). Re-verify (A) sorry-free after the patch.

**The adapter (item 4 — the real work, ~150 lines, in `ExtendShiInputs.lean`).** Target shape
(QUANTIFIER ORDER IS THE TRAP — `Λ` must come BEFORE the metric so the tail bound is uniform):
```
theorem chartJets_of_covBound (gRef : SmoothRiemannianMetric I M) (C : ℝ) (hC : 1 ≤ C)
    (α₀ : M) {Q : Set M} (hQc : IsCompact Q) (hQ : Q ⊆ chartLeviCivitaGoodSet (I := I) α₀) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ g : SmoothRiemannianMetric I M,
      (∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Q a g gRef C) →   -- match :691's exact shape
      MetricUniformEquivalentOn Q gRef (fun x v w => g.inner x v w) C →  -- match :601's shape
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 3 → ∀ x ∈ Q,
        ‖iteratedFDeriv ℝ k (Integral.DivergenceTheorem.chartGramOnE (I := I) g α₀ i j)
          (extChartAt I α₀ x)‖ ≤ Λ
```
(Adjust the two predicate applications to their true signatures — read `AllTimesBounds.lean:601/661/691`
first.) Route: STATIC recursion `∂ = ∇_{gRef} + Γ_{gRef}·(lower)` — chart partials of the Gram of `g`
in terms of `gRef`-covariant derivatives of `g` and the FIXED smooth reference chart data
(`chartChristoffel gRef`, bounded with all derivatives on compact `Q` by continuity — `IsCompact.exists_bound`-style
sup). k = 0: equivalence + `gRef`'s Gram bounds. k = 1: the chart metric-compat /
`∇g = ∂g − Γ·g − Γ·g` rearrangement (grep `ChartGramChristoffel`, `partialDeriv.*chartGram`). k = 2, 3:
iterate the recursion; each `∂^k(Gram g)` = polynomial(`Γ_{gRef}`-jets ≤ k−1 on `Q` [static], `∇^{≤k}g`
[hypothesis], `Gram`-lower). `iteratedFDeriv ↔ partialDeriv`: reuse `jet2_chartGram_d1/d2`
(`Evolution/ChartRicciJetIdentity.lean`, public) + finite-dim norm bridges (grep `UniformChartBounds/`,
`ChartGramUniformContinuity`). NO time integration anywhere — if you find yourself integrating in `t`,
you are off-route. The covariant-norm unpacking (`metricCovDerivNorm` = `‖·‖` via `normSq0S`, :661)
to slot/component bounds: grep the `normSq0S` component API (`Tensor/RSTensor/`) before hand-rolling.
**`hric` (if room):** `|Ric(v,v)| ≤ K·g(v,v)` from the raw `normSq0S`-`|Rm|²` bound — pointwise
curvature algebra; grep `ricciComp_eq_trace`/`rm04`/Cauchy–Schwarz-on-`normSq0S` API.

**Rules:** claim `ExtendShiInputs.lean` + `Evolution/ExtendViaUniqueness.lean` (the sanctioned
reshape only). Off-limits: everything under `HCGCompactness/` (import-only), `ShortTime*/`,
`DeTurck*`, `CinftyLimitGlue.lean`, `MaximalTime.lean`, frozen `JetGlueParam.lean`; (N)/(B) bodies
stay `sorry`. Verify: focused checks + targeted builds of both files. **Acceptance:** adapter
sorry-free with the Λ-before-`g` quantifier order; (A) re-verified sorry-free post-reshape; the two
files' only sorries remain (N)/(B); report `#print axioms` for the adapter (must be the 3 standard
axioms). Thread-crash flakes: retry, `-LeanThreads 3`. Stop per CLAUDE.md (3 failed routes ⟹ report).

### Y1b SESSION PROGRESS (2026-07-03)

**DONE + verified: the compact-`Q` reshape.** `Evolution/ExtendViaUniqueness.lean` (N)
`ricci_flow_unif_existence` and (A) `ricci_flow_interior_restart` reshaped exactly as decided: (N) now
begins `∃ S : Finset M, ∃ Q : M → Set M, (∀ α₀ ∈ S, IsCompact (Q α₀) ∧ Q α₀ ⊆ goodSet α₀) ∧ ∀ Λ, …`
with its data clause on `∀ x ∈ Q α₀`; (A)'s `hC3` takes `∀ S, ∀ Q, (compact-cover) → ∃ Λ, …, ∀ x ∈ Q α₀`.
(A)'s proof patched (`obtain ⟨S, Q, hSQ, hbox⟩`; `hC3 S Q hSQ`; `hC3_star` on `Q α₀`) and **re-verifies
sorry-free** — the file's only sorries stay (N):64 and (B):179. This unblocks the adapter's consumption.

**NOT done: the adapter `chartJets_of_covBound`** — confirmed a genuine fresh ~200-line multi-bridge
brick (all pieces exist, feasible; but not one-session alongside the reshape). Recommend a dedicated
adapter session. Execution-ready API map (all located this session):
- **chartGram ↔ inner / bilin bridge**: `chartGramBilin_eq_innerJinv`
  (`Analysis/Spectral/Tensor/ChartTensor/Inner/InnerBridge.lean`); chartGramMatrix↔chartGramBilin in
  `ChartTensor/Inner/LowerAllUpperIndices.lean`, `Defs.lean`. `chartGramBilin` + `le_opNorm₂` and
  `chartGramMatrix_entry_isBounded_on_compact` (`UniformChartBounds/ChartGramUniformContinuity.lean:151`,
  `∃C>0, ∀b∈K, |chartGramMatrix g α b i j|≤C` for compact `K ⊆ chartSource`) +
  `MetricUniformUpperBound.lean` (`g_inner_sqrt_uniform_upper_bound_on_compact`:224).
- **k=0**: equivalence + gRef Gram bound on `Q`; off-diagonal needs a PSD Cauchy–Schwarz for `g.inner x`
  (`(g(u,v))² ≤ g(u,u)g(v,v)`) — NOT found ready in `Geometry/Metric/`; likely a ~15-line new helper
  (discriminant of `g(u+tv,u+tv) ≥ 0`).
- **∂ = ∇_{gRef} + Γ_{gRef}·(lower) recursion (k=1,2,3)**: `metricCovDeriv_succ_component_coordFrame`
  (`HCGCompactness/MetricCovDerivCoordStep.lean`, coordinate-frame; importable), with
  `metricCovDeriv_succ_apply_section` / `_eval_smooth_slots`; leading connection
  `leviCivitaConnectionOfMetric gRef`.
- **coordComponent ↔ chartGram**: `Tensor0SInnerBridgeIdentity.lean` (`…_matrix_form`, `…_innerJinv`).
- **`metricCovDerivNorm` → single-component bound**: `normSq0S` component/CS-eval
  (`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean:711`; `tensor02_quadForm_abs_le` in
  `Geometry/Curvature/RicciOperatorNormBound.lean`).
- **iteratedFDeriv ↔ partialDeriv**: public `jet2_chartGram_d1/d2`
  (`Evolution/ChartRicciJetIdentity.lean`); k=3 needs a d3 step or manual iterate.
- **Γ_{gRef} jets bounded on `Q`**: `chartChristoffel gRef` continuous ⇒ `IsCompact.exists_bound` sup.
- **Trap** (from brief): quantifier order `Λ` BEFORE `g` (uniform tail bound); NO time integration.

## PLANNER ACCEPTANCE — ✅ Y1b-partial ACCEPTED (Fable, 2026-07-03): reshape landed, adapter re-dispatched
Verified in-tree: (N) carries `∃ S, ∃ Q, (∀ α₀ ∈ S, IsCompact (Q α₀) ∧ Q α₀ ⊆ goodSet α₀) ∧ …` with
its data clause on `∀ x ∈ Q α₀`; (A)'s `hC3` takes the `∀ S, ∀ Q, (compact cover) → …` form; (A)'s
proof region has 0 sorries (re-proved post-patch); file sorries = exactly (N) :87 + (B) :205.
Executor's targeted build green accepted. The adapter (primary ask) is 0% — correctly reported
fail-loud, correctly not forced as a multi-sorry half-build. **Re-dispatched as a STANDALONE brick
(Y1b′, below), no bundling.**

## BRICK Y1b′ — KICKOFF PROMPT (adapter only; dedicated session)

**Paste-pointer:** *"Read `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` — the
pinned adapter inventory (the scoping sections) and section 'BRICK Y1b′'. Implement ONLY the
adapter `chartJets_of_covBound`. Report back. Off-limits per the Rules below."*

**Scope: exactly one deliverable.** `chartJets_of_covBound` in `ExtendShiInputs.lean`, sorry-free,
with the Λ-BEFORE-`g` quantifier order (statement shape as specified in BRICK Y1b above, with the
two HCG predicates applied at their true signatures — `MetricUniformEquivalentOn` :601,
`MetricCovDerivOrderBoundOn` :691). Do NOT take on `hric`, the Shi producer, or the endpoint.

**Build order (the pinned inventory makes this executable without re-scoping):**
1. **PSD Cauchy–Schwarz helper** (`(g.inner x u v)² ≤ g.inner x u u * g.inner x v v`): FIRST grep
   Mathlib for an applicable form (`inner_mul_le_norm_mul_norm` needs an `InnerProductSpace`
   instance we don't have; look for bilinear-form CS: `LinearMap.BilinForm`, `_root_.abs_inner_le`,
   `mul_self_le` variants, and the project's own `PointwiseInner`/`Comparison` layers — the report
   already found `tensor02_quadForm_abs_le` (Comparison.lean:711), CHECK whether it already IS this
   fact for the metric before writing anything). If genuinely absent: ~15-line discriminant proof
   (`0 ≤ g(u+tv, u+tv)` for all `t`, `discrim_le_zero`), placed as a small public lemma in the
   `Geometry/Metric/PointwiseInner` layer if it states cleanly there (canonical home), else
   `private` in `ExtendShiInputs.lean` (acceptable; note it for relocation).
2. **k = 0 base**: equivalence (`MetricUniformEquivalentOn`) + CS + the fixed `gRef` Gram bound on
   compact `Q` (`chartGramMatrix_entry_isBounded_on_compact`) + the chartGram↔inner bridge
   (`InnerBridge.chartGramBilin_eq_innerJinv`).
3. **k = 1, 2, 3 recursion**: `MetricCovDerivCoordStep.metricCovDeriv_succ_component_coordFrame`
   (the `∂ = ∇_{gRef} + Γ_{gRef}·lower` step) + `coordComponent`↔`chartGram` bridge
   (`Tensor0SInnerBridgeIdentity`) + `normSq0S`→component (`tensor02_quadForm_abs_le`) +
   `Γ_{gRef}`-jet sup-bounds on compact `Q` (continuity of the fixed smooth reference data) +
   `iteratedFDeriv`↔`partialDeriv` via `jet2_chartGram_d1/d2`. NO time integration anywhere.
4. **Uniform-Λ assembly**: collect the finitely many constants; `Λ := max(…) + 1`-style; keep every
   per-`k` bound stated with its constant BEFORE the `∀ g`.

**Rules:** claim `ExtendShiInputs.lean` only (+ the `PointwiseInner` file ONLY if the CS helper
lands there). Off-limits: `HCGCompactness/**` (import-only), `Evolution/ExtendViaUniqueness.lean`
(the reshape is DONE — do not touch), `MaximalTime.lean`, `ShortTime*/`, `DeTurck*`,
`CinftyLimitGlue.lean`, `JetGlueParam.lean`. Verify: focused check + targeted build
`+…ExtendShiInputs`; **acceptance:** adapter sorry-free, `#print axioms` = the 3 standard axioms,
file still 0-sorry, quantifier order confirmed (Λ ∃-bound before the `∀ g`). Stop per CLAUDE.md —
if one of the pinned bridges turns out to have the wrong shape after 3 genuinely different
adaptation attempts, STOP and report the exact mismatch (statement, goal, error) rather than
rebuilding that bridge from scratch.

### Y1b′ SESSION PROGRESS (2026-07-03) — adapter foundations built; full adapter NOT complete

**Verified sorry-free (in `ExtendShiInputs.lean`):**
- `metricInnerSq_le` — Cauchy–Schwarz for the metric's pointwise inner product `(g(u,v))² ≤ g(u,u)g(v,v)`
  (discriminant of the nonneg quadratic `t ↦ g(u+tv,u+tv)`; Mathlib's `InnerProductSpace` CS does NOT
  apply — the tangent space's registered inner product is the ambient one, not `g`).
- `chartGramEntry_le_of_equiv` — the **k=0 core**: from `MetricUniformEquivalentOn Q gRef g C` + a bound
  `M0` on the `gRef` chart-Gram diagonal over `Q`, `|chartGramMatrix g α₀ x i j| ≤ C·M0` uniformly in `g`
  (diagonal via equivalence; off-diagonal via `metricInnerSq_le`).

**NAMESPACE / arg lessons (cost several iterations — pin for next session):**
- `chartGramMatrix`, `chartBasisVecFiber`, `chartGramMatrix_apply` live in
  `DifferentialGeometry.Integral.Measure` (`Geometry/Metric/ChartGram.lean`), NOT top-level. Need
  `open DifferentialGeometry.Integral.Measure`. **`chartBasisVecFiber` REQUIRES `(I := I)`** (its `M`-valued
  args don't determine `I`); **`chartGramMatrix` must NOT be given `(I := I)`** (inferred from the metric).
- `MetricUniformEquivalentOn` / `MetricCovDerivOrderBoundOn` / `MovingShiBoundOn` are in
  `DifferentialGeometry.HCGCompactness` — need `open DifferentialGeometry.HCGCompactness`; do NOT pass `(I := I)`.
- `chartGramMatrix_apply` (`= g.inner x (chartBasisVecFiber α₀ i x) (chartBasisVecFiber α₀ j x)`, a `rfl`
  simp lemma) is the k=0 bridge. `chartGramOnE` (`Integral.DivergenceTheorem`) reduces to `chartGramMatrix`
  via `chartGramOnE_def` (a `rfl`).

**Remaining for `chartJets_of_covBound` (still the bulk; ~250+ lines):**
- **k=0 assembly**: build `M0` via `chartGramMatrix_entry_isBounded_on_compact` (needs `Q ⊆ (chartAt H α₀).source`
  from `hQ` + `chartLeviCivitaGoodSet ⊆ chartSource` via `extChartAt_source`) + finite `max` over the diagonal
  index; reduce `‖iteratedFDeriv ℝ 0 f y‖ = |f y|` (`norm_iteratedFDeriv_zero`); `y = extChartAt I α₀ x`,
  `(extChartAt I α₀).symm y = x` by left_inv on the chart source; then `chartGramEntry_le_of_equiv`.
- **k=1,2,3**: the `∂ = ∇_{gRef} + Γ_{gRef}·lower` recursion (`metricCovDeriv_succ_component_coordFrame`),
  `abs_apply_le_sqrt_normSq0S` (Comparison.lean — pointwise CS `|T(v)| ≤ √normSq0S·∏√g(vₐ,vₐ)`, this IS the
  `metricCovDerivNorm`→component bridge), the `coordComponent↔chartGram` bridge (`Tensor0SInnerBridgeIdentity`),
  Γ-jet sup on `Q`, and the **finite-dim multilinear operator-norm bridge** `‖iteratedFDeriv k f y‖ ≤ C·max|∂ᵏf|`
  — NOT in the project; feasible via `ContinuousMultilinearMap.opNorm_le_bound` + the multilinear expansion of
  `iteratedFDeriv k f y v` over the basis (the genuinely-new sub-piece); k=3 has no `jet3` so needs manual iterate.
- **assembly**: `Λ := max(Λ₀,Λ₁,Λ₂,Λ₃)`, `interval_cases k`.

## PLANNER ACCEPTANCE — ✅ Y1b′-partial ACCEPTED + RULING: restate, don't bridge (Fable, 2026-07-03)

Accepted: `metricInnerSq_le` (:140, metric-PSD Cauchy–Schwarz, discriminant proof — Mathlib's CS
indeed inapplicable: the registered inner product is ambient, not `g`) and
`chartGramEntry_le_of_equiv` (:176, the k=0 core) — both sorry-free, file 0-sorry, build green.
Correct fail-loud stop, again. Two sessions under-delivering the same brick = the PLAN was wrong,
not the executors: my ~150-line estimate missed that the `iteratedFDeriv`-NORM form of the bounds
demands a finite-dim multilinear operator-norm bridge that does not exist in the project.

**RULING (wall-dissolves-on-restatement):** do NOT build the norm bridge. The `iteratedFDeriv` form
has NO consumer outside the (N)/(A)/proof triangle in `ExtendViaUniqueness.lean` (verified), and the
project's canonical chart-jet-bound vocabulary is NESTED `partialDeriv` (the `hp0/hp1/hp2` pattern,
`ExtendedSolutionRegularity.lean`). Entrywise partial bounds are exactly as faithful for the (N)
box (textbook parabolic existence is stated with coordinate-derivative bounds of the coefficient
entries; equivalent to norm bounds up to dimensional constants — the box absorbs them). Restating
DELETES the missing bridge AND the k=3 no-`jet2` issue. The banked k=0 core plugs in directly.

## BRICK Y1b″ — KICKOFF PROMPT (restate + adapter core; dedicated session)

**Paste-pointer:** *"Read `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` — the
pinned inventory/namespace sections and section 'BRICK Y1b″'. Do the restatement, then implement
`chartJets_of_covBound` in the restated form. Report back. Off-limits per the Rules below."*

**Step 1 — the restatement (planner-ruled, sanctioned; `Evolution/ExtendViaUniqueness.lean`).**
Replace the data clause `∀ k ≤ 3, ‖iteratedFDeriv ℝ k (chartGramOnE …) (extChartAt I α₀ x)‖ ≤ Λ`
in BOTH (N) `ricci_flow_unif_existence` and (A)'s `hC3` by the entrywise nested-`partialDeriv` form
(mirroring `hp0/hp1/hp2` of `ExtendedSolutionRegularity.lean`, plus third order), all `≤ Λ` at
`y := extChartAt I α₀ x`, `∀ x ∈ Q α₀`, `∀ i j` and all direction indices `m l p`:
`|chartGramOnE g α₀ i j y|`, `|partialDeriv m (chartGramOnE g α₀ i j) y|`,
`|partialDeriv m (partialDeriv l (chartGramOnE g α₀ i j)) y|`,
`|partialDeriv m (partialDeriv l (partialDeriv p (chartGramOnE g α₀ i j))) y|`.
(Four explicit conjuncts is FINE — clearer than an indexed-list encoding.) Patch (A)'s proof
(local: only the box-hypothesis discharge step changes shape). Re-verify (A) sorry-free.

**Step 2 — `chartJets_of_covBound` in the restated form (`ExtendShiInputs.lean`).** Same statement
skeleton as BRICK Y1b but the conclusion is the four entrywise clauses (Λ-before-`∀ g` order
UNCHANGED — still the trap). Build: k=0 = banked `chartGramEntry_le_of_equiv` + `M0` via
`chartGramMatrix_entry_isBounded_on_compact` + finite max (+ the `extChartAt` left-inverse pin);
k=1,2,3 = the `∂ = ∇_{gRef} + Γ_{gRef}·lower` recursion
(`MetricCovDerivCoordStep.metricCovDeriv_succ_component_coordFrame`) + `abs_apply_le_sqrt_normSq0S`
(confirmed right tool) + the `coordComponent`↔`chartGram` bridge (`Tensor0SInnerBridgeIdentity`) +
`Γ_{gRef}`-jet sup-bounds on compact `Q` (fixed smooth reference data, continuity + `IsCompact`).
NO `iteratedFDeriv`, NO operator norms, NO time integration. Use the namespace pins already
recorded in this note (`Integral.Measure` for `chartGramMatrix`/`chartBasisVecFiber`, `(I := I)`
placement, `open …HCGCompactness`).

**Rules:** claim `ExtendShiInputs.lean` + `Evolution/ExtendViaUniqueness.lean` (restatement only).
Off-limits: `HCGCompactness/**` (import-only), `MaximalTime.lean`, `ShortTime*/`, `DeTurck*`,
`CinftyLimitGlue.lean`, `JetGlueParam.lean`; (N)/(B) bodies stay `sorry`. Verify: focused checks +
targeted builds of both files. **Acceptance:** (A) re-proved sorry-free post-restatement; adapter
sorry-free, axioms = the 3 standard; both files' only sorries = (N)/(B). If the recursion's
component algebra walls after 3 genuinely different attempts on one identity, STOP and report the
exact goal/error — do not widen scope.

### Y1b″ SESSION PROGRESS (2026-07-04) — restatement DONE; adapter k=0 DONE; k=1,2,3 remaining

**Step 1 (restatement) — DONE, verified (targeted build green, 9367 jobs).** In `ExtendViaUniqueness.lean`:
new predicate `ChartJetBoundAt g α₀ i j y Λ` (the 4 entrywise conjuncts: `|chartGramOnE|` +
1st/2nd/3rd nested `partialDeriv`, all `≤ Λ`) + `ChartJetBoundAt.mono` (Λ-weakening). (N) and (A)'s `hC3`
data clauses restated to `∀ α₀∈S, ∀ i j, ∀ x∈Q α₀, ChartJetBoundAt … Λ` (dropped the `∀k≤3
iteratedFDeriv` form). (A)'s proof patched (`hC3_star := (hC3' …).mono hΛ₂le`), **re-proves sorry-free**
— the file's only sorries stay (N):89 + (B):196. The `iteratedFDeriv` norm form (and its missing
finite-dim norm bridge + k=3 jet gap) is now permanently GONE from the route.

**Step 2 adapter — k=0 machinery DONE, verified sorry-free (ExtendShiInputs.lean, file still 0-sorry):**
`metricInnerSq_le` (CS), `chartGramEntry_le_of_equiv` (k=0 core), `exists_gRefDiag_bound` (the `M0`
diagonal bound = finite `∑` of `chartGramMatrix_entry_isBounded_on_compact`), `goodSet_subset_chartSource`,
`chartJet0_le_of_equiv` (the 0-th `ChartJetBoundAt` conjunct: `|chartGramOnE g α₀ i j (extChartAt I α₀ x)|
≤ C·M0`, via the `extChartAt` left-inverse + the k=0 core).

**More namespace pins (this session):** `partialDeriv` is `DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv`
(same namespace as `chartGramOnE`; qualify it); `chartGramMatrix_entry_isBounded_on_compact` is in
`DifferentialGeometry.Analysis.Parabolic.TensorSpectral` (`open` it). `chartGramOnE_def` is the
`chartGramOnE … y = chartGramMatrix … ((extChartAt).symm y) …` reduction; `(extChartAt I α₀).left_inv`
+ `extChartAt_source` collapse it to `chartGramMatrix g α₀ x` on the goodset.

**REMAINING for `chartJets_of_covBound` (the k=1,2,3 conjuncts + assembly):** prove
`|partialDeriv m (chartGramOnE g α₀ i j) y| ≤ Λ` (and 2nd/3rd nested) via the
`∂ = ∇_{gRef}+Γ_{gRef}·lower` recursion (`metricCovDeriv_succ_component_coordFrame`) + the
`coordComponent↔chartGram` bridge (`Tensor0SInnerBridgeIdentity`) + `abs_apply_le_sqrt_normSq0S`
(the `metricCovDerivNorm`→component CS) + `Γ_{gRef}`-jet sup on `Q`; then `Λ := C·M0 ⊔ Λ₁ ⊔ Λ₂ ⊔ Λ₃`
and package the 4 conjuncts. NO `iteratedFDeriv`/operator norms. This is the remaining ~200 lines; the
k=0 machinery above plugs straight into the first conjunct.

## PLANNER ACCEPTANCE — ✅ Y1b″ ACCEPTED (Fable, 2026-07-03): restatement DONE; adapter = final slice
Verified: `ChartJetBoundAt` (:55) + `.mono` (:68) in `ExtendViaUniqueness.lean`; (A) re-proved
sorry-free (sorries = (N):110, (B):222 only); `ExtendShiInputs.lean` 0-sorry with the k=0 machinery
(`exists_gRefDiag_bound` :218, `goodSet_subset_chartSource` :234, `chartJet0_le_of_equiv` :240).
The norm-bridge blocker is permanently gone. **Risk is now fully retired (restatement ✓, k=0 ✓,
every k≥1 ingredient pinned and importable) — per the granularity calibration, the remaining work
is dispatched as ONE consolidated end-to-end session (below), not another partial.**

## BRICK Y1b-FINAL — KICKOFF PROMPT (the whole adapter, end-to-end; last slice)

**Paste-pointer:** *"Read `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` — the
pinned inventory/namespace sections and section 'BRICK Y1b-FINAL'. State and prove
`chartJets_of_covBound` completely. Report back. Off-limits per the Rules below."*

**Scope: deliver the COMPLETE theorem** `chartJets_of_covBound` in `ExtendShiInputs.lean`,
sorry-free, in one session. All risk is retired; this is assembly:
- **Statement**: mirror (A)'s restated `hC3` inner clause EXACTLY — conclusion
  `∃ Λ, 1 ≤ Λ ∧ ∀ g, (∀ a ≤ 3, MetricCovDerivOrderBoundOn Q a g gRef C) → (equiv ≤ C) →
  ∀ x ∈ Q, ChartJetBoundAt g α₀ Λ (extChartAt I α₀ x)`-shaped (READ `hC3`'s exact current form in
  `ExtendViaUniqueness.lean` and copy the predicate application verbatim; Λ-before-`∀ g` order).
- **k=0 conjunct**: banked — `chartJet0_le_of_equiv` (+ `exists_gRefDiag_bound`).
- **k=1,2,3 conjuncts**: the `∂ = ∇_{gRef} + Γ_{gRef}·(lower)` recursion
  (`MetricCovDerivCoordStep.metricCovDeriv_succ_component_coordFrame`) + the
  `coordComponent`↔`chartGram` bridge (`Tensor0SInnerBridgeIdentity`) + `abs_apply_le_sqrt_normSq0S`
  (covariant-norm → component) + `Γ_{gRef}`-jet sup-bounds on compact `Q` (fixed smooth reference:
  continuity + `IsCompact.exists_bound`-style, mirroring `exists_gRefDiag_bound`). Nested orders:
  each `∂^{k}(Gram g)` = polynomial(`Γ_{gRef}`-jets ≤ k−1 [static sups], components of
  `∇^{≤k}_{gRef} g` [≤ C by hypothesis via `abs_apply_le_sqrt_normSq0S`], lower Gram entries).
- **Assembly**: `Λ := (C·M0) ⊔ Λ₁ ⊔ Λ₂ ⊔ Λ₃ ⊔ 1`; package the four conjuncts into
  `ChartJetBoundAt`.
- **Shape smoke-test (mandatory, ~10 lines)**: after proving, add an `example` that, given the
  adapter + arbitrary `S Q` with the compact-cover fact + the covariant/equiv bounds on each
  `Q α₀`, produces `hC3`'s FULL `∀ S, ∀ Q, … → ∃ Λ, …` shape for a constant tail (no time yet —
  bind `t₂ := α` and a trivial `Ico` membership, or take the per-`s` bounds as hypotheses). This
  catches statement drift against (A) immediately; if it does not compile, fix the adapter's
  statement, not (A).
- **Namespace pins (all recorded above)**: `partialDeriv` ∈ `Integral.DivergenceTheorem`;
  `chartGramMatrix`/`chartBasisVecFiber` ∈ `Integral.Measure` (watch the `(I := I)` placement);
  `chartGramMatrix_entry_isBounded_on_compact` ∈ `DifferentialGeometry.Analysis.Parabolic.TensorSpectral`;
  HCG predicates need `open …HCGCompactness`.

**Rules:** claim `ExtendShiInputs.lean` ONLY. `ExtendViaUniqueness.lean` is NOT to be edited (the
restatement is done) — sole exception: a genuine shape mismatch surfaced by the smoke-test that
cannot be fixed adapter-side; then a minimal sanctioned `hC3` patch + re-verify (A) sorry-free, and
say so loudly in the report. Off-limits otherwise unchanged (`HCGCompactness/**` import-only,
`MaximalTime.lean`, `ShortTime*/`, `DeTurck*`, `CinftyLimitGlue.lean`, `JetGlueParam.lean`).
Verify: focused check + targeted build `+…ExtendShiInputs`. **Acceptance:** `chartJets_of_covBound`
sorry-free, axioms = the 3 standard, file 0-sorry, smoke-test `example` present and green. Stop per
CLAUDE.md: if ONE identity in the recursion walls after 3 genuinely different attempts, stop and
report the exact goal/error/lemmas-tried — do not widen scope, do not stub.

## Y1b-FINAL SESSION (2026-07-04): FRAME-MISMATCH WALL — the "assembly" plan is incomplete (4th under-estimation)

**No code changed this session** (file still 0-sorry with the banked k=0 machinery). STOP-and-report per
the brick's own stop-condition, after determining by close reading that the pinned recursion cannot be
assembled into the target.

**The obstruction (structural, not a tactic failure).** The pinned recursion
`MetricCovDerivCoordStep.metricCovDeriv_succ_component_coordFrame` is **frame-DIAGONAL**: at point `x` it
gives `component0S (coordinateFrameAt_toBasis x) (metricCovDeriv h gRef (a+1) x) I0 =
coordDeriv0SAt (coordinateFrameAt x (I0 0)) x (metricCovDeriv h gRef a) (Fin.tail I0) − Σ Γ(gRef)·…`,
where `coordDeriv0SAt (X) x₀ α slots = mfderiv … (fun y => α y (fun a => coordinateFrameAt x₀ (slots a) y)) x₀`
(`NablaComponents/Basic.lean`) and `coordinateFrameAt x₀ = (coordinateTrivializationAt x₀).localFrame …`
(`Coordinates/CoordinateFrame.lean`) — the **chart-at-`x₀`** frame, with the derivative taken in the
`x₀`-chart coordinates. So the recursion lives in the **moving** frame (each eval point `x` uses ITS OWN
chart-at-`x` frame).

The adapter target is `|partialDeriv m (chartGramOnE g α₀ i j) (extChartAt I α₀ x)| ≤ Λ` — the derivative
of `y ↦ g.inner (chartBasisVecFiber α₀ i y) (chartBasisVecFiber α₀ j y)` (pulled back through the chart)
in the **FIXED α₀-chart** coordinates, using the **α₀-frame** vector fields `chartBasisVecFiber α₀`. Since
the derivative of `g.inner(V_i,V_j)` depends on the vector fields `V`, and `coordinateFrameAt x ≠
chartBasisVecFiber α₀` for `x ≠ α₀` (different charts), the moving-frame recursion does NOT equal the
target. Confirmed: NO fixed-`α₀`-chart covariant→chart identity exists — `RealizedJet2CovGradBound.lean`
is `realizeMetricAt`-DIFFERENCE-specialized (not general `g`); `ChartGramChristoffel.lean` is the metric's
OWN Christoffels only (`∇_g g = 0`, no `∇_{gRef}g` term).

**What bridging would require (the missing layer, NOT "assembly").** `Tensor0SInnerBridgeIdentity.lean`:
`chartGramMatrix g α₀ b = chartJinv(α₀,b)ᵀ · gramMatrixAt(g,b) · chartJinv(α₀,b)`, where `chartJinv` is the
chart-change Jacobian (metric-INDEPENDENT). So `partialDeriv^k (chartGramOnE g α₀)` = polynomial in
`∂^{≤k} chartJinv` (fixed reference data, bounded on `Q` by continuity) and `∂^{≤k} gramMatrixAt(g)`
(moving-frame Gram derivatives → the recursion). The adapter therefore needs a **chart-Jacobian jet layer**
(`chartJinv` derivatives up to order 3, bounded on `Q`, + the change-of-frame Leibniz expansions) on top of
the recursion. That is a genuine additional brick, ~as large as the recursion itself — the "assembly"
estimate omitted it entirely.

**Smallest unblock (planner decision needed).** One of:
- **(a)** a **fixed-center** variant of `metricCovDeriv_succ_component_coordFrame` (frame `coordinateFrameAt
  α₀`, derivative at `x`) — i.e. an off-diagonal coordinate-component recursion — proved in the
  `Coordinates/NablaComponents` layer; then the adapter IS assembly. This is the clean fix but a real new
  lemma in that layer.
- **(b)** the `chartJinv`-jet layer above (bound `∂^{≤3} chartJinv` on `Q`, expand the triple product);
  more terms, all metric-independent/bounded, but a substantial brick.
- **(c)** reconsider whether `hC3` should instead be phrased in the **moving-frame** covariant-component
  form (matching the recursion directly), pushing the fixed-α₀-chart conversion into the (N) black box
  (where DeTurck existence lives) — another sanctioned restatement, analogous to the iteratedFDeriv→partialDeriv one.
Classification: **missing groundwork/API** (the fixed-α₀ chart covariant-derivative identity), a real
math/infra obstruction — not a local proof-search or coercion issue. The banked k=0 machinery
(`chartJet0_le_of_equiv` etc.) is unaffected and plugs into whichever route is chosen.

## PLANNER ACCEPTANCE — ✅ Y1b-FINAL stop ACCEPTED + RULING: covariant restatement, ADAPTER DELETED (Fable, 2026-07-03)

Accepted: correct definitional stop (frame-diagonal recursion — `coordinateFrameAt x` moving frame —
vs the fixed-α₀ chart target; verified `coordinateFrameAt` in `Coordinates/CoordinateFrame.lean:186`
and no fixed-α₀ covariant→chart identity in the tree). No edits, lock released, file still 0-sorry.
Fifth consecutive under-estimate on this brick ⟹ the CHART FORM ITSELF was the mistake, not any
particular bridge.

**RULING (option 3-strong).** Restate the bound clause in the producer's own intrinsic vocabulary —
`MetricCovDerivOrderBoundOn` (verified: `K : Set M`, `∀ x ∈ K, metricCovDerivNorm a h gRef x ≤ C`;
take `K := Set.univ`, `M` compact). Consequences, all sanctioned:
- **(N) `ricci_flow_unif_existence`**: data clause becomes
  `∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Set.univ a g₀ gBase Λ` (keep the existing inline
  ellipticity clause). **DELETE the `∃ S, ∃ Q` compact-cover apparatus entirely** — it existed only
  for chart-locality. (N) becomes: `∀ Λ ≥ 1, ∃ τ₀ > 0, ∀ g₀, (ellipticity Λ) → (covariant Λ-bounds
  ≤ order 3) → flow ≥ τ₀`. This is the MORE canonical textbook statement — "uniform short-time
  existence under bounded geometry relative to a fixed background" — and the honest accounting is
  that the covariant→chart conversion (true, standard coordinate bookkeeping) moves INSIDE the cited
  axiom, where the rest of the parabolic machinery already lives. Non-circularity unaffected.
- **(A) `ricci_flow_interior_restart`**: `hC3` → `hcov : ∃ C ≥ 1, ∃ t₂ ∈ Set.Ico α omega,
  ∀ s ∈ Set.Ico t₂ omega, ∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Set.univ a (g_fam s) (g_fam α) C`.
  Patch (A)'s proof — SIMPLER now (all S/Q plumbing gone).
- **DELETE `ChartJetBoundAt` + `.mono`** (no consumer remains). In `ExtendShiInputs.lean` KEEP
  `metricInnerSq_le` (reusable metric-CS) and keep the now-unconsumed chart-k=0 lemmas with an
  "unconsumed, banked" note (tree is uncommitted; do not destroy verified work).
- **Import**: `Evolution/ExtendViaUniqueness.lean` now imports `HCGCompactness.AllTimesBounds`
  (cycle-free — verified earlier: AllTimesBounds' closure never touches this branch; the dependency
  footprint is unchanged since Y2/MaximalTime consumes HCG anyway). Directory-nominal inversion
  accepted and documented in the module docstring.
- **TERMINAL iteration**: this is the 4th and LAST (N)/(A) statement change — the hypothesis now
  speaks Lemma 3.11's exact output language. Any residual mismatch (window `[β,ψ]` vs tail
  `Ico t₂ ω`, constant bookkeeping) is absorbed PRODUCER-side in Y1c, never by another restatement.
- **Plan effect**: the adapter brick is DELETED (second major deletion after W). Zero genuinely-new
  lemmas remain on the route: what's left is the restatement (below), Y1c (cited Shi producer shape
  + single-flow 3.11 instantiation + `hric` + endpoint), Y2 (rewiring).

## BRICK Y1-COV — KICKOFF PROMPT (the covariant restatement; small session, then start Y1c if room)

**Paste-pointer:** *"Read `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` — the
RULING above and section 'BRICK Y1-COV'. Do the covariant restatement; then begin Y1c (read the
`metricCovOrderWindow_of_*` hypotheses and shape the cited Shi producer) if the session has room.
Report back."*

1. In `Evolution/ExtendViaUniqueness.lean`: add the `HCGCompactness.AllTimesBounds` import (+
   `open DifferentialGeometry.HCGCompactness` scoped as needed); restate (N)'s data clause and (A)'s
   `hC3 → hcov` per the RULING verbatim; delete `ChartJetBoundAt` + `.mono` and the `∃ S, ∃ Q`
   apparatus; patch (A)'s proof; docstring note on the import inversion. Re-verify: focused check +
   targeted build; (A) sorry-free; file sorries = (N)/(B) only; `grep ChartJetBoundAt` → 0 hits.
2. In `ExtendShiInputs.lean`: add the "unconsumed, banked" note over the chart-k=0 lemmas (no
   deletion); file stays 0-sorry.
3. If room, Y1c step 1 (READ ONLY, then report): the exact hypotheses of
   `metricCovOrderWindow_of_pointwise/_of_evolution` (`AllTimesBounds.lean:793/4168/4403`) and what
   the single-flow instantiation needs — this fixes the cited Shi producer's statement for the Y1c
   session. Do NOT stub the producer before this read.
**Rules:** claim both files. Off-limits unchanged (`HCGCompactness/**` import-only, `MaximalTime.lean`,
`ShortTime*/`, `DeTurck*`, `CinftyLimitGlue.lean`, `JetGlueParam.lean`); (N)/(B) bodies stay `sorry`.
**Acceptance:** (A) re-proved sorry-free in the covariant form; `ChartJetBoundAt` gone; both files
build green with only the (N)/(B) sorries.

## BRICK Y1-COV — DONE (2026-07-04), verified green (targeted build, 9459 jobs)

The covariant restatement landed exactly per the RULING:
- `Evolution/ExtendViaUniqueness.lean` now imports `HCGCompactness.AllTimesBounds` (`open …HCGCompactness`)
  — **cycle-free, build green** (docstring note on the sanctioned import inversion added).
- **`ChartJetBoundAt` + `.mono` DELETED** (`grep ChartJetBoundAt` = 0 hits in both `.lean` files).
- **(N) `ricci_flow_unif_existence`** restated: the whole `∃ S, ∃ Q` chart-cover apparatus is gone; the
  data clause is now `∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Set.univ a g₀ gBase Λ`.  (N) is the
  canonical "uniform short-time existence under bounded geometry vs a fixed background."
- **(A) `ricci_flow_interior_restart`**: `hC3 → hcov : ∃ C ≥ 1, ∃ t₂ ∈ Ico α ω, ∀ s ∈ Ico t₂ ω,
  ∀ a ≤ 3, MetricCovDerivOrderBoundOn Set.univ a (g_fam s) (g_fam α) C`.  Proof simplified (S/Q plumbing
  gone); `hcov_star` weakens `C → Λ` via `.trans hΛ₂le`.  **Re-proves sorry-free.**
- `ExtendShiInputs.lean`: the chart-`k=0` lemmas kept with a "BANKED / UNCONSUMED" note; **still 0-sorry**.
- File sorries now = exactly (N) `:74` + (B) `:175` (the file shrank when the apparatus was deleted).

**Terminal statement iteration reached** — (N)/(A) now speak Lemma 3.11's exact output vocabulary.
With the adapter deleted, **zero genuinely-new lemmas remain on the route**.

## Y1c — step-1 READ done (cited Shi producer shape)

`metricCovOrderWindow_of_pointwise` (`AllTimesBounds.lean:793`) is a TRIVIAL packager:
`(∀ i t∈[β,ψ], ∀ x∈K, metricCovDerivNorm a (gSeq i t) gRef x ≤ C) → MetricCovDerivOrderBoundOnWindow …`.
So `MetricCovDerivOrderBoundOn K a h gRef C` IS just the pointwise `∀ x∈K, metricCovDerivNorm a h gRef x
≤ C` — and (A)'s `hcov` is exactly that on `univ` for a single flow over a tail.  **Consequence for Y1c:
NO window↔tail conversion, NO sequence instantiation needed** — the cited Shi producer's target is
`hcov` **verbatim**: `∃ C ≥ 1, ∃ t₂ ∈ Ico α ω, ∀ s ∈ Ico t₂ ω, ∀ a ≤ 3, MetricCovDerivOrderBoundOn univ
a (g_fam s) (g_fam α) C`, a single cited black box (Shi's `‖∇ᵏRm‖≤Cₖ` + the standard curvature→metric
covariant-derivative bookkeeping, GSM77 Ch.7 / Chow–Knopf).  The window producers
(`metricCovOrderWindow_of_evolution` :4403, `metricMixedOneWindow_of_ric_bound`) are the eventual
DISCHARGE route (evolution predicate from the solution), not needed for the cited-hypothesis shape.
Y1c = state that producer (sorry, cited) + `hric` + endpoint `extendInputs_of_soln = ⟨hell_of_soln, that⟩`.

## BRICK Y1c — DONE (2026-07-05), verified green (targeted build 9459 jobs + `#print axioms`)

Three declarations added to `ExtendShiInputs.lean` (imports `Geometry.Curvature.RicciOperatorNormBound`;
`open Tensor0SBundle`):
- **`ric_quad_le_of_rm04` — the one real Y1c proof, SORRY-FREE** (`#print axioms` = the 3 standard,
  no `sorryAx`). `|ricciTensor g x v v| ≤ (n²√C)·g(v,v)` from a `g`-orthonormal basis in which
  `metricRicciAt g = trace(Rm04)` (`htrace`) + `normSq0S Rm04 ≤ C`.  Composes
  `ricci_unitQuad_le_of_trace` (`‖Ric‖ from ‖Rm‖`) → `tensor02_quadForm_abs_le_of_unit_bound`
  (unit-sphere → quadratic form) → `metricRicciAt_apply_eq_ricciTensor`.  This is exactly Brick X's
  `hric`, `K := n²√C`.  (Namespace pins that cost iterations: `MetricInverseInBasis_gen`,
  `identityInvMetric`, `normSq0S` are all in the top-level `Tensor0SBundle` namespace — `open` it.)
- **`shiCovBound_of_soln` — the THIRD & FINAL cited black box (`sorry`, GSM77 Ch. 7 Shi estimates;
  eventual discharge = the banked Bernstein tower).**  Raw hypotheses (`IsSolutionOn` + raw `|Rm|²`
  bound) → `hcov` verbatim (`∃ C≥1, ∃ t₂∈Ico α ω, ∀ s∈Ico t₂ ω, ∀ a≤3, MetricCovDerivOrderBoundOn univ
  a (S.base.metric s) (S.base.metric α) C`).
- **`extendInputs_of_soln` — the endpoint, sorry-free body** (`#print axioms` `sorryAx` traces ONLY to
  `shiCovBound_of_soln`).  `⟨hell_of_soln hS hK hric, shiCovBound_of_soln Rm04 hS hbound⟩` — the exact
  `⟨hell, hcov⟩` tuple `ricci_flow_interior_restart` consumes, in raw-hypothesis form (Y2 bridges
  `_hS`/`_hRm`/`_hbound`; `hric` discharged by `ric_quad_le_of_rm04` + the realization at the Y2 site).

**Route ledger now:** the three cited black boxes are (N) `ricci_flow_unif_existence`, (B)
`ricci_flow_forward_unique`, and (Y1c) `shiCovBound_of_soln`.  Everything else on the interior-restart
route is proved sorry-free.  Remaining: **Y2** — rewire `MaximalTime.extends_of_rmBounded` to consume
`extendInputs_of_soln` → (A) → (B) → Brick U → `isSolutionOn_of_extendData` → `ExtendsPastEndpoint`,
bridging the raw hypotheses from `_hS`/`_hRm`/`_hbound` and discharging `hric` via `ric_quad_le_of_rm04`.

## SHI DISCHARGE PLAN (planner, 2026-07-04) — retiring the third cited box

**Goal:** replace `shiCovBound_of_soln`'s `sorry` by a proof whose only remaining citation is the
project-wide canonical Shi interface **`MovingShiBoundOn`** (`HCGCompactness/RicBound.lean:141` —
"the single honest analytic FRONTIER of the eq.(3.4) track", the SAME predicate the HCG P2 lane
cites as `hShi`). End state: ONE Shi citation for the whole project, discharged once by the
Bernstein tower for everyone. Verified shapes: `MovingShiBoundOn U β ψ gSeq N KShi =
∀ s ≤ N, ∀ i, ∀ t ∈ Icc β ψ, ∀ x ∈ U, √(normSq0S (gSeq i t) x (2+s) (ricCovTower (gSeq i t)
(gSeq i t) s x)) ≤ KShi` (Ric-tower in the MOVING metric);
`metricCovOrderWindow_of_evolution` (`AllTimesBounds.lean:4403`) consumes the bundled
`MetricCovOrderEvolutionInput K β ψ t0 gSeq gRef p` (fields incl. `Cpp Cppp timeRadius initC
nablaRic normsq_evol t0_mem`) and outputs `MetricCovDerivOrderBoundOnWindow` with constant
`metricCovOrderEvolutionConstant Cpp Cppp timeRadius initC`.

### Phase S1 (wiring, ~1–2 sessions): single-flow Lemma-3.11 instantiation

`shiCovBound_of_soln` ⇐ `metricCovOrderWindow_of_evolution` at `gSeq := fun _ t => g_fam t`,
`gRef := g_fam α`, orders `p ≤ 3`. Work items:
1. READ `MetricCovOrderEvolutionInput`'s fields and locate the HCG lane's producers for them —
   especially `normsq_evol` (the evolution differential inequality for `‖∇ᵖ_{gRef} g‖²`; grep its
   producers in `AllTimesBounds.lean` — the HCG lane builds it from the flow PDE + `MovingShiBoundOn`).
2. Build the single-flow Input from: the new cited decl
   `movingShi_of_soln : MovingShiBoundOn Set.univ t₂ ψ (fun _ t => g_fam t) N K_Shi` (`sorry`,
   GSM77 Ch. 7; N per what the Input's `nablaRic` field demands for `p ≤ 3` — likely `N = 3`),
   the PDE (`ricciFlowPDE_Ici_of_soln`), and `initC` (the `t0`-value bound — finite by continuity
   on compact `M`; if a producer exists in the HCG lane, reuse).
3. Window→tail bookkeeping: producers run on closed `[β,ψ]`; `hcov` wants `Ico t₂ ω`. Check the
   constant's `ψ`-dependence: `timeRadius`-type inputs are bounded by `ω − t₂` uniformly in `ψ < ω`
   ⟹ one constant works for all `ψ`; take the union over `ψ ↑ ω`. If a producer's constant
   genuinely blows up in `ψ`, STOP and report (that would be a real statement problem).
4. Endpoint: `shiCovBound_of_soln := proof from movingShi_of_soln`; the route's third box becomes
   `movingShi_of_soln` — citation unified with HCG `hShi`.

### BRICK S1 — SCOPE FINDING (2026-07-06, executor): S1 is under-scoped; two real blockers, STOP for planner ruling

Scoped the wiring end to end (read `covOrderBound_of_soln` RicBound:1179, `ric_bound_field` :777,
`metricCovOrderWindow_of_evolution` / `MetricCovOrderEvolutionInput` AllTimesBounds:4369/4403,
`metricCovOrderEvolutionConstant` :4305, `MetricCovDerivOrderBoundOn(Window)` :691/:773, the two
`covOrderBound_of_soln` consumers). **No code written** (pure scoping; claim released). Two blockers:

**Blocker 1 — the equivalence gap (design/interface).** EVERY covariant-order producer
(`covOrderBound_of_soln`, `covOrderBound_tower`, `ric_bound_field`) requires
`hequiv : MetricUniformEquivalentOnWindow U β ψ gRef gSeq B` — the metric equivalence — to convert the
MOVING-metric `MovingShiBoundOn` bound into the fixed-`gRef`-norm `ric_bound`. `shiCovBound_of_soln`
CANNOT build it from its current inputs `(Rm04, _hS, _hbound)`: the equivalence is `hell` (ellipticity),
which needs the pointwise Ricci-vs-metric bound `hric`, which needs the realization `_hRm` — absent from
`shiCovBound_of_soln`'s signature. Fix (feasible): thread `hell` (already produced by
`hell_of_soln` inside `extendInputs_of_soln`) into `shiCovBound_of_soln` as a hypothesis and convert to
`MetricUniformEquivalentOnWindow`; `extendInputs_of_soln`'s PUBLIC signature stays stable. The plan's
item 2 omitted this input.

**Blocker 2 — the ψ-uniform tail (the real obstruction; item-3 STOP condition hit, but for a subtler
reason than "constant blows up").** `shiCovBound_of_soln`'s output is a **tail** bound
`∀ s ∈ Ico t₂ ω, … ≤ C` with ONE `C`. HCG's producers give only **Window (`Icc β ψ`) bounds with an
EXISTENTIAL constant** (`covOrderBound_of_soln`/`_tower` conclude `∀ r ≤ N, ∃ Cw, …Window…`); there is
**no tail/all-times producer and no explicit-constant accessor** (verified: the two consumers use the
Window bound at a single fixed `t`, from a packaged `H.pack`, never a uniform tail). The underlying
constant `metricCovOrderEvolutionConstant Cpp Cppp timeRadius initC = √(exp(α·timeRadius)·(initC²+β/α))`
IS ψ-uniform — monotone in `timeRadius`, so `timeRadius := ω − t₂` dominates every `[t₂,ψ]`, ψ<ω — but
it is only reachable through `metricCovOrderWindow_of_evolution`'s EXPLICIT constant, which needs the
full `MetricCovOrderEvolutionInput` INCLUDING the lower-order tower (`ric_bound_field`'s `hBprev`/`Cg`).
The only HCG path that assembles that tower (`covOrderBound_tower`) re-hides the constant existentially.
So a clean ψ-uniform tail needs either **(a) replicating the explicit-constant order-tower in
ExtendShiInputs** (per order ≤ 3: `nablaRicReal` + `normsq_evol_of_comp` [needs the flow-evolution `hev`,
reuse `hevComp_of_solutions`/`solnTowerSwap_reg`] + `ric_bound_field` + `initC`-by-continuity, threaded
through `metricCovOrderWindow_of_evolution` tracking the constant) — **this is S2-scale, not "wiring"**;
or **(b) adding a uniform-constant / tail-form producer to the HCG lane** — violates "HCG import-only".
Plus **initC** (the `t0`-value bound, `metricCovDerivNorm r (g_fam t₂) gRef x ≤ initC r` uniform in x) is
a genuine compactness/continuity sub-brick, not free.

**PLANNER DECISIONS NEEDED before S1 can proceed:** (1) bless the `hell`→`shiCovBound_of_soln` interface
change; (2) choose the uniform-constant route — (a) executor replicates the explicit-constant tower in
ExtendShiInputs (accept S2-scale here), (b) relax import-only to add one explicit-constant/tail HCG
producer, or (c) reformulate the route's `hcov`/`shiCovBound` to a per-window shape and relocate the
tail-uniformity obligation (note (A) `ricci_flow_interior_restart` currently consumes the TAIL form, so
this pushes the problem, not removes it). Classification: not a local proof failure — a scope/design
finding. Recommend (2a) folded into S2 (the tower is S2's content anyway) OR (2b) if the planner will
own one small HCG addition.

## PLANNER RULING on the S1 scoping stop (Fable, 2026-07-06)

**Blocker 1 — APPROVED.** Thread `hell` into `shiCovBound_of_soln`. `extendInputs_of_soln`'s PUBLIC
signature stays unchanged — it already holds `hell_of_soln hS hK hric`'s output internally, so it passes
that to `shiCovBound_of_soln` for the `hcov` slot. Inside `shiCovBound_of_soln`, convert `hell` (the
ellipticity `∃ Λ≥1, ∃ t₁∈Ico α ω, ∀ s∈Ico t₁ ω, ∀ x v, Λ⁻¹ g_α(v,v) ≤ g_s(v,v) ≤ Λ g_α(v,v)`) into the
`MetricUniformEquivalentOnWindow` shape the covariant-order producers demand.

**Blocker 2 — route (2b), NARROWED.** Allowed: create **exactly one** new self-contained file
`HCGCompactness/CovOrderTail.lean`. FORBIDDEN: editing ANY existing HCG file, and (2a) replicating the
tower in the extension lane. Rationale: the **canonical-home rule overrides import-only** — a
ψ-uniform / explicit-constant statement is a *corollary of the window machine* and belongs in that layer;
doing it in the extension lane would be a forbidden parallel API. Coordination risk ≈ 0: the Codex lane's
live bricks are in `MetricPreconv*` / `StepC` / `GoodCovering`; `AllTimesBounds` / `RicBound` are stable
P2-era files, and the new file only IMPORTS them. The new file's header MUST note it is an
"extension-lane consumer corollary, NOT part of the P2/P3 brick flow." Three contents:
  - **(i)** a **constant-tracking** version of the `covOrderBound_tower` skeleton whose conclusion constant
    depends only on `KShi, N`, the equivalence constant, `initC`, and `timeRadius ≤ ω − t₂` — **NOT on ψ**
    (via the confirmed monotonicity of `metricCovOrderEvolutionConstant = √(exp(α·timeRadius)·(initC²+β/α))`
    in `timeRadius`). Reuse the existing sub-producers (`ric_bound_field`, `metricCovOrderWindow_of_evolution`,
    `normsq_evol_of_comp`, `hevComp_of_solutions`, `solnTowerSwap_reg`, `nablaRicReal`) — the ONLY new content
    is inducting over order with the EXPLICIT constant tracked instead of `∃`-hidden.
  - **(ii)** the `hcov`-shaped **`Ico`-tail corollary**: from (i)'s per-`ψ` Window bound with the ψ-uniform
    constant, take `ψ ↑ ω` (for `s ∈ Ico t₂ ω` pick `ψ ∈ (s,ω)`), yielding ONE constant on the whole tail.
  - **(iii)** the **`initC` sub-lemma**: `∀ r, ∃ initC r, ∀ x∈univ, metricCovDerivNorm r (g_fam t₂) gRef x ≤
    initC r` — continuity of the fixed smooth pair `(g_fam t₂, gRef)` on compact `M` ⟹ bounded.
  **Fallback:** if the constant-tracking tower (i) fails **3 genuinely-different structured attempts**, STOP
  and report; the route becomes (2a) **folded into S2** (the tower is S2's content anyway).

**Blocker-alternative (2c) — REJECTED** (harder than the executor's read): (A) `ricci_flow_interior_restart`
fixes `C` *before* `t_star` is chosen (the box's `Λ → τ₀ → t_star` order), so a per-window `C(ψ)` breaks
the quantifier structure. The tail-uniform constant is real mathematics and must not be weakened for
interface convenience.

**Citation shape — FIXED (ψ-uniform tail form).** The new cited box is
```
movingShi_of_soln : ∃ KShi, ∃ t₂ ∈ Set.Ico α ω, ∀ ψ ∈ Set.Ico t₂ ω,
    MovingShiBoundOn (I := I) Set.univ t₂ ψ (fun _ t => g_fam t) N KShi
```
— a **single** `KShi` (honest: the Shi constant depends only on the curvature bound and elapsed time
`≤ ω − t₂`). `N` is fixed by what the tower's `nablaRic` input actually needs for orders ≤ 3 — READ it
first, expected `N = 3`.

## BRICK S1b — KICKOFF (execute the ruling)

Goal: `shiCovBound_of_soln` sorry-free; the extension lane's ONLY sorries become `(N)
ricci_flow_unif_existence`, `(B) ricci_flow_forward_unique`, and the new `movingShi_of_soln`.

Pre-scoped producer map (verified locations; reuse, do NOT re-derive):
- `covOrderBound_of_soln` `RicBound.lean:1179` (the `∃`-constant tower — reference for the skeleton and
  the exact input list: `hKc hU hKU N D S hS hmet hreg B hequiv Bmax hBmax1 hBmax KShi hKShi0 hShi ht0
  hDreg initC hinitC0 hinit timeRadius htime`).
- `covOrderBound_tower` `RicBound.lean:1104` (the induction body to mirror **with constant tracking**).
- `ric_bound_field` `RicBound.lean:777` (needs `hequiv` + `hBprev : ∀ r<N, MetricCovDerivOrderBoundOnWindow
  … r (Cg r)` — the lower-order bounds; check whether its `Cpp/Cppp` depend on the `Cg` *values* or only
  their existence — that decides how the constant compounds).
- `metricCovOrderWindow_of_evolution` `AllTimesBounds.lean:4403`, `MetricCovOrderEvolutionInput` `:4369`
  (fields `t0_mem nablaRic normsq_evol Cpp Cppp {non­neg} ric_bound initC init_bound timeRadius time_abs_le`),
  `metricCovOrderEvolutionConstant` `:4305` (the explicit ψ-monotone constant), `metricCovOrderEvolutionAlpha/Beta`.
- `normsq_evol_of_comp` `RicBound.lean:811` (builds `normsq_evol` from the componentwise flow evolution
  `hev`; the single-flow `hev` is `hevComp_of_solutions` + `solnTowerSwap_reg`, as inside `covOrderBound_of_soln`).
- `MetricCovDerivOrderBoundOnWindow` `AllTimesBounds.lean:773` = `∀ i, ∀ t∈Icc β ψ, MetricCovDerivOrderBoundOn
  K a (gSeq i t) gRef C`; `MetricCovDerivOrderBoundOn` `:691` = `∀ x∈K, metricCovDerivNorm a h gRef x ≤ C`
  (= `shiCovBound_of_soln`'s output atom).
- `MovingShiBoundOn` `RicBound.lean:141`; `MetricUniformEquivalentOnWindow` (grep its def for the `hell`→it
  conversion — two-sided ratio bound on the window).

Single-flow instantiation: `gSeq := fun _ t => g_fam t` (`= S.base.metric t`), `gRef := g_fam α`,
`K = U = Set.univ`, `D := fun _ => closedOpen α ω hαω`, `S := fun _ => S`, `t0 := t₂` (pick `t₂∈(α,ω)`),
`β := t₂`, and on window `[t₂, ψ]` take `timeRadius := ω − t₂` (dominates every `|t−t₂|`, ψ<ω). `hmet =
fun _ _ => rfl` (via `SolutionOn.family`), `hreg`: `Icc t₂ ψ ⊆ Ioo α ω` needs `α < t₂ ∧ ψ < ω`, `hDreg`:
`Ioo α ω ∈ 𝓝` (open). `hequiv` from threaded `hell`; `hShi` from `movingShi_of_soln`; `initC` from (iii).

Order 0 is separate from the `1 ≤ r` tower — handle `a = 0` directly (it is `metricCovDerivNorm 0 =
‖g_fam s − g_fam α‖`-type, controlled by `hell` / order-0 continuity) and take the max with the tower
constants for the single `C ≥ 1` in `shiCovBound_of_soln`'s output.

Acceptance: `shiCovBound_of_soln` sorry-free; extension-lane sorries = exactly `(N)`, `(B)`,
`movingShi_of_soln`; targeted build of `CovOrderTail` + `ExtendShiInputs` green; `#print axioms` on
`extendInputs_of_soln` shows `sorryAx` via those three only. Report the new constant's FULL parameter
table (which of `KShi, N, Λ/equiv-const, initC r, ω−t₂` it depends on, and how). Claim only
`CovOrderTail.lean` (new) + `ExtendShiInputs.lean`; HCG existing files import-only.

### BRICK S1b EXECUTOR STOP (2026-07-08): constant-tracking field API gap

S1b stopped before Lean edits.  The `hell` threading is routine, and the single-flow instantiation
shape remains correct, but the required ψ-uniform covariant-order tail cannot be proved from the
current public HCG interfaces without either editing `RicBound.lean` or reimplementing its private
constants-first field proof in the new consumer file.

Failed structured routes:
- Reusing `covOrderBound_tower` / `covOrderBound_of_soln` gives only `∀ ψ, ∀ r, ∃ Cw`; it does not
  expose a single constant before ψ, so it cannot feed the `Ico t₂ ω` tail output.
- Rebuilding the whole-manifold tower in `CovOrderTail.lean` with `covOrderBound_stage` still calls
  `ric_bound_field`; its `Cpp, Cppp` are chosen after the window parameter ψ and the window proofs,
  so Lean cannot promote the resulting per-ψ constants to one ψ-uniform constant.
- Trying to build a constants-first field theorem from public APIs reaches the missing bridge:
  `RicBound.lean`'s constants-first engine `perDomain` is private, while public
  `ric_bound_field` hides the finite-cover constants existentially.  Reimplementing that proof in
  `CovOrderTail.lean` would violate the ruling that the new file only tracks the tower constant and
  reuses the existing field producer.

Smallest next lemma/API: add a public constants-first companion to `ric_bound_field` in the HCG
layer, or refactor `ric_bound_field` to return named `Cpp, Cppp` determined before β/ψ/window
proofs from only `gRef`, `N`, `Bmax`, lower-order constants `Cg`, and `KShi`.  Once that exists,
`CovOrderTail.lean` can carry the whole-manifold induction, use `metricCovOrderEvolutionConstant`
with `timeRadius := ω - t₂`, and then take the `Ico` tail by choosing `ψ ∈ (s,ω)`.

Progress estimate: `shiCovBound_of_soln` remains 0% discharged; S1b's dedicated implementation is
0% (no Lean file landed); the missing constants-first `ric_bound_field` companion is the next
producer API and is likely a small-to-medium HCG-layer refactor, not a local tactic proof.  The
extension-lane S1 unification remains blocked behind that API; the wider HCG compactness project
percentages are unchanged by this stop.

Verification: no Lean file was changed; no Lean check was run.

### Phase S2 (the tower — the real mathematics): discharge `MovingShiBoundOn` for the single flow

From the raw `|Rm|² ≤ K'` bound (`_hbound`), via the banked Bernstein machinery, at `N ≤ 3`,
`dim = 3` (`hdim` is available in `extends_of_rmBounded`):
- Banked sorry-free (tasks #11–38): Bernstein max-principle core, general-m G-induction, all-k
  heatEq bridge (`IteratedRmTowerOn`), curvature-norm evolution producers, the generic Bochner
  stack, rank-uniform realization bridges.
- Remaining bricks (truncate the old all-k plan to k ≤ 3): (i) spatial decomposition
  `[Δ,∇ᵏ]Rm ∈ StarSum2 k` for k ≤ 3 (task #42, in progress); (ii) the Uhlenbeck base `∂ₜRm04`
  3D-algebraic route (task #43 — `hdim = 3` suffices, the general-dim route stays deferred);
  (iii) time recursion `E_k = (∂ₜ−Δ)∇ᵏRm ∈ StarSum2 k`, k ≤ 3 (task #44); (iv) assembly:
  `∇ᵏRm` bounds → `∇ᵏRic` by contraction → the `ricCovTower`/`MovingShiBoundOn` shape (task #46
  + a Ric-from-Rm tower contraction bridge).
- **Standing regularity inputs** (`hSt`/`hswap`, flagged in `BBSLimitProducer.md` as
  not-derivable-from-`IsSolutionOn`): re-assess at k ≤ 3. If still needed they surface as NAMED
  sub-citations (DeTurck-lane facts) — do not bury them inside the tower proofs.
- Estimate: 3–6 focused sessions on the banked machinery. The k ≤ 3 truncation is the point —
  do NOT resume the all-k grind.

**Sequencing:** S1 first (small; unifies the citation and de-risks the interface); S2 as its own
brick series after S1 fixes `movingShi_of_soln`'s exact (U, β, ψ, N) shape. (N)/(B) remain
user-owned DeTurck-lane decisions, untouched by this plan.

### PLANNER RULING on the S1 scoping stop (Fable, 2026-07-04) — both blockers answered

Verified: `covOrderBound_tower` (RicBound:1104, existential constants), `covOrderBound_of_soln`
(:1179), `metricCovOrderEvolutionConstant` (AllTimesBounds:4305, monotone in `timeRadius` ⟹
ψ-uniform on the tail). The stop was correct; S1 as written was under-scoped. Decisions:

1. **Blocker 1 — BLESSED.** Thread the equivalence into `shiCovBound_of_soln` (add the `hell`-shaped
   hypothesis; `extendInputs_of_soln`'s public signature unchanged — it already holds `hell` from
   `hell_of_soln`).
2. **Blocker 2 — route (2b), SCOPED: one NEW self-contained file under `HCGCompactness/`**
   (`CovOrderTail.lean`), and NOTHING else changes in the HCG lane. Rationale: the canonical-home
   rule — a ψ-uniform/explicit-constant corollary of the window machinery belongs NEXT TO that
   machinery; replicating it in the extension lane would be a forbidden parallel API. Coordination:
   zero edits to existing HCG files (the Codex lane's live bricks are `MetricPreconv*`/StepC/
   GoodCovering, not the P2-era stable `AllTimesBounds`/`RicBound`); the new file's header marks it
   "extension-lane consumer corollary — not part of the P2/P3 brick flow". Contents:
   (i) a constant-tracked variant of the `covOrderBound_tower` skeleton whose conclusion exposes a
   constant depending only on `(KShi, N, hequiv-constant, initC, timeRadius ≤ ω − t₂)` — NOT on ψ
   (use `metricCovOrderEvolutionConstant`'s monotonicity in `timeRadius`);
   (ii) the tail corollary in exactly `hcov`'s shape (`Ico t₂ ω` union over `ψ ↑ ω`, one constant);
   (iii) the `initC` sub-lemma (the `t₀`-value bound uniform in `x` — continuity of the fixed
   smooth pair `(g_fam t₀, gRef)`'s covariant norms on compact `M`).
   **Fallback:** if constant-tracking the tower skeleton fails after 3 genuinely different
   structurings, STOP, report, and we fold S1 into S2 in the extension lane (option 2a) instead.
3. **Citation shape PINNED (ψ-uniform tail form):** `movingShi_of_soln : ∃ KShi, 0 ≤ KShi ∧
   ∃ t₂ ∈ Set.Ico α omega, ∀ ψ ∈ Set.Ico t₂ omega, MovingShiBoundOn Set.univ t₂ ψ
   (fun _ t => g_fam t) N KShi` (ONE `KShi` for all ψ — faithful: Shi's constants depend on the
   curvature bound and the elapsed time, both uniform on `[t₂, ω)`). `N` = whatever order the
   tower's `nablaRic` inputs demand for metric orders `≤ 3` (read it; likely `N = 3`).
4. **(2c) REJECTED** — (A)'s proof needs the constant before `t_star` is chosen (the box's `Λ → τ₀ →
   t_star` order); a per-window `C(ψ)` breaks that quantifier structure. The tail-uniform constant
   is true mathematics, not an interface convenience — state it, don't weaken it.

### BRICK S1b — KICKOFF PROMPT (supersedes S1)

*"Read `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` — sections 'SHI DISCHARGE
PLAN' and 'PLANNER RULING on the S1 scoping stop'. Implement S1b: (1) the new
`HCGCompactness/CovOrderTail.lean` per ruling item 2 (constant-tracked tower variant + Ico-tail
corollary + initC lemma — NO edits to any existing HCGCompactness file); (2) thread `hell` into
`shiCovBound_of_soln` and discharge it from the pinned `movingShi_of_soln` citation (ruling item 3)
via the new tail corollary. Claim `ExtendShiInputs.lean` + the new file only. Acceptance:
`shiCovBound_of_soln` sorry-free; the extension lane's only remaining sorries = (N), (B),
`movingShi_of_soln`; targeted builds green; axiom check on `extendInputs_of_soln` traces to
`movingShi_of_soln` only. Report the constant's exact parameter list (what it depends on) verbatim.
Stop per CLAUDE.md."*

### BRICK S1 — KICKOFF PROMPT (SUPERSEDED by S1b above; kept for the record)

*"Read `DifferentialGeometry/Geometry/Flow/RicciFlow/ExtendShiInputs.md` — section 'SHI DISCHARGE
PLAN', Phase S1. Implement S1: read `MetricCovOrderEvolutionInput`'s fields and their HCG
producers, then discharge `shiCovBound_of_soln` from a new cited `movingShi_of_soln`
(`MovingShiBoundOn`, sorry) via `metricCovOrderWindow_of_evolution` at the single flow. Rules: claim
`ExtendShiInputs.lean` only; `HCGCompactness/**` is import-only; (N)/(B) sorries untouched;
acceptance = `shiCovBound_of_soln` sorry-free, file's only sorry = `movingShi_of_soln`, targeted
build green, axiom check on `extendInputs_of_soln` shows sorryAx via `movingShi_of_soln` only.
Report the window→tail constant analysis explicitly (S1 item 3). Stop per CLAUDE.md."*

## Y2 (unchanged plan)
Rewire `MaximalTime.extends_of_rmBounded`: Y1 → (A) → restart → (B) `ricci_flow_forward_unique` on
`[t*,ω)` → `hagree_overlap` → Brick U → `isSolutionOn_of_extendData` → `ExtendsPastEndpoint`; delete the
`hglue`/`hLimit` leaves; move the private MaximalTime solution-PDE helpers down into this file.

## BRICK Y2 — IN PROGRESS (2026-07-06): four ExtendShiInputs helpers GREEN + MaximalTime rewired

Four NEW sorry-free helpers added to `ExtendShiInputs.lean` (each verified green via focused check;
full targeted build of the module = exit 0):
- **`ric_quad_le_of_realizes`** — the `hric` crux, realization → ricci-trace → `ric_quad_le_of_rm04`.
  From `Rm04RealizesConnection g (metricCov g) Rm04sec` + `normSq0S ≤ C` ⟹ `|Ric(v,v)| ≤ (n²√C)·g(v,v)`.
  Discharges `htrace` from the realization: `rm13Section_realizes` + `rm04LowersRm13At_of_realizes` +
  `ricciFromRm13_comp_eq_rm04_trace` (orthonormal ⟹ `gInv = δ`, collapse) + `metricRicciAt =
  ricciFromRm13At (rm13Section…)` (`ricciCurvatureAt_eq_trace` + `rm13Section_apply`, both `rfl`).
  KEY: `hmr` closes by `rw [hRm13def, rm13Section_apply]; rfl` (default-transparency rfl through the
  `metricCov` abbrevs); the delta-collapse is `simp only [rm04CompAt_apply, ite_mul, one_mul, zero_mul,
  Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
- **`ric_quad_le_of_soln`** — packages the above over the solution: `∀ t ∈ Ico α ω, ∀ x v,
  |Ric(g_fam t)| ≤ ((finrank E)²√K')·g(v,v)` from the RAW per-time realization
  `∀ t ∈ Ico α ω, Rm04RealizesConnection (g_fam t) (metricCov (g_fam t)) (Rm04 t)` + the raw `|Rm|²`
  bound.  `finrank (TangentSpace I x) = finrank E` is `rfl`.  (Realization taken raw because
  `Rm04RealizesSolutionConnectionOn` is defined DOWNSTREAM in MaximalTime — the FlowTime +
  `leviCivita = metricCov` bridge happens at the MaximalTime call site.)
- **`chartGram_smooth_of_soln`** — `hsmooth_left`: interior joint C∞ chart-Gram on `Ioo α ω` from
  `_hS.smoothMetric.frameCompSmooth` fed the trivialization frame `e.localFrame (chartModelBasis E)`;
  `chartGramMatrix = inner(chartBasisVecFiber) = inner(localFrame)` via `localFrame_apply_of_mem_baseSet`
  (`basisAt = linearEquivAt.symm = e.symm`, all `rfl`).  Model `𝓘(ℝ) ≡ 𝓘(ℝ,ℝ)` for ℝ-valued (congr
  unified).  Metric defeq closed with `simp only [..., SolutionOn.family]`.
- **`chartGram_cont_of_soln`** — `hcont_left`: chart-Gram continuity up to closed endpoint on `Ico α ω`
  from `_hS.smoothMetric.metricTensor_cont.eval_continuous` on the (continuous) chart frame; mirrors
  `Evolution/Metric/Basic.lean:coordMetricContOn` (`metricTensorField_apply` + chart-frame `contMDiffAt`).

**MaximalTime.extends_of_rmBounded** rewired onto the interior-restart route (verification pending
full build): deleted 3 private helpers (`hasDerivWithinAt_Ici_boundary`, `tensor2_eval_contOn`,
`ricciFlowPDE_Ici_of_solution` — ported here) and the `hLimit`/`hglue`/`ricci_flow_extends_construction`
leaves.  New body: `hleft = ricciFlowPDE_Ici_of_soln` → bridge `_hbound`→raw + `_hRm`→raw realization
(`simpa [SolutionOn.family, SolutionFamily.connection, metricCov]`, mirroring `rm04Realizes_metric`) →
`ric_quad_le_of_soln` (`hric`) → `extendInputs_of_soln` (`⟨hell, hcov⟩`, `K := (finrank E)²√K'`) → (A)
`ricci_flow_interior_restart` → `chartGram_{smooth,cont}_of_soln` (`hsmooth/hcont_left`) → `hagree_overlap`
via (B) `ricci_flow_forward_unique` on `g_fam` vs `rr(·−t*)` (time-shift regularity via Brick U's
`hshift = (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd`; `h2pde` = `HasDerivWithinAt.comp`
chain rule; `h1pde` = `hleft.mono (Ici_subset_Ici)`; `h1smooth/h1cont` = `hsmooth/hcont_left.mono`) →
Brick U `extend_construction_of_restart` → Leaf 5 (unchanged).  MaximalTime imports ExtendShiInputs.
Three cited-input `sorry`s remain in the route: (N), (B), `shiCovBound_of_soln`.

## BRICK Y2 — DONE (2026-07-06), verified via real `lake build` (exit 0) + `#print axioms`

`MaximalTime.extends_of_rmBounded` is now on the interior-restart route, **zero sorry in its own body**
(the `hLimit`/`hglue`/`ricci_flow_extends_construction` leaves + the 3 private helpers are deleted;
`ricciFlowPDE_Ici_of_soln`, `hasDerivWithinAt_Ici_boundary`, `tensor2_eval_contOn` all live here now).
Needed `set_option maxHeartbeats 1000000 in` before the theorem (heavy `chartGramMatrix` defeq in the
`ContinuousOn.comp` time-shift; the default 200000 timed out at `isDefEq`).

**`#print axioms extends_of_rmBounded` (verbatim):**
`'…extends_of_rmBounded' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`

The 3 standard axioms + `sorryAx` only, and `sorryAx` traces to exactly the three cited black boxes
(N) `ricci_flow_unif_existence`, (B) `ricci_flow_forward_unique`, `shiCovBound_of_soln` — every other
declaration on the route (the 4 new ExtendShiInputs helpers included) is verified sorry-free.  **The
interior-restart extension route is now assembled end to end; the only remaining content is the three
cited black boxes.**

## 2026-07-14 moving-Shi discharge

`movingShi_of_soln` is now implemented by the checked, axiom-clean producer
`movingShiBoundSol`. Consequently the source bodies of `movingShi_of_soln`,
`shiCovBound_of_soln`, and `extendInputs_of_soln` contain no `sorry`.

The mathematical output is a single uniform constant `KShi` and an interior
time `tShi` such that every upper-truncated tail `[tShi, psi]` has the
order-three moving-metric Shi bound. The proof comes from the Ricci-flow tower
heat equation, joint regularity of intrinsic squared tower norms, a Bernstein
estimate after an interior time shift, and contraction from the Riemann tower
to the Ricci tower.

Focused verification of this downstream file is pending only because an active
Spectral rebuild has not yet produced one required upstream object file. The
producer itself has already passed focused and targeted verification and its
axiom closure has only the standard three axioms.

Strict accounting: the moving-Shi theorem and its dedicated machinery are
100%. The unconditional extension theorem remains 0% because the independent
uniform-existence `(N)` and forward-uniqueness `(B)` producers are still 0%.

## 2026-07-14 lower-layer relocation and all-order producer

`rm04_bound_can` was moved without an API change to
`HCGCompactness/MovingShiProducer.lean`, where it is consumed by both the
order-three moving-Shi theorem and the new arbitrary-order
`movingRmBoundSol`. `ExtendShiInputs.lean` continues to import and use the same
name; no downstream assumption was added.

The all-order corollary `bbsAllMBounds` is now proved in
`Evolution/BBSAllMBounds.lean`. This closes the Bernstein C1+C2 part of the
alternate endpoint-limit route, but does not affect the independent `(N)` and
`(B)` frontiers on the live interior-restart route.

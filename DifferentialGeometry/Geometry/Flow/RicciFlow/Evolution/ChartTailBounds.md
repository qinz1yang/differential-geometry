# ChartTailBounds — Brick W (`hC3` producer): scoping report + plan

## RESOLVED (2026-07-02, user chose "rethink the route"): **W is RETIRED.**

The scoping pass + a layering check obviate the bespoke chart-C³ producer:

- **The extension branch and HCGCompactness are independent.** `MaximalTime.lean` (home of
  `extends_of_rmBounded` and the future rewiring `Y`) imports only Evolution
  (`CinftyLimitGlue`/`BBSLimitProducer`/`ExtendedSolutionRegularity`); **no** HCGCompactness file
  imports `MaximalTime`/`ExtendViaUniqueness`/`CinftyLimitGlue`; and `AllTimesBounds`' closure is
  `HCGCompactness + low-Evolution(.Connection.Christoffel) + Analysis` — NOT the CinftyLimit/MaximalTime
  branch. So **`MaximalTime` (or a new file above both branches) can import HCGCompactness with no cycle.**
- **Lemma 3.11 already produces the tail derivative bounds.** `AllTimesBounds` concludes
  `MetricCovDerivOrderBoundOnWindow K β ψ gSeq gRef a C` (covariant ∇ᵃg window bounds) +
  `MetricUniformEquivalentOnWindow` (= Brick X's `hell`), from `MovingShiBoundOn` (Shi) inputs — the same
  inputs W would have taken. `MetricCovDerivOrderBoundOnWindow` = `∀ i t∈[β,ψ], MetricCovDerivOrderBoundOn
  K a (gSeq i t) gRef C`, **instantiable at a single flow** via `gSeq := fun _ t => g_fam t`. Producers
  ready: `metricCovOrderWindow_of_{pointwise,evolution,christoffel}`.
- **The hard W1 frontier is deleted from the critical path.** The chart `∂ₜΓ` time-integration (the
  binding ~1–2 session obstacle) is exactly what Lemma 3.11's BBS/Shi + integration machinery already
  does. W does not rebuild it.

**New plan (folds into `Y`, not a separate `Evolution/` file):**
1. Do the rewiring `Y` at the `MaximalTime` level (or a new file above both branches), importing
   HCGCompactness. Discharge (A)`ricci_flow_interior_restart`'s `hell` + tail-derivative hypotheses from
   Lemma 3.11 (`metricUniformEquivalentOnWindow_of_*` + `metricCovOrderWindow_of_*`) at
   `gSeq := fun _ t => g_fam t`.
2. The ONLY residual is a **static** covariant→chart adapter
   `MetricCovDerivOrderBoundOn K a g gRef C + MetricUniformEquivalentOn K gRef g B ⟹
   ‖iteratedFDeriv k (chartGramOnE g α i j) (extChartAt I α x)‖ ≤ Λ (x ∈ compact Q, k ≤ a)` — NO time
   integration; reuses the chart-Christoffel / chart metric-compat / public `jet2_chartGram_d1/d2`
   infrastructure (all importable). This is the `hC3` producer, but as a Y-level adapter over Lemma 3.11,
   not a bespoke Evolution brick.
3. Sub-decision for the Y session: keep (A) in Evolution with its current chart-`hC3` hypothesis and put
   the covariant→chart adapter at Y (recommended — leaves verified (A) untouched), vs. restate (A)'s
   hypothesis in covariant-window form (needs (A) to see the HCGCompactness predicate ⇒ (A) moves up).
   Note `chartLeviCivitaGoodSet` non-compactness still forces the compact-`Q` shape (the (A) patch).

Everything below is the original scoping detail (still valid as the inventory for the Y-level adapter).

---


Target: produce, for a curvature-controlled Ricci flow, the `hC3` hypothesis consumed by
`ricci_flow_interior_restart` (ExtendViaUniqueness.lean) — for every finite centre family `S`, a tail
`[t₂, ω)` on which `‖iteratedFDeriv ℝ k (chartGramOnE (g_fam s) α₀ i j) (extChartAt I α₀ x)‖ ≤ Λ`
for `k ≤ 3`, `α₀ ∈ S`, `x ∈ chartLeviCivitaGoodSet α₀`.

Status after the scoping pass (2026-07-02): **W1 is NOT completable sorry-free this session.** The
integration engine it needs already exists but is trapped in an off-limits/downstream lane, and the
heart (chart `∂ₜΓ` bound) is a genuine chart-calculus frontier. Details + plan below. No `.lean`
written yet (a bare statement-with-`sorry` would be a gratuitous new frontier `Y` does not yet
consume).

## Scoping inventory (exact names / files)

### Importable (Geometry / Analysis / Evolution — usable from a new `Evolution/` file)
- `chartGramOnE g α i j : E → ℝ` — `Geometry/Operator/Hessian.lean:211`; `chartGramOnE_def`,
  `chartGramOnE_symm`; `chartGramOnE_contDiffOn` (`HessianTrace.lean:940`, C∞ on chart target);
  `chartGramOnE_differentiableAt_interior`.
- `chartChristoffel g α i j k y = ½ Σ_l G^{kl}(∂_iG_{lj}+∂_jG_{li}−∂_lG_{ij})` — `Hessian.lean:237`.
- **chart** metric-compatibility `∂_k G_{ij} = Σ_l Γ^l_{ki}G_{lj} + Σ_l Γ^l_{kj}G_{li}` —
  `Geometry/Connection/MetricCompatibility/ChartGramChristoffel.lean` (the m=1 conversion).
- PUBLIC jet↔partialDeriv bridges `jet2_chartGram_d1/d2`, `chartChristoffel_eq_jet`,
  `chartChristoffelDeriv_eq_jet`, and `partialDeriv_chartChristoffel_eq`, `partialDeriv_chartInvGramOnE_eq`
  — `Evolution/ChartRicciJetIdentity.lean` (an Evolution file). This reconstructs the
  `iteratedFDeriv↔partialDeriv` bridge from public API.
- fixed-metric compact bounds: `chartGramMatrix_entry_isBounded_on_compact`
  (`Analysis/.../UniformChartBounds/ChartGramUniformContinuity.lean:151`),
  `chartInvGramMatrix_l1Sum_isBounded_on_compact` (:194) / `_on_pouTsupport` (:215, closed-`M`).
- chart-Christoffel Lipschitz-in-jet: `exists_chartChristoffel_lipschitz_on_compact`
  (`ChristoffelPerturbation.lean:384`); per-order difference bounds
  `partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup` / `partialDeriv2_..._sub_abs_le_partial2DiffSup`.
- chart-Gram entry TIME-derivative (chart PDE): `Analysis/Integration/Measure/Family*.lean`
  (`hasDerivAt_chartGramMatrix_entry`-family) — importable Analysis layer.
- `∂ₜΓ` in FRAME form: `christoffelEvolutionRHSInFrame` (`Evolution/Connection/Components.lean:71`,
  `= Σ g^{kl}(−∇_iRic_{jl}−∇_jRic_{il}+∇_lRic_{ij})`); predicate
  `ChristoffelEvolutionEquationInFrameOn` (`Evolution/Connection/Christoffel.lean:141`).

### Trapped (off-limits `HCGCompactness/` — importing inverts the layer + couples a coworker lane)
- time-integration engine in `HCGCompactness/AllTimesBounds.lean` (imports `Evolution.Connection.Christoffel`,
  so it is ABOVE Evolution): `norm_le_initial_add_deriv_bound` (:182), `norm_le_initial_add_derivWithin_bound`
  (:212), `affineGronwall_of_abs_deriv_le` (:114), `exp_bounds_of_log_deriv_bound` (:76),
  `componentL2_le_initial_add(_within/_on_subset)` (:341–425), **`gammaL2_le_initial_add` family (:434–522)
  — Christoffel integration with `dΓ = −∇Ric−∇Ric+∇Ric`**, `gammaL2_le_of_christoffel` (:884).
- Shi predicate `MovingShiBoundOn` + `ricCovTower` (= `iterCov gRef 2 ricciSection s`) —
  `HCGCompactness/RicBound.lean:117/141`. (W takes `hShi3` AS A HYPOTHESIS, so it may be stated in any
  importable intrinsic form — this one is only a naming reference.)
- private + off-limits `iteratedFDeriv↔partialDeriv` bridges — `ShortTimeFlow/DeTurckVFSmoothness.lean:1086/1094`
  (superseded by the public `ChartRicciJetIdentity` route above).

### Genuinely absent
- `‖iteratedFDeriv k (chartGramOnE g α i j)‖ ≤ Λ` for `k ≤ 3` (the exact `hC3` target) — no standalone lemma.
- **frame→chart bridge for `∂ₜΓ`**, i.e. `∂ₜ(chartChristoffel g_t α i j k y) = (chart components of the
  tensor `−g^{kl}(∇Ric+∇Ric−∇Ric)`)`, and its NORM bound. THIS IS THE HEART/FRONTIER.
- intrinsic→chart bridge turning `hShi3` (`‖∇Ric‖_g ≤ C₁`, intrinsic) into the chart-component bound that
  enters the `∂ₜΓ` estimate.

## The blocker (why W1 is not a one-session sorry-free build)

`hC3` needs `k ≤ 3` bounds. The k=1 heart's route (brief's own): `‖∂ₜΓ(s)‖ ≤ c‖∇Ric(s)‖ ≤ cC₁`
→ integrate from a fixed `s₀` → `‖Γ(s)‖` bounded → `∂(chartGram)` bounded via chart metric-compat.
Two of the three ingredients are blocked/absent:
1. the integration step (`gammaL2_*` / `norm_le_initial_add_derivWithin_bound`) is **pure analysis but
   trapped in off-limits/downstream `HCGCompactness/AllTimesBounds.lean`**;
2. the `‖∂ₜΓ(chart)‖ ≤ cC₁` step needs the **absent frame→chart `∂ₜΓ` bridge + intrinsic→chart ∇Ric
   bridge** — genuine chart calculus (time-differentiate `chartChristoffel = ½g⁻¹(∂g+∂g−∂g)` using the
   chart PDE `∂ₜ chartGram = −2 Ric-in-chart` and the inverse time-derivative), ~1–2 sessions.
Only the chart metric-compat step (3) is cleanly importable.

## Architectural finding / design choice (for the user)

W1's engine is **already implemented once**, in the MSM135 Lemma 3.11 track
(`HCGCompactness/AllTimesBounds.lean`: `gammaL2_*`, `componentL2_*`, the Grönwall/integration family).
Those lemmas are PURE SCALAR/VECTOR ANALYSIS — mis-placed above Evolution. Re-deriving them inside
`Evolution/ChartTailBounds.lean` duplicates ~200 lines of a coworker's lane; importing them inverts the
layer. The Mathlib-correct fix ("canonical home, lowest suitable module") is to **factor the
pure-analysis integration lemmas down into a low shared `Analysis/` module**, leaving compat wrappers in
`AllTimesBounds.lean`, so BOTH the Lemma 3.11 track and the extension route consume the shared layer.
That refactor edits `AllTimesBounds.lean` (off-limits, another planner's lane) → it needs the user's
authorization / coordination. Options:
- **(A, recommended)** authorize the factor-down (touch `AllTimesBounds.lean`): move
  `norm_le_initial_add_*`, `affineGronwall_*`, `exp_bounds_*`, `componentL2_*`, `gammaL2_*` to a new low
  `Analysis/ODE/` (or `Analysis/Calculus/`) module; both lanes import it. Then W1 = the chart-`∂ₜΓ`
  calculus + assembly (still ~1–2 sessions, but no duplication).
- **(B)** no coordination: locally re-port the ~5 pure-analysis integration lemmas into
  `Evolution/ChartTailBounds.lean` (precedent: `expBounds_of_logDiff` in ExtendViaUniqueness), accept
  the duplication, build the chart-`∂ₜΓ` frontier there.
- **(C)** reconsider the route: have `Y` consume the Lemma 3.11 output directly instead of a bespoke
  `hC3` producer — a larger question about how the extension route relates to the MSM135 track.

The chart-`∂ₜΓ` heart (bullet 2 above) is a genuine frontier independent of A/B/C.

## W1 / W2 / W3 decomposition (once the engine question is resolved)

- **W1a (m=0, importable, ~60–80 lines, sorry-free NOW):** from `hell` (Λ-equivalence, Brick X output)
  + `chartGramMatrix_entry_isBounded_on_compact` (fixed `g_fam α`), bound `|chartGramOnE (g_fam s) α i j|`
  on a compact `Q ⊆ chartLeviCivitaGoodSet α` — via coordinate-basis evaluation + Cauchy–Schwarz in the
  `g_s` inner product. NOTE: `chartLeviCivitaGoodSet` is OPEN, closure NOT compact — must bound on a
  compact `Q` (use `tsupport (chartAtlasPOU I M α)`), so `hC3`'s statement shape needs the compact-`Q`
  refactor + the matching (A) patch (the brief flags this as acceptable).
- **W1b (m=1 heart, the frontier):** chart `∂ₜΓ` bound (frame→chart or chart-direct) + intrinsic→chart
  ∇Ric bridge + integration (engine from A/B) + chart metric-compat `∂g = Γg+gΓ` → `‖iteratedFDeriv 1
  (chartGram)‖` bound. `iteratedFDeriv 1 ↔ partialDeriv` via public `jet2_chartGram_d1`.
- **W2 (m=2):** `∂²g` via Leibniz on `∂(g·Γ)`; needs `∂Γ(s)` bound = integrate `∂ₜ∂Γ = ∂(tensorial RHS)`
  with conversion errors controlled by W1b. `iteratedFDeriv 2 ↔ partialDeriv²` via `jet2_chartGram_d2`
  (needs chart-target interior; goodSet interior condition).
- **W3 (m=3):** iterate once more. Same pattern, one more integration + Leibniz order.
- Assembly: `∀ k ≤ 3` by `interval_cases k`/`Finset` over the four bounds; take `Λ = max` of the four.

## Traps recorded
- `iteratedFDeriv` (hC3 form) vs `partialDeriv` (identity form): use public `jet2_chartGram_d1/d2`
  (Evolution/ChartRicciJetIdentity), NOT the private ShortTime bridges.
- `chartLeviCivitaGoodSet` non-compact ⇒ bound on compact `Q`; entails a `hC3` statement-shape change.
- one-sided PDE (`HasDerivWithinAt … (Ici α)`): integrate with a within-MVT (mirror Brick X), not the
  two-sided `norm_le_initial_add_deriv_bound`; use the within-form `norm_le_initial_add_derivWithin_bound`
  analog.

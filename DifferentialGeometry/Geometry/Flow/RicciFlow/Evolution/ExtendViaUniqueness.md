# ExtendViaUniqueness — interior-restart + uniqueness route for `extends_of_rmBounded`

## Why this route (user's insight, 2026-06-20)

The current route restarts short-time existence **at ω** from the BBS limit `g(ω)`, which forces
the C∞-glue *across* the seam ω → Gate-R (DeTurck C∞-**up-to-the-initial-time**, blocked: the PDE
black box `deturck_ricci_flow_parabolic_short_time_existence` caps endpoint regularity at C² / `k≤2`)
+ Gate-L + the jet-matching (corollary a + Lemma 3 + splice).

**Better route:** restart from an *interior* time `t* < ω` (where `g_fam` is genuinely C∞), get a
flow `r̃` whose existence interval `[0, T̃)` reaches past `ω` (i.e. `ω < t* + T̃`). Then `ω` is an
**interior** time of `r̃(·−t*)`, so C∞-at-ω is FREE (interior regularity, which the black box DOES
give). Forward uniqueness patches `r̃(·−t*) = g_fam` on the overlap `[t*, ω)`, so the seam dissolves.

## Construction (provable; reuses the `gluedFamily` machinery)

`g_ext := gluedFamily g_fam (fun u => r̃ (u + (ω − t*))) ω` `= fun s => if s < ω then g_fam s else r̃ (s − t*)`.
Key fact `hext_eq_r`: for `s ≥ t*`, `g_ext s = r̃ (s − t*)` (uniqueness below ω + def above) — so
`g_ext = r̃(·−t*)` on `[t*, ω+ε)`, with `ω−t* ∈ (0, T̃)` interior to `r̃`.

Output tuple = same as `ricci_flow_extends_construction` (ε, g_ext, agree, Ioo-C∞, Ico-C⁰, PDE), then
fed to the banked `isSolutionOn_of_extendData`. ε := t* + T̃ − ω > 0.
- **agree** below ω: `gluedFamily_eq_left`. ✓ reuse.
- **PDE** on `Ico α (ω+ε)`: `gluedFamily_pde` + `gluedFamily_pde_cross_of_matching`. ✓ reuse, with
  `metric_match` (`g_fam s → r 0`) and `ricci_match` derived from **uniqueness + r̃ continuity** (NOT
  from BBS): `g_fam s = r̃(s−t*) → r̃(ω−t*) = r 0`. `r`'s PDE on `Ico 0 ε` = `r̃`'s PDE shifted.
- **gram_smooth** (Ioo α (ω+ε)) + **gram_cont** (Ico): NEW. `Ioo α (ω+ε) = Ioo α ω ∪ Ioo t* (ω+ε)`;
  on `Ioo α ω` use `g_fam` interior C∞ (from `_hS.smoothMetric`); on `Ioo t* (ω+ε)` use `hext_eq_r`
  + `r̃` interior C∞ shifted (`ContMDiffOn.comp` with `(s,x)↦(s−t*,x)`); `ContMDiffOn.union` (both
  open). Similarly C⁰ via `ContinuousOn`.

## Historical planning snapshot (2026-07-02; superseded below)

- **(A) `ricci_flow_interior_restart`**: bounded-curvature solution on `[α,ω)` ⇒ `∃ t* ∈ [α,ω), T̃`,
  `ω < t*+T̃`, and a restart `r̃` from `g_fam t*` (interior C∞ on `Ioo 0 T̃`, C⁰ `Ico`, PDE `Ico`).
  Needs a **uniform/stable existence time** (existence time from `g(t*)` doesn't collapse as `t*→ω`):
  cleanest via `g(t*) → g(ω)` C∞ (BBS) + lower-semicontinuity of the short-time existence time, OR a
  quantitative-in-curvature short-time existence. **This was the missing state
  at the snapshot; (A) is now proved from (N), so it is no longer an independent
  frontier.**
- **(B) `ricci_flow_forward_unique`**: two flows with the same PDE + interior C∞ + C⁰ + equal initial
  value agree forward. Standard (DeTurck), **not in the project**. ← the main new ingredient / block.

## VERIFIED against GSM77 (Fable, 2026-07-02): which black boxes are faithful

User asked to double-check truth before citing. Checked against the local GSM77 LaTeX
(`RicciFlow/RicciFlowBooksLatex/GSM77/tex/chapters/`):

1. **(B) forward uniqueness on closed M — TRUE, but the advertised GSM route needs an edge
   theorem.** GSM77 Ch. 7 §5.2 uses the Ricci–DeTurck energy class with C⁰-comparability and
   `|∇̃g| + √t|∇̃²g| ≤ A`, followed by harmonic-map-flow conversion.  Interior joint C∞ plus
   chart-Gram C⁰ at the initial time does not by itself make those derivative bounds automatic.
   The exact Lean statement is still expected true (it is the identity-gauge regularizing-flow
   class), but this route first needs a theorem deriving the displayed edge bounds from its exact
   hypotheses, or a direct uniqueness theorem for regularizing Ricci flows.  Merely adding the
   already-present `Ioo`-C∞ and `Ico`-C⁰ fields did not finish that bridge.

2. **"Flow exists ≥ c(n)/K when |Rm(g₀)| ≤ K" — TRUE mathematics, but CIRCULAR here; DO NOT cite.**
   GSM77 Ch. 6: the doubling-time estimate (`lem doubling time`: |Rm| ≤ 2K for t ≤ 1/(16K)) is an
   a-priori bound ON AN EXISTING solution; converting it into an existence-time lower bound is
   exactly Theorem `LTE` (closed M, maximal T < ∞ ⟹ max|Rm| → ∞) — and `LTE` IS
   `extends_of_rmBounded` (contrapositive). Citing c/K-existence to prove extends_of_rmBounded
   axiomatizes the theorem being proved. Lean-consistent, scholarship-void.

3. **The faithful non-circular (A)-source: neighborhood-uniform short-time existence
   (continuous dependence).** For every smooth ḡ there are `τ₀ > 0`, `δ > 0`, `k` (k = 3 safe) such
   that every smooth `g₀` whose chart-Gram k-jets are δ-close to ḡ's (finite-atlas sup) flows for
   time ≥ τ₀ with the standard fields (interior C∞, C⁰-up-to-0, PDE). TRUE and standard: the DeTurck
   fixed-point existence time is uniform over data in a bounded C^{2,α}/C³-neighborhood (ellipticity
   + coefficient + data bounds all uniform); no blow-up criterion inside. Same lane/flavor as the
   existing `deturck_ricci_flow_parabolic_short_time_existence` black box.

**Consequence for the route:** with (3), obligation (A) needs `g(t*) → g(ω)` uniformly in C^k for
FINITE k (~3) — so the finite-k BBS limit packaging (limit metric + uniform C³ convergence from
bounded |∇ᵏRm|, k ≤ 3) RETURNS to the critical path (only the all-k/C∞ form is obviated). Chain:
finite-k BBS bounds [Bernstein machinery mostly banked] → uniform C³ limit g(ω) [analysis frontier,
BBSLimitProducer-style but finite-k] → (3) gives uniform τ₀ near ω → pick t*, restart → (B) →
`extend_construction_of_restart` [DONE] → `isSolutionOn_of_extendData` [DONE].

## Historical statement draft and approved route (2026-07-02) — brick board

User approved the faithful black boxes after the §VERIFIED audit. Drafted, typechecked, and banked
(build green, 9367 jobs; the file's 3 sorries are exactly these):

- **(N) `ricci_flow_unif_existence` (live line 74) — analytic producer, still sorry**
  (`∀ Λ ≥ 1, ∃ τ₀ > 0` uniform over `Λ`-elliptic data with intrinsic
  `MetricCovDerivOrderBoundOn` hypotheses through order three).  The earlier
  centre-family `S` wording is not part of the live statement.
- **(A) `ricci_flow_interior_restart` (live line 103) — DONE from (N)**;
  hypotheses = the two tail producers `hell` (ellipticity) + `hC3` (chart-C³ on any finite family).
- **(B) `ricci_flow_forward_unique` (live line 175) — analytic producer, still sorry.** Its chart-Gram
  `Ioo`-C∞ + `Ico`-C⁰ hypotheses describe the intended regularizing-flow class, but a
  boundary derivative estimate is still required before applying the GSM energy theorem.
- `extend_construction_of_restart` (live line 210) — **Brick U, DONE sorry-free** (accepted).

### Brick board (dependency order)

| Brick | What | Status |
|---|---|---|
| U | consumer assembly (restart+overlap ⟹ extension tuple) | ✅ DONE, accepted |
| V | prove (A) from (N): Λ-max + t\*-choice + box application | ✅ DONE (2026-07-02), (A)'s sorry removed |
| X | `hell` producer: `\|Ric\| ≤ K·g` ⟹ metric equivalence `exp(±2K(ω−α))` vs `g_α` on a tail | ✅ DONE (2026-07-02), sorry-free |
| ~~W~~ | ~~bespoke chart-C³ `hC3` producer~~ | **RETIRED 2026-07-02** (scoping: obviated by Lemma 3.11 — see `ChartTailBounds.md`; the chart-∂ₜΓ time-integration frontier is deleted from the critical path) |
| Y | rewiring `extends_of_rmBounded` at `MaximalTime` level (imports HCGCompactness, no cycle): `hell` + tail-cov-bounds discharged from **Lemma 3.11** (`metricUniformEquivalentOnWindow_of_*` + `metricCovOrderWindow_of_*` at `gSeq:=fun _ t=>g_fam t`) → static covariant→chart adapter for (A)'s `hC3` → (A) → (B) on `[t*,ω)` → `hagree_overlap` → Brick U → `isSolutionOn_of_extendData`; retire old `hglue`/Gate-R path | ✅ DONE; its remaining `sorryAx` is transitive through (N) and (B) |

### BRICK V+X — DONE (2026-07-02)

Both landed in `ExtendViaUniqueness.lean`; full targeted build green (9367 jobs).

- **V `ricci_flow_interior_restart`** (sorry removed): straight assembly of (N) `ricci_flow_unif_existence`.
  `S` from the box at `gBase := g_fam α`; `Λ := max Λ₁ Λ₂` dominating both producers (weaken each bound
  to `Λ`: upper by `mul_le_mul_of_nonneg_right` with `0 ≤ g_α(v,v)`; lower via the same after `gcongr`
  handles `Λ⁻¹ ≤ Λ₁⁻¹`); `t_star := max (max t₁ t₂) (ω − τ₀/2)` gives `t_star ∈ [α,ω)` and `ω < t_star+τ₀`;
  apply the box at `g_fam t_star`, output fields ARE the conclusion (`TT := τ₀`). `#print axioms` shows
  `sorryAx` **only via (N)** (never (B)) — the intended acceptance state. Metric-positivity API used:
  `g.pos x v hv : 0 < g.inner x v v` (`v ≠ 0`), `(g.inner x).map_zero` for `v = 0`.
- **X `metricEquiv_of_ricBound`** (sorry-free): the `hell` producer. `Λ = exp(2K(ω−α))`, `t₁ = α`.
  `v = 0` trivial; `v ≠ 0`: `f t = g_t(v,v) > 0`, within-`[α,s]` MVT
  (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) on `log f` — the one-sided `hpde`
  (`HasDerivWithinAt … (Ici α)`) is restricted to `Icc α s` by `.mono` then `.log`; the `2K` bound is
  `|(-2)Ric|/f ≤ 2K` from `|Ric| ≤ K f`; exponentiate the log-difference bound
  (`|log f(s) − log f(α)| ≤ 2K(s−α) ≤ 2K(ω−α)`) and weaken `exp(±2K(s−α))` to `Λ^{±1}` using `f_α ≥ 0`.
  Needed a **local private port** `expBounds_of_logDiff` (log-diff ⟹ exp-bounds): the identical
  `exp_bounds_of_abs_log_sub_le` / `exp_bounds_of_log_deriv_bound` engine lives in
  `HCGCompactness/AllTimesBounds.lean`, which is off-limits AND downstream (imports
  `Evolution.Connection.Christoffel`), so it cannot be imported here; and its
  `exp_bounds_of_log_deriv_bound` wants two-sided `HasDerivAt`, incompatible with our one-sided PDE. If
  that scalar engine is ever moved to a low Analysis layer, X should drop the private port and reuse it.

**Remaining to finish the route:** W (`hC3` producer, the meaty chart-C³ bootstrap) then Y (rewiring
`extends_of_rmBounded`). (N) and (B) stay as cited black boxes (sorry).

### BRICK V+X — KICKOFF PROMPT (for the record; both DONE above)

**Paste-pointer:** *"Work in `E:\testdifferential-geometry`. Read `CLAUDE.md`, `important_lesson.md`,
then `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.md` section
'BRICK V+X' — implement Brick V, then Brick X if the session has room. Report back. Do not touch
any file marked off-limits."*

**Brick V (prove `ricci_flow_interior_restart` at ExtendViaUniqueness.lean:96 — remove its `sorry`):**
1. `obtain ⟨S, hbox⟩ := ricci_flow_unif_existence (I := I) (g_fam α)`.
2. `obtain ⟨Λ₁, hΛ₁, t₁, ht₁, hell'⟩ := hell`; `obtain ⟨Λ₂, hΛ₂, t₂, ht₂, hC3'⟩ := hC3 S`.
3. `Λ := max Λ₁ Λ₂` (`1 ≤ Λ` ✓); `obtain ⟨τ₀, hτ₀, hexist⟩ := hbox Λ (le_max_left … |>.trans` — just `le_trans hΛ₁ (le_max_left _ _)`).
4. `t_star := max (max t₁ t₂) (omega - τ₀/2)`. Facts by `constructor`/`linarith`: `t_star ∈ Ico α omega`
   (each of `t₁ t₂ ∈ Ico α omega`, `omega - τ₀/2 < omega`, and `α ≤ t₁ ≤ t_star`);
   `omega < t_star + τ₀` (from `t_star ≥ omega − τ₀/2`, `τ₀ > 0`).
5. Apply `hexist (g_fam t_star)`:
   - ellipticity: from `hell' t_star ⟨le_trans (le_max_left …) …, …⟩`, weaken `Λ₁ → Λ`: needs
     `Λ⁻¹ * B ≤ Λ₁⁻¹ * B` and `Λ₁ * B' ≤ Λ * B'` where `B = (g_fam α).inner x v v ≥ 0` and
     `B' = (g_fam t_star).inner x v v ≥ 0`. Nonnegativity of `inner v v`: grep the
     `SmoothRiemannianMetric` API (`inner_self_nonneg`/posdef field — it exists; if the field is
     strict posdef `v ≠ 0`, handle `v = 0` by `simp` since both sides are `0`).
     Then `mul_le_mul_of_nonneg_right` + `inv_le_inv_of_le` (`0 < Λ₁`).
   - C³ bound: `hC3' t_star … α₀ hα₀ i j k hk x hx` then `le_trans … (le_max_right _ _)`.
6. `TT := τ₀`; conclusion fields are verbatim the box's output. `exact ⟨…⟩`.
Size ~80–120 lines, no new imports. TRAPS: the `Ico` memberships want `linarith` with all bounds
named; the Λ-monotone step needs the right `mul_le_mul` lemma variants (`div`-free formulation
already chosen); DO NOT touch (N)/(B)'s `sorry`s.

**Brick X (state + prove the `hell` producer — new theorem in ExtendViaUniqueness.lean):**
Target shape (align to (A)'s `hell` hypothesis, for `g_fam := S.base.metric` abstractly):
`theorem metricEquiv_of_ricBound (g_fam) {α omega} (hαω) (K) (hK : 0 ≤ K)`
`(hpde : PDE on Ico α omega within Ici α)` `(hric : ∀ t ∈ Ico α omega, ∀ x v, |ricciTensor (g_fam t) x v v| ≤ K * (g_fam t).inner x v v)` `:` the `hell` shape with
`Λ := Real.exp (2*K*(omega−α))`, `t₁ := α`. Route: fix `(x, v)`; `f t := (g_fam t).inner x v v`;
`hpde` gives `HasDerivWithinAt f (−2·Ric_t(v,v)) (Ici α) t` with `|f'| ≤ 2K·f`; Gronwall both sides
(`Mathlib`: `norm_le_gronwallBound_of_norm_deriv_right_le` / `gronwallBound` family — search also
the project's Stage-1 uses in `CinftyLimitGlue.lean` and `AllTimesBounds`-related files for an
existing metric-equivalence engine FIRST; if one exists, write a thin adapter instead). NOTE the
hypothesis `hric` is stated as an INPUT here (its own producer from `Rm04NormSqBoundedAt` + the
pointwise `|Ric| ≤ c|Rm|` algebra is part of Brick Y/W wiring, NOT this brick).
If the Gronwall shape fights, deliver V alone and report the exact blocker.

**Rules:** claim `Evolution/ExtendViaUniqueness.lean` via lake-locked; off-limits: `MaximalTime.lean`,
`CinftyLimitGlue.lean` (read-only), `HCGCompactness/**`, `ShortTime*/`, `DeTurck*`, frozen
`JetGlueParam.lean`. Verify: focused check + targeted build
`+DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendViaUniqueness`; GREEN = only the
(N)/(B) sorries remain after V ((A)'s sorry gone), plus X's theorem sorry-free if delivered.
Expect transient `failed to create thread` crashes under concurrent agent builds — see
`important_lesson.md`/memory (retry when lake lock frees, `-LeanThreads 3`). Record outcome in this
`.md`; `#print axioms` on the proved theorems must show no `sorryAx` beyond (N) for V (V cites (N) —
so V's axiom print WILL show `sorryAx` via (N); the acceptance criterion for V is instead: removing
(A)'s own `sorry`, build green, and V's proof term referencing ONLY (N) among the sorried trio).

### PLANNER ACCEPTANCE — ✅ V + X ACCEPTED (Fable, 2026-07-03)
Verified: (A)'s sorry gone (file sorries = exactly :85 (N), :201 (B)); V's proof region cites
`ricci_flow_unif_existence` and never `ricci_flow_forward_unique` (matches the executor's axiom
report: sorryAx only via (N)); X `metricEquiv_of_ricBound` (:419) sorry-free with the documented
private scalar port `expBounds_of_logDiff` (:392 — acceptable: the AllTimesBounds engine is
downstream/off-limits and two-sided; relocation chip filed); diff confined to the two brick files.
**Board: U ✅ V ✅ X ✅ → W (next) → Y.**

### BRICK W — KICKOFF PROMPT for the next Opus 4.8 executor session (scope + W1)

**Paste-pointer:** *"Work in `E:\testdifferential-geometry`. Read `CLAUDE.md`, `important_lesson.md`,
then `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.md` section
'BRICK W' — do the scoping pass, then implement W1. Report back. Do not touch off-limits files."*

**Context.** (A) `ricci_flow_interior_restart` (proved) consumes `hC3`: for every finite centre
family `S`, a tail `[t₂, ω)` on which the chart-Gram spatial jets of order `≤ 3` are uniformly
bounded (`‖iteratedFDeriv ℝ k (chartGramOnE (g_fam s) α₀ i j) (extChartAt I α₀ x)‖ ≤ Λ` on
`chartLeviCivitaGoodSet α₀`, `α₀ ∈ S`, `k ≤ 3`). Brick W produces `hC3` for a real solution. Inputs
you may TAKE AS HYPOTHESES (do not prove): `hShi3` — Shi-type covariant bounds
`∀ k ≤ 3, ‖(∇ᵏRm)(s)‖_{g s} ≤ Cₖ` on a tail (precedent: Lemma 3.11's `hShi`; project vocabulary:
the `totalNabla0S`/iterated-∇ curvature norms — match whatever shape the BBS layer exposes, record
the choice); `hell` — the Brick X output shape (Λ-equivalence to `g_fam α` on a tail); the PDE and
`IsSolutionOn`-style regularity as needed.

**Mathematical route (Chow–Knopf pp. 223–224 / GSM77 Ch. 6 §7 shape), induction on jet order m:**
- **m = 0**: `hell` + the FIXED metric `g_fam α`'s chart-Gram bounds on the finitely many `S`-charts
  (each `goodSet`-region; continuity of a fixed smooth metric — but note `goodSet` need not have
  compact closure: INTERSECT with the compact sets the consumer actually needs, or bound on
  arbitrary compact `Q ⊆ goodSet` and refactor `hC3`'s statement accordingly if necessary — a
  statement-shape adjustment here is ACCEPTABLE if (A)'s proof is patched in the same session).
- **W1 heart (m = 1)**: the Christoffel evolution `∂ₜΓ^k_{ij} = −g^{kl}(∇ᵢRic_{jl} + ∇ⱼRic_{il}
  − ∇_lRic_{ij})` is TENSORIAL ⟹ `‖∂ₜΓ(s)‖ ≤ c·‖∇Ric(s)‖ ≤ c·C₁` on the tail ⟹ integrating from a
  fixed `s₀` bounds the chart Christoffels on the tail ⟹ `∂(chartGram)` bounded via the chart
  metric-compatibility `∂_l g_{ij} = g_{pj}Γ^p_{li} + g_{ip}Γ^p_{lj}`. SCOPE FIRST (½ session):
  grep for existing (i) a chart-Christoffel TIME-evolution identity
  (`christoffel.*[Ee]vol|deriv.*[Cc]hristoffel|partial.*t.*Christoffel` — check
  `ChristoffelPerturbation.lean`, the DeTurck linearization layers, `Evolution/`), (ii) chart
  metric-compatibility (`partialDeriv.*chartGram` in `Hessian.lean`/`HessianTrace.lean`), (iii)
  covariant↔chart conversion bounds and `iteratedFDeriv`-vs-`partialDeriv` norm bridges
  (`UniformChartBounds/`, `ChartGramUniformContinuity.lean`). Report what exists BEFORE building.
- **m = 2, 3 (W2/W3, later bricks)**: iterate — `∂^m g` via Leibniz expansions of `∂^{m−1}(g·Γ)`;
  `∂ₜ∂^{m−1}Γ = ∂^{m−1}(tensorial RHS)` integrates with conversion errors controlled by lower
  orders. Do NOT attempt in the W1 session; deliver the W2/W3 decomposition plan instead.

**Deliverables:** (1) scoping report (which identities exist, exact names/lines, what is missing);
(2) W1 = the `k ≤ 1` producer theorem, sorry-free, in a NEW file `Evolution/ChartTailBounds.lean`
(same-name `.md` note; keep `ExtendViaUniqueness.lean` unchanged except — only if you adjusted
`hC3`'s statement shape — the matching (A) patch); (3) updated brick plan for W2/W3.
**Traps:** `iteratedFDeriv` (the `hC3` form) vs `partialDeriv` (the identities' form) — you need the
finite-dimensional norm bridge, grep before hand-rolling; `goodSet` non-compactness (see m = 0);
time-integration must use the one-sided PDE (`HasDerivWithinAt … (Ici α)`) — mirror Brick X's
within-MVT pattern rather than two-sided engines. **Rules:** claim the new file (+
`ExtendViaUniqueness.lean` only if patching (A)); same off-limits list as V+X; targeted build;
expect `failed to create thread` flakes (retry, `-LeanThreads 3`). Stop per CLAUDE.md (3 failed
routes ⟹ report exact blocker).

### PLANNER ACCEPTANCE — ✅ W-SCOPING ACCEPTED, W RETIRED (Fable, 2026-07-03)
Independently verified the load-bearing claims: (i) NO HCGCompactness file imports
MaximalTime/ExtendViaUniqueness/CinftyLimitGlue (reverse edge empty ⟹ MaximalTime → HCGCompactness
is cycle-free); (ii) `AllTimesBounds.lean` imports `HCGCompactness.BoundedGeometry` (+ low
Evolution) — it sits above Evolution, confirming the trap; (iii) the predicates/producers exist:
`MetricUniformEquivalentOnWindow` (AllTimesBounds:612), `MetricCovDerivOrderBoundOnWindow` (:773),
`metricCovOrderWindow_of_pointwise` (:793) / `_of_evolution` (:4403), `MovingShiBoundOn`
(RicBound:141); (iv) analysis-only session, no premature `.lean`, notes in `ChartTailBounds.md`.
**Ratified: W retired; the chart-`∂ₜΓ` frontier is deleted; the residual static covariant→chart
adapter folds into Y. Sub-decision ratified: (A) stays chart-shaped and untouched; the adapter
lives at the Y level.**

**Planner design decision for Y (signature question):** `extends_of_rmBounded`'s PUBLIC SIGNATURE
STAYS UNCHANGED (hypotheses: `hdim`, `_hS`, `_hRm`, `_hbound` only — the textbook Thm 14.1 shape).
The Shi-type input enters as a clearly-labelled CITED PRODUCER
(`movingShi_of_rmBounded … : MovingShiBoundOn …`, `sorry`, docstring citing Shi — GSM77 Ch. 7 — and
the banked Bernstein tower as the eventual discharge). This matches the established
hShi-as-cited-input pattern (Lemma 3.11), and the old deferred content it replaces (the `hglue`
sorry + `cinftyLimitData_of_solution`'s internal `bbsAllMBounds` sorry) leaves the critical path —
the net honest sorry ledger improves.

### BRICK Y — KICKOFF PROMPT for the next Opus 4.8 executor session (Y1, then Y2 if room)

**Paste-pointer:** *"Work in `E:\testdifferential-geometry`. Read `CLAUDE.md`, `important_lesson.md`,
then `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.md` section
'BRICK Y' — implement Y1, then Y2 if the session has room. Report back. Do not touch off-limits
files."*

**Context.** All plumbing is proved: (A) `ricci_flow_interior_restart` (chart-`hC3` + `hell`
hypotheses), Brick U `extend_construction_of_restart`, Brick X `metricEquiv_of_ricBound`,
`isSolutionOn_of_extendData`; black boxes (N)/(B) stay sorry. Lemma 3.11's engine
(`HCGCompactness/AllTimesBounds.lean`, `RicBound.lean`) supplies the tail bounds; the extension
branch may IMPORT it (verified cycle-free) but NEVER EDIT it.

**Y1 — new file `Geometry/Flow/RicciFlow/ExtendShiInputs.lean`** (sibling of `MaximalTime.lean`;
imports `Evolution.ExtendViaUniqueness` + `HCGCompactness.AllTimesBounds` + `HCGCompactness.RicBound`;
same-name `.md`). Contents:
1. **Cited Shi producer** (`sorry`, labelled): from `IsSolutionOn` + `Rm04RealizesSolutionConnectionOn`
   + `Rm04NormSqBoundedAt`, conclude the `MovingShiBoundOn`-shaped bounds (order ≤ 3 suffices; use
   whatever order parameter Lemma 3.11's producers consume) for `g_fam` on a tail `[t₀, ω)`.
   Docstring: Shi's estimates (GSM77 Ch. 7); eventual discharge = the banked Bernstein tower.
2. **Single-flow Lemma 3.11 instantiation**: `gSeq := fun _ t => g_fam t` through
   `metricCovOrderWindow_of_*` → `MetricCovDerivOrderBoundOnWindow` + `MetricUniformEquivalentOnWindow`
   on a window `[β, ψ] ⊆ [α, ω)` approaching ω; pick the reference metric `gRef := g_fam α` if the
   producers allow, else adapt via the equivalence. READ the producers' exact hypothesis shapes
   FIRST (`AllTimesBounds.lean:612/773/793/4403`, `RicBound.lean:141`) and mirror them.
3. **`hell` discharge**: `MetricUniformEquivalentOnWindow` → (A)'s `hell` shape (vs `g_fam α`); if
   shapes differ only by window-vs-tail bookkeeping, a thin adapter; Brick X
   (`metricEquiv_of_ricBound`) remains the fallback if the window predicate's reference differs.
4. **The static covariant→chart adapter** (the one genuinely new Lean content):
   `MetricCovDerivOrderBoundOn (order ≤ 3) + equivalence ⟹ (A)'s hC3` — chart partials from
   covariant derivatives by the STATIC recursion `∂ = ∇_ref + Γ_ref·(lower)`, with `Γ_ref` the FIXED
   smooth reference metric's chart Christoffels (bounded with all derivatives on the compact pieces
   of the finitely many `S`-charts), then the `iteratedFDeriv`↔partials norm bridge (grep
   `UniformChartBounds/`, `ChartGramUniformContinuity`, and reuse `jet2_chartGram_d1/d2` from
   `Evolution/ChartRicciJetIdentity.lean`). NO time integration anywhere. If `goodSet`
   non-compactness bites, adjust `hC3`'s statement to compact `Q ⊆ goodSet` AND patch (A)'s proof
   in the same session (sanctioned; (A)'s proof consumes `hC3` only via the box application).
5. Endpoint of Y1: `theorem extendInputs_of_solution … : hell-shape ∧ hC3-shape` (or two theorems)
   consuming exactly `extends_of_rmBounded`'s hypotheses + the cited Shi producer.

**Y2 — rewire `extends_of_rmBounded` (`MaximalTime.lean`)**: replace the `hLimit`/`hglue` leaves:
Y1 → (A) → restart data; (B) `ricci_flow_forward_unique` on `[t_star, ω)` applied to
`g₁ := fun t => g_fam t` vs `g₂ := fun t => rr (t − t_star)` (regularity for g₁ from
`_hS.smoothMetric` restricted; for g₂ from (A)'s fields via the time-shift, mirroring Brick U's
`hshift` pattern; PDEs via `.mono` (`Ici t_star ⊆ Ici α`) and the shift chain rule; `h0` from
`rr 0 = g_fam t_star`) → `hagree_overlap` → `extend_construction_of_restart` →
`isSolutionOn_of_extendData` (call-site pattern already at MaximalTime.lean:304) →
`ExtendsPastEndpoint`. DELETE the `hglue` have-block and the `hLimit` leaf. Do NOT edit
`CinftyLimitGlue.lean` (the old construction goes dormant; a separate cleanup brick will deprecate
it per the transitions rule).

**Rules:** claim `ExtendShiInputs.lean` + `MaximalTime.lean` (Y2) via lake-locked; off-limits:
EVERYTHING under `HCGCompactness/` (import-only!), `ShortTime*/`, `DeTurck*`, `CinftyLimitGlue.lean`
(read-only), frozen `JetGlueParam.lean`; (N)/(B) sorries untouched. Verify: focused checks + targeted
builds (`+…ExtendShiInputs`, then `+…MaximalTime`). **Acceptance:** after Y2, `MaximalTime.lean` has
NO sorry; `#print axioms extends_of_rmBounded` shows `sorryAx` ONLY via the three cited inputs
((N) `ricci_flow_unif_existence`, (B) `ricci_flow_forward_unique`, the Y1 Shi producer) — grep the
proof to confirm no other sorried name is referenced. Report the axiom list verbatim. Thread-crash
flakes: retry with `-LeanThreads 3`. Stop per CLAUDE.md.

## RESOLVED (was: PAUSED 2026-06-20) — the (A)-truth objection is addressed by the (N)-decomposition above; (A) is no longer claimed as a black box but proved from (N), whose truth was verified non-circular. Original pause note kept below for the record.

(A) "interior restart reaches past ω" is FALSE in general: at a genuine maximal/singular time ω the
existence time from `g(t*)` collapses to 0 as `t* → ω`. (A) holds ONLY under bounded curvature, and
ONLY via a **uniform/stable existence time** (existence time ≥ `T₀(|Rm| bound)`, or lower-
semicontinuity of the existence time). The current short-time existence (`∃ T` per `g₀`, no
uniformity) does NOT give this, so (A) is **not dischargeable from it**. Decision: PAUSE the route;
once the short-time-existence theorem is obtained/revised in a form that yields the uniform/stable
existence time, REVISE (A) (its hypotheses must thread the curvature bound through the existence
theorem — `CinftyLimitData` alone is not obviously enough; the uniformity is the real content).
`Evolution/ExtendViaUniqueness.lean` keeps (A) + (B) as stated typecheck-verified obligations
(sorry); do not attempt to discharge (A) until short-time existence is settled.

## BRICK U — KICKOFF PROMPT for an Opus 4.8 executor session (written by Fable, 2026-06-20)

**Paste-pointer for the executor:** *"Work in `E:\testdifferential-geometry`. Read `CLAUDE.md`,
`important_lesson.md`, then `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.md`
section 'BRICK U' — implement exactly that brick and report back. Do not touch any file it marks
off-limits."*

### Context (self-contained)

`extends_of_rmBounded` (MaximalTime.lean:247, Hamilton-3D BBS pillar) is being re-routed: instead of
restarting the flow AT the endpoint ω (which needs blocked endpoint regularity), we restart at an
interior `t* < ω` and use forward uniqueness. The two PDE facts (A) `ricci_flow_interior_restart`
and (B) `ricci_flow_forward_unique` in `ExtendViaUniqueness.lean` are PAUSED obligations (statements
will be revised when the quantitative short-time existence arrives). **Brick U builds the CONSUMER:
the sorry-free assembly that turns restart data + the uniqueness consequence into the extension
tuple.** It is fully decoupled from (A)/(B): it takes their OUTPUT SHAPES as hypotheses and the
uniqueness consequence as a plain agreement hypothesis, so later statement revisions cost nothing.

### Target (state + prove, sorry-free, in `ExtendViaUniqueness.lean`)

```lean
theorem extend_construction_of_restart
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (hαω : α < omega)
    -- left flow data (later extracted from IsSolutionOn; here plain hypotheses):
    (hleft : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici α) t)
    (hsmooth_left : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ioo α omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont_left : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ico α omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    -- restart data at an interior time t* (the (A) output shape, taken as hypotheses):
    {t_star TT : ℝ} (ht1 : α ≤ t_star) (ht2 : t_star < omega) (hreach : omega < t_star + TT)
    (rr : ℝ → SmoothRiemannianMetric I M)
    (hrr_smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hrr_cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hrr_pde : ∀ t ∈ Set.Ico (0 : ℝ) TT, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Set.Ici 0) t)
    -- the uniqueness CONSEQUENCE (decoupled from (B)'s exact statement):
    (hagree_overlap : ∀ s ∈ Set.Ico t_star omega, rr (s - t_star) = g_fam s) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ g_ext : ℝ → SmoothRiemannianMetric I M,
      (∀ s : ℝ, s < omega → g_ext s = g_fam s) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
          (Set.Ioo α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
          (Set.Ico α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico α (omega + ε), ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_ext s).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (g_ext t) x v w) (Set.Ici α) t)
```

This output tuple is EXACTLY the shape `ricci_flow_extends_construction` (CinftyLimitGlue.lean:653)
returns and `isSolutionOn_of_extendData` (ExtendedSolutionRegularity.lean:993) consumes — do not
change it.

### Construction + proof route

`ε := t_star + TT − omega` (`> 0` by `hreach`); `g_ext := gluedFamily g_fam (fun u => rr (u + (omega - t_star))) omega`
(gluedFamily: CinftyLimitGlue.lean:294; `_of_lt` :300, `_of_ge` :305, `_eq_left` :314).

1. **Master lemma `hext_eq_r`: `∀ s, t_star ≤ s → g_ext s = rr (s − t_star)`.** For `s < omega`:
   `gluedFamily_of_lt` + `hagree_overlap` (note direction: rr (s−t*) = g_fam s). For `s ≥ omega`:
   `gluedFamily_of_ge` gives `rr ((s − omega) + (omega − t_star)) = rr (s − t_star)` by `ring_nf`.
   (No TT cap needed in this identity — TT only bounds where rr has good properties.)
2. **agree**: `gluedFamily_eq_left`.
3. **gram_smooth** on `Ioo α (omega+ε) ×ˢ B`: locality (`contMDiffOn_of_locally_contMDiffOn`) over
   the OPEN cover `(Ioo α omega ×ˢ B) ∪ (Ioo t_star (omega+ε) ×ˢ B)` (covers since `t_star < omega`):
   - piece 1: congr to `g_fam` via `gluedFamily_of_lt`; use `hsmooth_left`.
   - piece 2: congr to `(fun p => chartGram (rr (p.1 − t_star)) …)` via `hext_eq_r`; this is
     `hrr_smooth` composed with the time-shift `Ψ : (s,x) ↦ (s − t_star, x)`. `Ψ` is `ContMDiff
     ((𝓘(ℝ,ℝ)).prod I) ((𝓘(ℝ,ℝ)).prod I) ∞` via `(contMDiff_fst.sub contMDiff_const).prodMk
     contMDiff_snd`; `MapsTo` : `Ioo t_star (t_star+TT) ×ˢ B → Ioo 0 TT ×ˢ B`. Use
     `ContMDiffOn.comp (hrr_smooth …) Ψ.contMDiffOn hmaps`. (`omega + ε = t_star + TT` — `ring_nf`.)
4. **gram_cont** on `Ico α (omega+ε) ×ˢ B`: pick `m := (t_star + omega)/2`. Split into the two
   RELATIVELY CLOSED pieces `(Icc α m ×ˢ B)` (there `g_ext = g_fam`, use `hcont_left.mono`) and
   `(Ici m ×ˢ B) ∩ carrier = Ico m (omega+ε) ×ˢ B` (there `g_ext = rr(·−t*)` since `m > t_star`; use
   `hrr_cont` ∘ shift, shift continuous). Trap: Mathlib's ContinuousOn-union lemma names vary — if
   a direct union lemma resists, prove `ContinuousWithinAt` pointwise by case `p.1 ≤ m` / `m ≤ p.1`
   with `ContinuousWithinAt.mono` + congr on a within-neighborhood. Either route acceptable.
5. **PDE** on `Ico α (omega+ε)` — simpler than the old route (NO one-sided cross-derivative needed):
   - `t < omega`: the coefficient function `s ↦ (g_ext s).inner x v w` agrees with `s ↦ (g_fam s).inner x v w`
     on `Iio omega`, a neighborhood of `t` (open). `hleft t` + `HasDerivWithinAt.congr_of_eventuallyEq`
     (eventually-eq within `Ici α` from `Iio omega ∈ 𝓝 t`), RHS rewrites via `g_ext t = g_fam t`.
   - `omega ≤ t < omega+ε`: then `t − t_star ∈ (0, TT)` (positive since `t ≥ omega > t_star`). `hrr_pde`
     at `t − t_star` is within `Ici 0`, and `t − t_star > 0` is INTERIOR to `Ici 0` →
     `HasDerivWithinAt.hasDerivAt (Ici_mem_nhds (by linarith))` → full `HasDerivAt` of
     `u ↦ (rr u).inner x v w` at `t − t_star` → composed with `s ↦ s − t_star` (derivative 1,
     `HasDerivAt.comp` or `.scomp`, chain rule multiplies by 1) → `HasDerivAt` of
     `s ↦ (rr (s − t_star)).inner x v w` at `t` → `.hasDerivWithinAt` for `Ici α` → congr to `g_ext`
     via `hext_eq_r` on the neighborhood `Ioi t_star ∈ 𝓝 t` → RHS via `g_ext t = rr (t − t_star)`.
6. Keep every helper `private` unless reusable; the public statement is only `extend_construction_of_restart`.

### Rules / off-limits (multi-agent)

- Claim ONLY `Evolution/ExtendViaUniqueness.lean` via `./scripts/lake-locked.ps1 claim`. Release when done.
- Do NOT modify: `MaximalTime.lean`, `CinftyLimitGlue.lean` (read-only reuse), anything under
  `HCGCompactness/` (another planner's lane), `ShortTime*/`/`DeTurck*` files (coworker's lane),
  `Analysis/Calculus/SmoothExtension/JetGlueParam.lean` (frozen).
- Do NOT modify or try to prove the (A)/(B) obligations in this file (statements pending revision);
  the new theorem must NOT cite them (its hypotheses replace them).
- Verify: focused `lake env lean` check, then `./scripts/lake-locked.ps1 build
  +DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendViaUniqueness`. GREEN = build
  success with the file's only sorries being the two pre-existing obligations (A)/(B).
- Record outcome + lessons in this `.md` (section below), per CLAUDE.md. Stop rules per CLAUDE.md
  (3 genuinely different failed routes on one lemma → stop and report exactly).

### Acceptance (planner runs on report-back)

Targeted build green; `#print axioms DifferentialGeometry.PDE.RicciFlow.extend_construction_of_restart`
shows no `sorryAx`; diff touches only `ExtendViaUniqueness.lean` (+ its `.md`); statement matches the
target shape above (hypothesis names may differ; output tuple may not).

## BRICK U — DONE (2026-07-02)
`extend_construction_of_restart` is stated and proved **sorry-free**, GREEN in a full targeted build
(`+…Evolution.ExtendViaUniqueness`, all 9367 jobs). `#print axioms` = `[propext, Classical.choice,
Quot.sound]` — **no `sorryAx`**, confirming it does NOT transitively touch the two paused (A)/(B)
obligations `ricci_flow_interior_restart` / `ricci_flow_forward_unique` (whose `sorry`s at lines 52/74
are the file's only sorries and are intentionally left).

Shape: takes the (A)/(B) OUTPUT shapes as hypotheses (`hleft` PDE on `Ico α ω`, restart data
`rr`/`hrr_pde` on `Ico 0 TT`, overlap `hagree_overlap`), returns the extension tuple
`∃ ε>0, ∃ g_ext, agree-below-ω ∧ gram-smooth on `Ioo α (ω+ε)` ∧ gram-cont on `Ico α (ω+ε)` ∧ PDE on
`Ico α (ω+ε)``. Construction: `ε := t_star+TT-ω`, `r u := rr (u+(ω-t_star))`,
`g_ext := gluedFamily g_fam r ω` (reuses `CinftyLimitGlue`, read-only). Key haves: `hext_eq_r`
(`t_star ≤ s → g_ext s = rr (s-t_star)`), `hagree` (`s<ω → g_ext s = g_fam s`), time-shift smoothness
`hshift`. Smoothness via two-piece `contMDiffOn_of_locally_contMDiffOn` + `ContMDiffOn.comp hshift`;
seam continuity via `ContinuousWithinAt.union` + `continuousWithinAt_of_notMem_closure`; PDE by cases
on `t<ω` (`hleft` + `congr_of_eventuallyEq`) vs `ω≤t` (`hrr_pde.hasDerivAt` + `HasDerivAt.comp` chain
rule for `s↦s−t_star` + `congr_of_eventuallyEq`).

### PLANNER ACCEPTANCE — ✅ ACCEPTED (Fable, 2026-07-02)
Independently verified: (1) exactly 2 sorries in the file, lines 68/84 = the paused (A)/(B) bodies;
(2) zero references to `ricci_flow_interior_restart`/`ricci_flow_forward_unique` in or below the new
theorem — decoupling holds; (3) diff confined to this file (+186) and this note (+170/−6); no
off-limits file touched; (4) executor's full-build GREEN (9367 jobs) + axiom check
`[propext, Classical.choice, Quot.sound]` accepted as authoritative. Statement matches the kickoff
target shape (incl. the `_hαω` unused-marker). **The consumer assembly of the
interior-restart+uniqueness route is settled API.** Remaining on this route: solely the paused
(A)/(B) statement decision (user-owned; see PAUSED section).

### Durable env lesson (cost me ~5 build cycles)
On a full targeted build, individual heavy modules crashed with `libc++abi: … lean::exception: failed
to create thread` → `error: Lean exited with code 3221226505` (0xC0000409). This is **OS thread
exhaustion from concurrent multi-agent builds** (several agents × `LEAN_NUM_THREADS=6` × 16-way lake
parallelism), NOT a source defect. Symptom that fooled me: `lake build` reported 4 upstream modules as
"failed" and EVICTED their (previously stale-but-present) `.olean`s, so the next focused `lake env lean`
died with "object file … .olean does not exist". A DIFFERENT pair of modules crashed on the next run —
the tell that it's load-dependent, not deterministic. Fix that worked: wait for the concurrent lake lock
to clear, then re-run the targeted build with **`-LeanThreads 3`**; the crashed modules built on retry
and the closure converged. Takeaway: a "failed to create thread" / 3221226505 crash + evicted upstream
olean is transient concurrency pressure — retry with fewer threads when the lock is free, do NOT chase it
as an upstream source bug.

## Post-merge frontier audit (2026-07-14)

The live merged sources confirm that both remaining sorries are analytic
frontiers.

For (N), the time selected by
`quasilinear_maxreg_solution_of_nemytskii` is explicit, but depends on two
mixed Lipschitz constants and `‖Nfun 0‖` in Sobolev order
`4 * finrank E + 10`. With background equal to the initial metric, `Nfun 0`
contains `-2 Ric(g0)` rather than vanishing. The present hypotheses bound only
fixed-background metric derivatives through order three, so the merged
high-Sobolev proof does not supply the required uniform time. The smallest
missing API is a quantitative low-regularity DeTurck existence theorem uniform
under exactly those ellipticity and C3 bounds.

For (B), `quasilinear_strong_unique` proves uniqueness only after both
solutions have been realized as fixed points of the same forcing-space map.
The geometric headline does not retain that witness, and no reverse
realization theorem exists. More importantly, the repository has the
DeTurck-to-Ricci conjugating flow but no harmonic-map heat-flow producer that
gauges an arbitrary Ricci flow into a Ricci--DeTurck solution. Filling (B)
therefore requires that gauge producer plus its PDE identity, not an adapter in
this file.

Endpoint accounting remains strict: `ricci_flow_unif_existence` is 0% and
`ricci_flow_forward_unique` is 0%. Their existing consumer assembly is 100%,
but it does not count toward either theorem.

## Analytic producer execution (2026-07-18)

Both exact endpoint theorems remain 0%.  Their public statements were left
unchanged, and no new hypothesis, axiom, opaque constant, or `sorry`-backed
producer was added.  The existing statements are still expected to be true;
the present repository lacks a complete faithful proof route.

### (N) `ricci_flow_unif_existence`

Three mathematically different routes were audited to their first unavoidable
obstruction and ruled out with the current formal API.

1. The proved high-Sobolev fixed-point engine selects time from constants and
   `norm (Nfun 0)` at order `4 * finrank E + 10`; those data are not uniformly
   controlled by the endpoint's order-at-most-three metric hypotheses.
2. In the dimension-three mixed `H3 -> H1` route, the conditional remainder
   assembly is fully checked (named target build and warning-free focused check
   pass), but the proposed pointwise bound on the
   zero-order lower coefficient is false on an `H3`-bounded, `H2`-small ball.
   After the raw Ricci/DeTurck cancellation, the full normal form retains the
   generically nonzero cometric-variation arm
   `D(g^-1)[U] * nabla^2 g`.  With a fixed compactly supported chart bump
   `bump_n(x) = n^(-3/2) phi(n * (x - x0)) K`, take
   `T'_n = bump_n` and `T_n = P0 + bump_n` for fixed small `P0`.  Both endpoints
   stay `H2`-small and `H3`-bounded, their difference is the fixed `P0`, and the
   pointwise coefficient diverges.  The faithful repair is tensor `H1 -> L6`,
   then
   `appCc_h1_h2_h1`, not a coarse `rhs_h1_lip` estimate.  The missing public
   finite-component reconstruction makes this a substantial new analytic
   layer.  Moreover this route assumes `finrank E = 3`, while the endpoint is
   dimension-generic, and it still lacks uniform cross-metric Sobolev constants,
   a uniform spectral-`H1` realization of the existing chart-level RHS bound as
   the common forcing-size bound, and same-horizon smoothing.
3. A dimension-generic Schauder/`W2p` construction would match the C3 data, but
   no such quasilinear parabolic existence/regularization engine is formalized.

Smallest next machinery lemma: a public intrinsic tensor `H1 -> L6` estimate,
followed by the `H1 x H2 -> H1` coefficient-action theorem.  Smallest complete
endpoint design: a dimension-generic low-order solver (or Schauder/`W2p`
engine) with family-uniform constants and horizon-preserving regularization.

### (B) `ricci_flow_forward_unique`

Three different routes were likewise audited to their first unavoidable
obstruction and ruled out with the current formal API.

1. The standard harmonic-map heat-flow gauge is absent: there is no short-time
   map heat-flow producer for an arbitrary Ricci flow, no diffeomorphism
   regularity package, and no proved gauge PDE identity.
2. A direct metric/connection/curvature energy route lacks the coupled evolution
   inequalities and a closed energy estimate, including the boundary-time
   regularization needed for the theorem's `C0`-at-initial-time hypotheses.
   The present API does not derive uniform fixed-background first-derivative
   and parabolically weighted second-derivative bounds near `a` from those exact
   hypotheses.
3. `quasilinear_strong_unique` only compares two forcing-space fixed points.
   There is no geometric Ricci--DeTurck PDE-to-Duhamel converse, and working
   directly in fixed coordinates leaves the Ricci diffeomorphism kernel.

Smallest next lemma: `ricci_edge_bounds`, deriving metric equivalence, an
order-one fixed-background covariant bound, and a `sqrt (t-a)`-weighted
order-two bound on a common short window from the exact endpoint hypotheses.
After it, the next consumer-shaped producers are short-window harmonic-map
heat-flow existence and its gauge identity (`hmHeatShort`/`ricciGaugeShort` in
a future API), followed by local Ricci--DeTurck uniqueness and continuation over
the common interval.  The existing time-dependent ODE-flow uniqueness is
reusable only after that common gauge exists.  Identity-gauge uniqueness for
regularizing Ricci flows from a smooth `C0` initial metric is another faithful
route, but its rough-flow existence/stability machinery is likewise absent.

### Downstream status

`extends_of_rmBounded` remains blocked directly by (N) and (B).  Brick U, the
restart/gluing consumer, is still 100% checked, but this does not make the
maximal-time theorem axiom-clean: the two analytic `sorryAx` dependencies flow
to `rmUnbounded_of_maximal` and the Hamilton continuation package.  HCG
compactness work remains an independent lane; the unconditional Hamilton
positive-Ricci endpoint remains 0%.

## Earlier pause record

The 2026-06-20 pause identified interior-restart existence and forward
uniqueness as upstream of this brick.  The restart statement has since been
revised and its consumer wiring proved; the exact 2026-07-18 analytic status is
the execution record above.  Brick U remains deliberately decoupled from both
producers and is complete independently of them.  Corollary (a) + Lemma 3
remain unnecessary for `hglue` under this route.

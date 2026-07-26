# JetGlueParam.lean — joint hyperplane splice for the Ricci `hglue`

## End goal & where this sits

`extends_of_rmBounded` (`Geometry/Flow/RicciFlow/MaximalTime.lean:247`) is the BBS /
long-time pillar of Hamilton 3D ("bounded |Rm| ⇒ the flow extends past `ω`"). It has
**2 sorries**: `hglue` (line 280) and the DeTurck short-time existence (transitive,
collaborator lane). This file targets the analysis layer needed for **`hglue`**.

`hglue` must produce `CinftyGlueData g_fam r α ω ε` (`Evolution/CinftyLimitGlue.lean:567`):
- **`gram_smooth`**: glued chart-Gram is jointly `C∞` on the *open* slab `Ioo α (ω+ε) ×ˢ baseSet`
  (seam `ω` is interior — this is the genuine **junction smoothness**);
- **`gram_cont`**: jointly `C⁰` on `Ico α (ω+ε) ×ˢ baseSet`;
- **`metric_match`**: `g_fam(s).inner → (r 0).inner` as `s → ω⁻`.

`gluedFamily g_fam r ω s = if s < ω then g_fam s else r (s-ω)`. After shifting the seam to
`0` (`t = s-ω`), the chart-Gram entry is `if t < 0 then fL t else fR t` with
`fL(t)=chartGram(g_fam(ω+t))`, `fR(t)=chartGram(r t)`.

## Provenance of the route

GPT Pro consult (route **A**: match all normal time-jets at the seam by one induction, then a
generic joint hyperplane splice; **not** route B/bootstrap, **not** backward uniqueness, **not**
time-analyticity). Headline theorem = Chow–Knopf GSM77 Ch.6 LTE; the junction-smoothness step is
"left to the reader" in the texts, so this is formalizing the textbook-skipped step.

## KEY DISCOVERY — the engine is already built (`Analysis/Calculus/SmoothExtension/`)

All sorry-free:
- **`IteratedFDerivProdMatch.lean`** — `iteratedFDerivWithin_prod_match`: two families `C∞` on the
  **same** closed slab `Ici 0 ×ˢ V` sharing their one-sided `t`-jet at every seam parameter have
  equal joint iterated Fréchet derivatives at the seam. **This is Pro's "deep step" (the
  bivariate/mixed-partial heart) — already done.** Also `fderivWithin_iteratedFDerivWithin_apply_eq`
  (single-slot `C∞` permutation symmetry, bootstrapped from Clairaut).
- **`SmoothJetGlue.lean`** — `contDiff_if_le_of_jet_match`: the **1-D** (`ℝ → F`) splice. Proof
  architecture (piecewise `ftaylorSeriesWithin`, `HasFTaylorSeriesUpToOn ∞` via
  `hasFTaylorSeriesUpToOn_top_iff'`, seam glued by `HasFDerivWithinAt.union` over `Iic_union_Ici`)
  is the template for the joint version.
- **`BorelHalfLineParam.lean`** — `borel_halfLine_extend_param` (extend a family `C∞` on `Ici 0 ×ˢ K`
  to a two-sided `C∞` `gext` on `univ ×ˢ V`), `borel_interval_extend_param` (two-seam interval),
  plus `reflect_iteratedFDerivWithin` (orientation-reversing seam transport via `reflectFst`) and
  `prodMatch_intervalCutoff`. Needs `[FiniteDimensional ℝ E] [CompleteSpace F]` (fine: `E`=chart
  model `ℝ^d`, `F`=ℝ).

## CORRECTED feasibility — Pro's plan assumed inputs Pro did NOT have

Pro assumed both sides were already `C∞` up to the closed seam endpoint ("probably already settled").
**They are not.** Verified:
- **`CinftyLimitData`** (`CinftyLimitGlue.lean:211`) exposes only `tendsto_left` (chart-Gram **C⁰**
  convergence as `s→ω⁻`) + `ricci_match`. **No** `C∞`-up-to-`ω`.
- **`restart_short_time`** (`:246`) exposes chart-Gram `C∞` on the **open** `Ioo 0 T` + `C⁰` on
  `Ico 0 T`. **No** `C∞` up to closed `0`. Moreover its smoothness is **not even threaded** into the
  `glue` hypothesis of `ricci_flow_extends_construction` (`:640`) — `glue` only receives `r, T,
  hr0, hT, hr_pde`.

So `gram_smooth` (C∞ across the interior seam `ω`) is genuinely **gated** on:
- **Gate-L (BBS lane):** strengthen `CinftyLimitData` to carry `fL` (= `chartGram(g_fam(ω+·))`)
  jointly `C∞` on the closed-right slab `Iic 0 ×ˢ baseSet` (all-order `C∞` convergence — Chow–Knopf
  metric-derivative-bounds Prop via Shi). Producer = `cinftyLimitData_of_solution` (BBS, tasks 39–47).
- **Gate-R (DeTurck lane):** strengthen `restart_short_time`/`ricci_flow_short_time_existence` to
  carry `fR` (= `chartGram(r ·)`) jointly `C∞` on the closed slab `Ici 0 ×ˢ baseSet`, AND thread it
  through `glue`'s signature in `ricci_flow_extends_construction`.

These are the two real frontiers; both live in **other lanes**. This file builds the lane-agnostic
**assembly** that consumes them.

## Build plan (this file = pure analysis, no Ricci)

- **Lemma 1a `contDiffOn_glue_of_seam_param` (THIS TURN):** joint Taylor glue from the *Fréchet*
  seam match given as hypothesis.
  `fL` `C∞` on `Iic 0 ×ˢ V`, `fR` `C∞` on `Ici 0 ×ˢ V` (`V` open), and
  `∀ n, ∀ z∈V, iteratedFDerivWithin n fL (Iic0×V) (0,z) = iteratedFDerivWithin n fR (Ici0×V) (0,z)`
  ⇒ `ContDiffOn ℝ ∞ (fun p => if p.1 < 0 then fL p else fR p) (univ ×ˢ V)`.
  Proof = the 1-D `contDiff_if_le_of_jet_match` mirrored to the product: `Iic 0 → Iic 0 ×ˢ V`,
  nbhd `Iio 0 → Iio 0 ×ˢ V` (product nbhd, needs `V` open), `Iic_union_Ici → Set.union_prod +
  Iic_union_Ici`, `uniqueDiffOn_Iic 0 → UniqueDiffOn.prod (uniqueDiffOn_Iic 0) hV.uniqueDiffOn`.
  Seam-match hypothesis replaces the scalar `hjetF`.

- **Lemma 1b `iteratedFDerivWithin_seam_match` (NEXT):** cross-slab seam match — derive 1a's
  hypothesis from the `t`-slice jets. `fL` `C∞` on `Iic 0 ×ˢ V`, `fR` `C∞` on `Ici 0 ×ˢ V`,
  `∀ i, EqOn (w ↦ iteratedDerivWithin i (fL(·,w)) (Iic 0) 0) (w ↦ iteratedDerivWithin i (fR(·,w))
  (Ici 0) 0) V` ⇒ the Fréchet seam match.
  **Crux** (existing `prod_match` is same-slab `Ici`, this is cross-slab `Iic`↔`Ici`; reflecting one
  side alone flips odd `t`-jets by `(-1)^i`, breaking a naive `prod_match`). Chosen route (uses only
  built tools): Borel-extend `fR` to two-sided `FR` on `univ ×ˢ V'`; then `M_fR(Ici)=M_FR(full)`
  (locality + within=full); reflect BOTH `fL` and `FR` to `Ici` (signs cancel since both reflected →
  matching `t`-jets), apply `iteratedFDerivWithin_prod_match`, transport back via
  `reflect_iteratedFDerivWithin` (`reflectFst∘reflectFst = id`). Needs `[FiniteDimensional ℝ E]
  [CompleteSpace F]`.

- **Public `contDiffOn_glue_of_jet_param`:** 1a ∘ 1b (the caller-facing splice: `t`-slice jets ⇒ C∞).

## Then (Ricci side, other files / gated)

- **Lemma 2 (jet compatibility):** abstract — `fL,fR` `C∞` on closed slabs, both solving
  `∂ₜu = Φ(2-jet of u)` (smooth `Φ`), same boundary value ⇒ `t`-slice jets match. One ℕ-induction
  (invariant: equality of boundary trace functions on `V`). Buildable as pure analysis (takes
  closed-endpoint `C∞` as hypotheses).
- **Lemma 3 (Ricci instantiation):** coordinate Ricci-flow RHS is a smooth function of (metric,
  inv-metric, 1st & 2nd spatial derivs); `g_fam(ω+·)` and `r` satisfy it; boundary values both =
  `chartGram(limitMetric)`.
- **Assembly into `hglue`:** `gram_smooth` from public splice + L2 + L3 + Gate-L + Gate-R;
  `gram_cont` from a plain `C⁰` piecewise glue (`ContinuousOn.union`, easier); `metric_match` from
  `CinftyLimitData.tendsto_left` (already there, `hr0` rewrites `r 0 = limitMetric`).

## Status

- [x] **1a `contDiffOn_glue_of_seam_param`** — joint Taylor glue from the Fréchet seam match. DONE,
  verified (sorry-free, targeted `lake build` green).
- [x] **1b `iteratedFDerivWithin_seam_match`** — cross-slab (`Iic`↔`Ici`) seam match from one-sided
  `t`-jets. DONE, verified. NOTE: the Borel-witness + double-reflection route in the plan above was
  NOT needed; instead proved directly by the SAME induction as `iteratedFDerivWithin_prod_match` but
  comparing two functions across the two slabs, using the public `fderivWithin_iteratedFDerivWithin_apply_eq`
  (transverse `(1,0)` via that commutation + IH on `∂ₜfL,∂ₜfR`; seam-tangential `(0,e)` via IH at all
  seam points + chain rule through `ι : v ↦ (0,v)`). Self-contained — NO Borel, NO reflection, NO
  `[FiniteDimensional]`/`[CompleteSpace]`, NO `private` deps. Cleaner than planned.
- [x] **Public `contDiffOn_glue_of_jet_param`** — `1a ∘ 1b`. DONE, verified. This is the full caller-
  facing junction-smoothness splice: `fL` C∞ on `Iic 0 ×ˢ V`, `fR` C∞ on `Ici 0 ×ˢ V`, one-sided
  `t`-jets agree on `V` ⇒ `fun p => if p.1 ≤ 0 then fL p else fR p` is C∞ on `univ ×ˢ V`.

**⇒ The joint hyperplane splice (Pro's "Lemma 1", the analytic frontier) is COMPLETE.**

### Remaining for `hglue` (all OUTSIDE this file)

- [x] **Gate-R contract (DONE, verified — build green 9469 jobs).** `restart_short_time`
  (`CinftyLimitGlue.lean:246`) now outputs the restart `r`'s chart-Gram `C∞` up to the CLOSED
  initial endpoint, on `Set.Ico 0 T` (= `[0,T)`), supplied by ONE labeled `sorry` (the explicit
  DeTurck closed-endpoint regularity obligation — NOT inferred from interior; CinftyLimitGlue:252).
  `ricci_flow_extends_construction`'s `glue` hypothesis (`:640`) widened to receive it; threaded to
  `MaximalTime.lean:hglue` as `hr_smooth_closed`. `ricci_flow_short_time_existence`, `ham3_*`, and
  the `g_DT→g_fam` conjugating-flow conversion are UNTOUCHED. To later discharge the `sorry`:
  strengthen `conjugating_flow_jointContMDiffOn_interior` to an up-to-`0` variant +
  `pullbackGram_jointContMDiffOn` on `Ico 0 T` (DeTurck conversion lane).
- [~] **Lemma 3 (Ricci instantiation) — substantially EXISTS.** `ExtendedSolutionRegularity.lean`
  already has the full private chain (built for `scalarTime`): `chartInvGramOnE_contDiff_in_metric_at`
  (:254) → `chartChristoffel_contDiff_in_metric_at` (:357) → `chartRiemannTensor_contDiff` (:421) →
  `chartRicciTensor_contDiff` (:456). Each takes the chart-Gram 2-jet (`hp0`/`hp1`/`hp2` = chart-Gram
  + its 1st/2nd spatial partials, ContDiff in the time/metric variable on the +ve-definite locus) and
  concludes the chart-Ricci is ContDiff. This IS "coordinate Ricci is smooth in the metric 2-jet", in
  composed-with-a-smooth-`s`-family form. NEXT: decide whether the time-jet recursion consumes these
  directly (compose-and-differentiate) or wants a standalone `Φ : 2-jet → SymMatrix` smooth lemma;
  promote/relocate from `private` as needed.
- [~] **Lemma 2 → time-jet recursion core (per user).**
  - [x] **Core engine DONE, verified** (`Analysis/Calculus/TimeJetMatch.lean`, sorry-free, 1965 jobs):
    `iteratedDeriv_comp_jet_eq` — `Φ` `C^n` at `uL 0`, curves `uL,uR` `C^n` at `0`, iterated derivs
    agree to order `n` at `0` ⇒ `iteratedDeriv i (Φ∘uL) 0 = iteratedDeriv i (Φ∘uR) 0` for `i ≤ n`.
    Proof = Mathlib `iteratedDeriv_vcomp_eq_sum_orderedFinpartition` (Faà di Bruno) + termwise
    congruence (`uL 0 = uR 0` for the outer `iteratedFDeriv Φ`; `OrderedFinpartition.partSize_le`
    for the inner jet tuple). No explicit universal coefficients — exactly the user's preferred
    "same input jet ⇒ same composite jet."
  - [x] **Within/cross-set variant DONE** (`iteratedDerivWithin_comp_jet_eq`, in TimeJetMatch.lean,
    verified) — covered above. Cross-set `Iic`↔`Ici` handled by `uL 0 = uR 0` + `t = univ` target.
  - [x] **Commute bricks DONE, verified** (`Analysis/Calculus/TimeJetCommute.lean`, sorry-free, 2052
    jobs): `fderiv_deriv_time_comm` (order-1: spatial `fderiv` commutes with time `deriv` for jointly
    `C∞` `G`, via `second_derivative_symmetric` on `uncurry G` + chain rules) and
    `fderiv_iteratedDeriv_time_comm` (iterated: `fderiv` commutes with `iteratedDeriv` in time, by
    induction via `iteratedDeriv_succ'` + the order-1 commute on `∂ₜG`). These are the GLOBAL
    (two-sided) commutes — the "t-jet of ∂ₓG = ∂ₓ of t-jet" step the `H_n` induction needs.
  - [x] **Within commute DONE, verified** (route A, `TimeJetCommute.lean`, sorry-free, 2053 jobs):
    `fderiv_derivWithin_time_comm` (order-1, one-sided in time on `sₜ` via
    `ContDiffWithinAt.isSymmSndFDerivWithinAt` on `uncurry G` over `sₜ ×ˢ V`) and
    `fderiv_iteratedDerivWithin_time_comm` (iterated, induction on the order-1). These give the
    one-sided `Iic`/`Ici` "t-jet of ∂ₓG = ∂ₓ of the t-jet" step. **The full commute toolkit
    (global + within, order-1 + iterated) is complete.** Key idioms recorded: `2 ≤ ∞` via
    `WithTop.coe_le_coe.mpr le_top` (NOT `le_top`, since `∞ ≠ ⊤`); inline the chain-rule comp (don't
    ascribe `fun s => G s y`, else `g` becomes a metavar — let `hg` pin `g = uncurry G`).
  - [x] **ALL analysis bricks for corollary (a) VERIFIED** (sorry-free): jet-propagation cores
    `iteratedDeriv_comp_jet_eq` / `iteratedDerivWithin_comp_jet_eq`; four commutes
    `fderiv_{deriv,iteratedDeriv,derivWithin,iteratedDerivWithin}_time_comm`; product-decomposition
    CLM-commute `iteratedDerivWithin_clm_comp` (`iteratedDerivWithin n (L∘f) = L (iteratedDerivWithin
    n f)`, via `ContinuousLinearMap.iteratedFDerivWithin_comp_left`). `jetMatch_of_evolution` is now
    pure WIRING of these.
  - [x] **`jetMatch_of_evolution` PROVEN** (`Analysis/Calculus/TimeJetEvolution.lean`, sorry-free,
    2056 jobs) — corollary (a)'s main induction: `GL,GR` with the same evolution `∂ₜG = Φ(jet2 G)`
    (smooth Φ) + equal boundary ⇒ equal one-sided time jets `∂ₜⁿG(0,·)` at the seam. Strong induction
    (`Nat.strong_induction_on`) + `iteratedDerivWithin_succ'` + evolution-`iteratedDerivWithin_congr`
    + the core `iteratedDerivWithin_comp_jet_eq`. The curve-jet match is factored as the explicit
    hypothesis `hcurveJet`.
  - [x] **Discharge `hcurveJet`** (`curveJet_match`, TimeJetEvolution.lean) — **DONE, sorry-free**
    (2026-06-20). `simp only [jet2]` then nested `iteratedDerivWithin_prodMk` (pair decomposition via
    single `fst`/`snd` CLMs — NOT `.comp`, which left a metavar) to split the 2-jet triple; component
    `C∞` via `ContDiffWithinAt.fst/.snd` on `hcurveL`. value slot = `hval`; fderiv slot =
    `← fderiv_iteratedDerivWithin_time_comm` ×2 + `heqf.fderiv_eq` (value-jet fns `=ᶠ[𝓝 w]` on open
    `V`); fderiv² slot = outer commute via NEW `spatialFDeriv_contDiffOn` (spatial `fderiv` of a
    jointly-`C∞` family is jointly `C∞`: `(fderivWithin (uncurry G) S ·).comp inr` + `((compL).flip
    inr)` postcomp) + inner commute under the `𝓝 w` binder (`filter_upwards`, each `y∈V`) +
    `eventuallyEq_of_mem`.fderiv_eq. The `G := fun t y => fderiv ℝ (GL t) y` beta-redex matched under
    `rw` without massaging. `jetMatch_of_evolution` now folds this inline — NO abstract `hcurveJet`
    hyp; takes hGL/hGR/haccL/haccR/hV. **Corollary (a) FULLY PROVEN, self-contained.**
  - [ ] **Corollary (a) (jet match) — EXECUTABLE DESIGN** (all analysis bricks above are verified).
    Abstract `Hₙ` lemma `jetMatch_of_evolution` (component-scalar level; `F'` = ℝ or matrix entry):
    HYPS — `GL : ℝ→E→F'` `C∞` on `sₜL ×ˢ V`, `GR` on `sₜR ×ˢ V` (`sₜL=Iic 0`, `sₜR=Ici 0`, `V` open,
    both `sₜ` unique-diff + accumulated); `Φ : F' × (E→L[ℝ]F') × (E→L[ℝ] E→L[ℝ]F') → F'` with
    `ContDiffAt ℝ ∞ Φ (seam 2-jet)`; evolution `derivWithin (GX·w) sₜX t = Φ (GX t w, fderiv(GX t·)w,
    fderiv(fun w'=>fderiv(GX t·)w') w)` (∀ t∈sₜX, w∈V); boundary `EqOn (GL 0) (GR 0) V`. CONCLUSION
    `∀ a, ∀ w∈V, iteratedDerivWithin a (GL·w) sₜL 0 = iteratedDerivWithin a (GR·w) sₜR 0`.
    PROOF — induction on `a`, invariant ∀w∈V (function-level). Step `a→a+1`:
    `iteratedDerivWithin (a+1) (GX·w) sₜX 0 = iteratedDerivWithin a (derivWithin (GX·w) sₜX) sₜX 0`
    (`iteratedDerivWithin_succ'`) `= iteratedDerivWithin a (fun t => Φ(2jetX t w)) sₜX 0` (evolution).
    Match the two via `iteratedDerivWithin_comp_jet_eq` (core) on the curve `uX_w(t)=2jetX t w`,
    `Φ`; its `hjet` (curve-jets agree to `a` ≤ n) by COMPONENTS: value = IH; `fderiv`-slot via
    `fderiv_iteratedDerivWithin_time_comm` (commute) + IH-as-EqOn-V ⇒ `EventuallyEq.fderiv_eq`;
    `fderiv²`-slot = commute applied twice. `uX_w` is `C∞` (spatial `fderiv` of jointly-`C∞`).
  - [ ] **Standalone `Φ` (Lemma 3 proper)** — instantiate the above `Φ` for chart-Ricci: define the
    coordinate Ricci as a function of the Gram 2-jet (inverse via `contDiffAt_ring_inverse` on the
    +ve-def/`IsUnit` locus, then Christoffel/Riemann/Ricci polynomials), prove `ContDiffAt`, and the
    identity `chartRicci(g) at y = Φ(2-jet of chartGram(g) at y)`. Reuse `chartRicciTensor_eq_*`
    (`Analysis/Spectral/Intrinsic/DeTurckCoefficients/RicciDiffAffine.lean`) + the matrix-ContDiff
    pattern in `ExtendedSolutionRegularity` (`matrixDet_contDiffOn`, `matrixAdjugate_contDiffOn`).
    Large; the one big remaining concrete construction for corollary (a).
  - [ ] **Corollary (b) (convergence → endpoint smoothness, Gate-L leverage).** local `Cᵏ`
    convergence (every finite `k`) + evolution eq ⇒ joint `ContMDiffOn` up to the one-sided endpoint.
    Derivative-loss bookkeeping ≈ `|β|+2(n+1)`; pin only once Lemma 3's evaluator dependency is fixed.
- [ ] **Gate-L (BBS lane):** strengthen `CinftyLimitData` to expose `g_fam`'s chart-Gram `C∞` up to
  CLOSED `ω` (`Iic`-side closed half-slab), via corollary (b) + local `Cᵏ` convergence (NOT mere
  pointwise derivative limits — see user's failure signal). Producer = `cinftyLimitData_of_solution`.
- [ ] **Assembly:** `CinftyGlueData.gram_smooth` from the public splice + Lemma 2(a) + Lemma 3 +
  Gate-L + Gate-R; `gram_cont` = `C⁰` piecewise glue; `metric_match` = `tendsto_left` + `hr0`.

**KNOWN assembly bridge (flag):** the frozen splice's right hypothesis is on `Ici 0 ×ˢ V` (unbounded
above) but the restart only gives `Ico 0 T` (bounded). Assembly needs a bounded-right-slab variant of
`contDiffOn_glue_of_jet_param` — addable in a NEW file importing (NOT reopening) `JetGlueParam.lean`,
since the seam analysis is purely local at `0`.

**`hglue` cannot be closed until Gate-L opens and Lemma 2/3 are assembled.** Gate-R is now an
available hypothesis; this file's splice is the ready assembly tool.

Verification policy: focused `lake env lean` read-only first, then `lake-locked check`. Do not record
commands/logs here — only pass/fail + exact blocker.

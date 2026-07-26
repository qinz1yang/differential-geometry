# TowerProducer

P5 producer: from a Ricci-flow solution (+ standing time-side inputs) to the all-`m` Bernstein–Bando–
Shi derivative estimate. Intended to be the gating brick between the (DONE) StarSum chain and the
(BANKED) Bernstein machinery.

## 2026-06-13 EXECUTOR — STOP: prescribed target `IteratedRmTowerOn` is the WRONG interface

I did NOT create `TowerProducer.lean`. The prompt's target — produce `IteratedRmTowerOn` and feed
`bernsteinShi_solution_estimate` — is **not satisfiable from the StarSum2 route**, for two independent
reasons in the `starBound` field. Producing it would require fabricating a `star` that cannot meet
`starBound` (a frontier-hiding wrapper, forbidden by CLAUDE.md). Logging the finding + the corrected
target instead, per the stop condition "a banked lemma's shape is wrong".

### The mismatch (evidence)

`IteratedNablaRmTower.IteratedRmTowerOn.starBound` (IteratedNablaRmTower.lean:320) demands, per `j`:
  `|star k t x j m| ≤ (Fintype.card Idx)^2 · √(w j)·√(w (k−j))`     -- constant EXACTLY card², per-`j`.
and `towerReactionMulti = nablaRmReactionMulti (level k) (star k) = Σⱼ 2·Σ_m level(m)·star(j)(m)`
(NablaRiemannHeat.lean), so the residual must be SPLIT as `Σⱼ star_j` with each `star_j` per-`j`-bounded.
`bernsteinShi_solution_estimate` (BernsteinShiSolution.lean:145) consumes exactly this `IteratedRmTowerOn`.

What StarSum2 actually gives (`TowerHeat.resStarBoundLF`):
  `|T y (frame·y)| ≤ C · Σⱼ √(stNormSq j)·√(stNormSq (k−j))`        -- SUMMED, single constant `C`.
with `C` from `StarSum2.bound` (StarSum2.lean:568): `zero→0`, `add→Ca+Cb`, `smul→|c|·Ca`,
`base (a,b,r) → card^(2+r)`. The dim-3 residual is a SUM of many base terms with metric factors
(`r ≥ 1`: the Uhlenbeck `−2B#−drift` KN terms, the gamma `sigmaRic` terms, the spatial-commutator
terms), so `C ≥ card^(2+r) > card²`, and summed `C ≫ card²`, growing with `k`.

Two fatal gaps, both in `starBound`:
1. **No per-`j` decomposition.** `resStarBoundLF` bounds the WHOLE residual array; it does not produce
   arrays `star_j` with `Σⱼ star_j = residual`. (T's StarSum2 structure IS `a`-indexed, so a per-`a`
   bucketing exists in principle, but that needs a NEW per-bucket `StarSum2` bound, not the public
   summed `StarSum2.bound`.)
2. **Constant.** Even a proportional split `star_j := combinedStar · √wⱼ√w_{k−j}/Σᵢ√wᵢ√w_{k−i}` gives
   `|star_j| ≤ C·√wⱼ√w_{k−j}`; the rigid `card²` requires `C ≤ card²`, false (C > card², see above).

### The correct target (recommended): `BernsteinTower` directly (summed, arbitrary `c`)

`BernsteinShiHigher.TowerHeatBoundOn w wLap c k` (BernsteinShiHigher.lean:478) takes the **summed**
reaction `towerReactionSum = Σⱼ c·√(w j)·√(w (k−j))·√(w k)` with an **arbitrary** `c`
(`BernsteinTower.hc : 0 ≤ c`). `BernsteinTower.estimate_div` (BernsteinShiHigher.lean:1311) yields the
SAME all-`m` bound shape `w m t x ≤ (towerConst c α m)²·K²/tᵐ` directly from a `BernsteinTower` — no
`IteratedRmTowerOn` needed. (`bernsteinShi_solution_estimate` is itself just
`IteratedRmTowerOn → BernsteinTower → estimate_div`; bypass the first arrow with a direct
`BernsteinTower` whose `c` is the StarSum2 summed constant.)

So `TowerHeatBoundOn`/`BernsteinTower` is the interface the StarSum2 summed bound was built to feed —
the planner's earlier "the Bernstein consumer takes an arbitrary constant" note (StarSum2.md brick-4
plan) is exactly this. The `IteratedRmTowerOn` per-`j`-card² interface is the OLD pre-StarSum2 shape
(it models each `star_j` as a single clean ∗-contraction); StarSum2 deliberately replaced the explicit
per-`j` split with a single residual + summed bound.

### Recommended next target (for the planner)

Retarget the producer to `bernsteinTower_of_solution` / a `towerHeatBound_of_solution` core producing
`∀ k, TowerHeatBoundOn w wLap c k` (with `w k = nablaKRm04NormSqIntrinsic S k`, `c` = the StarSum2
summed reaction constant), then `estimate_div` for the all-`m` bound. The genuine remaining content is
the reaction-bound assembly (already scoped in `TowerHeat.md` P5 plan, steps 4–9):
- step 1-3 BANKED: `nablaKRm04NormHeatEquationOn_intrinsic` (heat eq), reaction-collapse
  `nablaKRm04Reaction_orthoBasis_eq_compContract` (reaction = `2⟨∇ᵏRm, combinedStar⟩`), and
  `resStarLFU` (residual = comp T).
- step 4-8 REMAINING (smallest next brick): `reaction ≤ towerReactionSum` via Cauchy–Schwarz on the
  contraction + Minkowski `combinedStar = ricStar + residual`, with `abs_ricStarArray_le` (j=0) and
  the INTRINSIC residual-norm bound from `resStarBoundLF` (per-component → L² via
  `compNormSqMulti_orthoBasis_eq_normSq0S` + `compNormSqMulti f ≤ card·B²`, the not-yet-banked helper).
- step 9 + fields: assemble `TowerHeatBoundOn`, then the `BernsteinTower` regularity fields + carried
  standing inputs.

Alternative (Option A, NOT recommended): generalize `IteratedRmTowerOn.starBound`'s constant from
`card²` to a per-level parameter `c k` and propagate through `bernsteinShi_solution_estimate`. This is
a public-API rewrite of the tower interface (against the ground rules) and still needs a per-`a`
`StarSum2` bound for the per-`j` decomposition — strictly more work than Option B for no benefit.

### Files inspected (read-only; nothing edited, no lock taken)

`IteratedNablaRmTower.lean` (IteratedRmTowerOn, towerReactionMulti), `BernsteinShiSolution.lean`
(bernsteinShi_solution_estimate), `BernsteinShiHigher.lean` (TowerHeatBoundOn, BernsteinTower,
estimate_div), `NablaRiemannHeat.lean` (nablaRmReactionMulti), `IteratedRmTowerProducer.lean`
(nablaKRm04Reaction_orthoBasis_eq_compContract, combinedStarArray, ricStarArray, abs_ricStarArray_le),
`StarSum2.lean` (StarSum2.bound constant).

## 2026-06-13 EXECUTOR — TowerProducer.lean created; STEP 1 GREEN (residual-norm infra)

Retargeted per reviewer to the BernsteinTower-direct path. Created `TowerProducer.lean` (imports
TowerHeat + IteratedRmTowerProducer + BernsteinShiSolution + NablaRiemannHeatFrameInvariant). Focused
check GREEN, sorry-free, warning-free.

### Step 1 DONE (GREEN) — the intrinsic L² residual-norm infrastructure

- `compNormSqMulti_le_card (f) (B) (hB : ∀ m, |f m| ≤ B) : compNormSqMulti f ≤ card·B²`
  (Finset.sum_le_sum + sq_le_sq' via abs_le + Finset.sum_const/card_univ/nsmul_eq_mul). Generic.
- `normSq0S_le_card (g) (basis) (horth) (A) (B) (hB : ∀ m, |A (basis∘m)| ≤ B) :
  normSq0S g x s A ≤ card·B²` (rw [← compNormSqMulti_orthoBasis_eq_normSq0S] then step-1a). Generic.
LEAN TRAPS: `pow_le_pow_left` is GONE in this Mathlib — use `sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2`.
`[DecidableEq Idx]` unused in 1a (drop it). `[Module.Finite ℝ E]` flagged unused in 1b but can't be
`omit`ted (instance-synth) → `set_option linter.unusedSectionVars false in` BEFORE the doc-comment.

### Steps 2–3 NOT built this session (each a large proof) — precise plan, shapes verified

**Step 2 — generic reaction bound** (keep it generic in `resid`, NO standing inputs):
target: `2·Σ_m rmC(m)·(ricStarArray ric rmC m + resid m) ≤ towerReactionSum w c k` (= `c·√w_k·Σⱼ√wⱼ√w_{k-j}`).
Route (no Minkowski needed — do it per-component):
- `|ricStarArray ric rmC m| ≤ s·card·Rbnd·√(compNormSqMulti rmC)` = `abs_ricStarArray_le`
  (IteratedRmTowerProducer.lean:246), with `Rbnd` = a Ricci-component bound. SUB-NEED: `Rbnd = C₀·√w₀`
  i.e. `|ric p q| ≤ C₀·|Rm|` (Ricci ≤ Rm in norm at orthonormal) — check if banked (e.g. RicciControlsRm)
  or prove small.
- `|resid m| ≤ B` (the residual bound; in step 3, B := `C·Σⱼ√wⱼ√w_{k-j}` from `resStarBoundLF`).
- per-component triangle: `|combinedStar m| = |ricStar m + resid m| ≤ (s·card·Rbnd·√w_k) + B =: D`.
- `compNormSqMulti combinedStar ≤ card·D²` (step-1a `compNormSqMulti_le_card`).
- Cauchy–Schwarz on the contraction: `|Σ_m rmC(m)·combinedStar(m)| ≤ √(compNormSqMulti rmC)·√(compNormSqMulti combinedStar)`
  — Mathlib `Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_mul_sq_le_sq_mul_sq` (VERIFY exact name/shape).
- `√(compNormSqMulti rmC) = √w_k` at orthonormal (`compNormSqMulti_orthoBasis_eq_normSq0S`, rmC = comp ∇ᵏRm).
- assemble: `2√w_k·√(card·D²) = 2√card·√w_k·D` splits into `(2√card·s·card·C₀)·√w₀·w_k` (≤ c·(j=0 term))
  + `(2√card·C)·√w_k·Σⱼ√wⱼ√w_{k-j}` (≤ c·full sum); pick `c := 2√card·(s·card·C₀ + C)`. `reaction ≤ |reaction|`
  since towerReactionSum ≥ 0. √-algebra: `√w_k·√w_k = w_k` (Real.sq_sqrt, w_k ≥ 0); `√w₀√w_k ≤ Σⱼ√wⱼ√w_{k-j}`
  (j=0 term ≤ nonneg sum).

**Step 3 — `towerHeatBound_of_solution`** (CARRY resStarLFU's standing inputs + the intrinsic-heat-eq inputs):
- `w k := nablaKRm04NormSqIntrinsic S k`; the heat EQUATION is `nablaKRm04NormHeatEquationOn_intrinsic`
  (IteratedRmTowerHeatEq.lean:185), whose conclusion `NablaRm04NormHeatEquationOn (w k)(wLap)(w(k+1))(reaction)`
  unfolds to `∀ t x, HasDerivWithinAt (w k · x) (wLap + (-2·w(k+1) + reaction)) D.carrier t`.
  Its `hT` input IS `resStarLFU`'s per-component identity with **Tdot := metricTrace0S2TensorInBasis(basis)(gInv)(∇^{k+2}Rm) + T**
  (so `comp(Tdot − roughLap) = comp T`, the residual).
- reaction = `nablaKRm04ReactionIntrinsic`; collapse at orthonormal (gInv = δ) via
  `nablaKRm04Reaction_orthoBasis_eq_compContract` (IteratedRmTowerProducer.lean:434) to
  `2·Σ_m (∇ᵏRm m)·combinedStar m`, `combinedStar = ricStarArray + residualComp`, residualComp = comp T.
- THE SUBTLETY (pointwise-in-t basis): heat-eq wants `hgInvDt : ∂ₜgInv = 2 gInv² ric` (evolving metric),
  while the collapse wants `gInv t = δ` (orthonormal AT t). Compatible ONLY for a basis chosen orthonormal
  at the SPECIFIC t (gInv(t)=δ, gInv(r)≠δ, ∂ₜgInv|_t = 2·δ²·ric = 2ric). So TowerHeatBoundOn (∀ t x, ∃ d) is
  proved POINTWISE: at each (t,x) choose basis orthonormal at (t,x), instantiate heat-eq + collapse there.
  The carried standing inputs must therefore be stated ∀-(chosen basis) or supplied as a frame-cover datum.
- assemble TowerHeatBoundOn: `d := wLap + (-2 w(k+1) + reaction)` (the heat-eq deriv), then `d ≤ wLap +
  (-2 w(k+1) + towerReactionSum)` from step 2's `reaction ≤ towerReactionSum`.
- DEFER: full `BernsteinTower` (regularity fields + hw0_bound from K) needs IsSolutionOn; `estimate_div`
  (BernsteinShiHigher.lean:1311) is then a one-liner to `w m ≤ (towerConst c α m)²·K²/tᵐ`.

### Honest status

Step 1 (residual-norm infra) GREEN. The all-`m` bound is NOT yet produced. Steps 2–3 are the real
remaining content — step 2 is a self-contained ~1-session finite-inequality proof (verify the CS lemma
name + the `|Ric| ≤ C₀|Rm|` sub-need); step 3 is the heat-eq plumbing with the pointwise-basis subtlety,
its own session. No frame OBSTRUCTION (pointwise basis resolves it), no new geometry.


## 2026-06-13 EXECUTOR — STEP 2 GREEN (the reaction bound), scope target hit

Reviewer's `reactionContract_le` draft verified GREEN on first check (sorry-free, warning-free). Added
the connector to the literal scope target; both green.

### Step 2 DONE (GREEN)

- `reactionContract_le` (reviewer draft, verified): generic
  `|2·Σ_m level_m·(ricStarArray ric level + resid)_m| ≤ Σⱼ c·(√wⱼ√w_{k−j}√w_k)`,
  `c := 2·√(card^{4+k})·((4+k)·card² + Cres)`. Route: per-component triangle `|ricStar+resid| ≤ Br+Bres`
  (`abs_ricStarArray_le` with `Rbnd := card·√w₀` + `hresid`); `compNormSqMulti_le_card` (step 1) →
  `compNormSqMulti combined ≤ Ncard·(Br+Bres)²`; `Finset.sum_mul_sq_le_sq_mul_sq` (finite CS) →
  `|Σ| ≤ √(cnsm level)·√(cnsm combined)`; `√(cnsm level) ≤ √w_k` (`hlevel`); absorb the Ricci `j=0`
  half via `√w₀√w_k ≤ Σⱼ√wⱼ√w_{k−j}` (`Finset.single_le_sum`).
- `nablaKReaction_le` (added, the SCOPE TARGET): `|nablaKRm04ReactionIntrinsic S k basis gInv ric Tdot t x|
  ≤ towerReactionSum w c k t x` with the same `c`. Proof = `rw [nablaKRm04Reaction_orthoBasis_eq_compContract …
  horth hgInv]` (collapse to the plain contraction, residual = `comp (Tdot − roughLap)`), then
  `le_trans (reactionContract_le …) (le_of_eq (Finset.sum_congr rfl fun _ _ => by ring))` to match
  `towerReactionSum`'s assoc grouping. Carries the orthonormal/level/Ricci/residual inputs as hypotheses.

KEY: the collapse connection works cleanly — `combinedStarArray (ric t x) level resid m` is defeq
`ricStarArray (ric t x) level m + resid m` (so `reactionContract_le` applies through `le_trans` without
unfolding), and `towerReactionSum`'s `c·√·√·√` vs the contraction's `c·(√·√·√)` is just `ring` per term.
This de-risks step 3 (the residual spelling `Tdot − metricTrace0S2TensorInBasis …(∇^{k+2}Rm)` matches
`resStarLFU`'s when `Tdot := roughLap + T`).

## 2026-06-13 REVIEWER — STEP 3 GREEN (TowerHeatBoundOn assembly)

`towerHeatBoundOn_of_heatReact`: given `NablaRm04NormHeatEquationOn w(k) nablaKRmNormLap w(k+1) reaction`
+ `∀ t x, |reaction t x| ≤ towerReactionSum w c k t x` + Laplacian alignment `nablaKRmNormLap = wLap`,
produce `TowerHeatBoundOn w wLap c k`. Proof: take `d := heat-eq derivative`, bound via
`reaction ≤ |reaction| ≤ towerReactionSum` (`le_abs_self` + `linarith`). GREEN, sorry-free, warning-free.

Also fixed `extends_of_rmBounded` statement: added `_hS : IsSolutionOn S`, propagated to consumers
(`rmUnbounded_of_maximal`, `formsSing_of_maximal`, `formsSing_of_maximal_metric`). MaximalTime.lean
compiles (only the expected sorry on `extends_of_rmBounded`).

### Steps 1-3 COMPLETE — TowerProducer theorems (all GREEN, sorry-free)

1. `compNormSqMulti_le_card` — generic per-component → L² bound
2. `normSq0S_le_card` — orthonormal version
3. `reactionContract_le` — generic reaction bound (CS + Ricci absorption)
4. `nablaKReaction_le` — intrinsic reaction ≤ towerReactionSum
5. `towerHeatBoundOn_of_heatReact` — NablaRm04NormHeatEquationOn + reaction bound → TowerHeatBoundOn

### Endgame map: `extends_of_rmBounded` (MaximalTime.lean:153)

**PROOF SKELETON IN PLACE** — `extends_of_rmBounded` now calls
`ricci_flow_extends_construction` with 4 sorry'd inputs, and the
`SolutionAgreesOn` wrapping (metric/connection/Ricci agreement) is fully proved.

Section variables changed: `InnerProductSpace ℝ E`, `NeZero (Module.finrank ℝ E)`,
`CompactSpace M`, `BoundarylessManifold I M`, `I.Boundaryless` added.
Consumers (`rmUnbounded_of_maximal`, `formsSing_of_maximal`, `formsSing_of_maximal_metric`)
updated. `HamiltonPositiveRicci.lean` only references these in comments — no breakage.

#### 4 remaining sorry's (all well-typed, independently attackable)

**Sorry 1 — `hleft` (line ~169): PDE extraction**
- From `IsSolutionOn.equation` (which gives `HasDerivWithinAt` on `D.carrier` for `RegularTime`)
  to `HasDerivWithinAt` on `Set.Ici alpha` for `t ∈ Set.Ico alpha omega`.
- Two gaps: (a) carrier `[α,ω)` → `[α,∞)` domain upgrade (needs interior smoothness →
  `HasDerivAt` for `t > alpha`); (b) PDE at `t = alpha` (right-sided derivative).
- CLASSIFICATION: interface bridge, not mathematical frontier.

**Sorry 2 — `hLimit` (line ~173): CinftyLimitData from BBS**
- The GATING sorry: all of Leaves A+B+C from the old map.
- Leaf A: `IsSolutionOn` → orthonormal basis → `nablaKRm04NormHeatEquationOn_intrinsic` →
  `nablaKReaction_le` → `towerHeatBoundOn_of_heatReact` → `∀ k, TowerHeatBoundOn`
- Leaf B: `TowerHeatBoundOn` + regularity → `BernsteinTower` → `estimate_div` → all-m bounds
- Leaf C: all-m bounds → Arzelà-Ascoli on chart-Gram → `CinftyLimitData`
- CLASSIFICATION: Leaf A = analytic regularity plumbing; Leaf B = mechanical;
  Leaf C = hard analysis (may need new infrastructure)

**Sorry 3 — `hglue` (line ~184): short-time glue (DeTurck)**
- Collaborator's work (`ricci_flow_short_time_existence`). Leave as sorry.
- CLASSIFICATION: out of scope.

**Sorry 4 — `IsSolutionOn Shat` (line ~196): regularity wrapping**
- From `ricci_flow_extends_construction`'s output (chart-Gram C∞ + PDE on extended interval),
  construct all fields of `IsSolutionOn { base := { metric := g_ext } }`.
- Needs: `smoothMetric`, `smoothConnection`, `equation`, `scalarCont`, `scalarTime`,
  `ricciCont`, `rm04Cont`, `nablaRicCont`, `ricciNormSpace`, `ricciNormGrad`.
- Most follow from chart-Gram C∞ → metric smooth → derived quantities smooth.
- CLASSIFICATION: substantial but mechanical interface plumbing.

**What's DONE:**
- `SolutionAgreesOn S Shat [α,ω)` — fully proved (metric, connection, Ricci agreement
  all follow from `g_ext t = g_fam t` for `t < ω`)
- `hwide : alpha < omega + ε` — proved from `0 < ε`
- `Shat : SolutionOn` construction — `{ base := { metric := g_ext } }`
- `ricci_flow_extends_construction` call — fully wired

**Assessment:**
- Sorry 1: interface bridge, doable
- Sorry 2: the hard mathematical core (multi-session)
- Sorry 3: out of scope (collaborator)
- Sorry 4: substantial but mechanical
- The tensor algebra / StarSum2 chain is COMPLETE — all remaining work is analytic/regularity


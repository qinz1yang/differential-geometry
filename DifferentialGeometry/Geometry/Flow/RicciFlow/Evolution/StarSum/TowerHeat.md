# TowerHeat

## 2026-07-14 fixed residual constant

`resStarBoundLF` now exposes a witness equal to `resStarCost k`, together with
its nonnegativity and the existing derivative/residual bounds. Focused
verification and the module refresh passed. This removes the former
pointwise-existential constant mismatch with `TowerHeatBoundOn`.

P4 bridge layer: expose the closed P3 endpoint (`resStarLFU`) plus `StarSum2.bound` as a single
local-frame residual component bound. First step toward `TowerHeatBoundOn`.

## 2026-06-13 EXECUTOR -- `resStarBoundLF` GREEN (P4 bridge), sorry-free

New file `Evolution/StarSum/TowerHeat.lean` (ns `DifferentialGeometry.PDE.RicciFlow`, imports only
`StarSum.TimeRecursion`). Focused check PASSES, sorry-free, warning-free. One small upstream API
change was required (see below).

### What `resStarBoundLF` is

Takes EXACTLY the `resStarLFU` hypotheses (S, hS, k, t, frame, hframe, hu, hdim, horthU, hbase,
baseDt, chrDt, hrm, hchr, hchrId, hswap) -- NO new residual assumption. Concludes:

  exists T, StarSum2 S t k T and exists C, 0 <= C and
    (the resStarLFU per-component time-derivative identity, forall y in u, forall I0) and
    forall y in u, forall m, |T y (fun p => frame (m p) y)|
      <= C * sum_{j in range (k+1)} sqrt(stNormSq j y basis) * sqrt(stNormSq (k-j) y basis)
  with basis := hframe.toBasisAt hy.

Proof = compose: `obtain T,hT,hcomp := resStarLFU ...`; `obtain C,hC0,hCbound := StarSum2.bound
(Idx := Fin 3) hT`; `refine ⟨T, hT, C, hC0, hcomp, ?_⟩`; then per (y,m): build family-metric
orthonormality `horthFam` from `horthU` (family = base is `rfl`, so `exact horthU y hy i j` after
`rw [hframe.toBasisAt_coe hy i/j]`), apply `hCbound y (toBasisAt hy) horthFam m`, and reduce the
basis tuple `(fun p => toBasisAt hy (m p))` to `(fun p => frame (m p) y)` by funext + `toBasisAt_coe`
(`rwa [htuple]`). Closed first try once the API issue below was fixed.

### Upstream API change (necessary, minimal): lfBase/lfChr made public

`resStarLFU`'s time-side hypotheses `hrm`/`hchr`/`hswap` are stated in terms of `lfBase` and `lfChr`
(the local-frame Riemann/Christoffel arrays). These were `private def` in `TimeRecursion.lean`, so a
DOWNSTREAM file could not name them to state the same hypotheses (error: cannot resolve / "Invalid
argument name `I`"). Removed `private` from both `lfBase` and `lfChr` (added a one-line doc note why).
No theorem statement changed. This is the honest fix per CLAUDE.md (a reusable def needed by a
downstream consumer belongs in public API), not a wrapper or new assumption.

### Lessons / API facts

- `StarSum2.bound` requires orthonormality w.r.t. `S.family.metric t` (NOT `S.base.metric t`).
  `SolutionOn.family_metric : S.family.metric = S.base.metric` is `:= by rfl`, so `exact horthU ...`
  (base-metric) closes the family-metric goal by defeq -- no rewrite needed.
- `stNormSq S t j x basis = compNormSqMulti (fun m => nablaKRm04Field S t j x (fun p => basis (m p)))`
  -- the conclusion keeps `basis := hframe.toBasisAt hy`, matching `StarSum2.bound` directly.
- Building a fresh downstream file: its olean deps were NOT cached (prior sessions only ran read-only
  `lake env lean`); a one-off targeted build `+...TimeRecursion` was needed before the focused check
  could import it.
- Unused-section-var linter flagged `[Module.Finite ℝ E]`; `omit` it FAILS ("cannot omit referenced
  section variable" -- it's needed for instance synthesis), so use
  `set_option linter.unusedSectionVars false in` (the codebase's standard approach).

### Project placement (honest)

`resStarBoundLF` is a pure bridge: it moves no new mathematics, it just packages P3 + `StarSum2.bound`
into a directly-consumable local-frame bound.

**CORRECTION (no global basis needed -- earlier draft was wrong):** the global Bernstein consumer is
stated INTRINSICALLY (`nIntrinsic S k t x = |∇ᵏRm|²`, `IteratedRmTowerHeatEq.lean`; the eq-7.4 `n`
predicate in `BernsteinShiHigher.lean` takes intrinsic `w`/`wLap`). A global orthonormal frame
generally does NOT exist (parallelizability) and is NOT required. The per-`u` local-frame bound lifts
to a pointwise INTRINSIC bound with existing infrastructure: at an orthonormal frame the component
sum-of-squares IS the intrinsic norm -- `compNormSqMulti_orthoBasis_eq_normSq0S`
(`NablaRiemannHeatFrameInvariant.lean`) gives `compNormSqMulti (A ∘ basis) = normSq0S g x s A`, so
`stNormSq` at any orthonormal basis = `|∇ʲRm|²(x)`, frame-independent. Pick ANY local orthonormal
frame around each point (always exists -- Gram-Schmidt; codebase has `exists_orthonormalBasisAt`),
apply the bound, rewrite to intrinsic norms; intrinsic results glue with no transition condition. So
frame-existence/invariance is NOT a frontier (both pieces exist).

The genuine remaining P4 work for `TowerHeatBoundOn`: (b) the reaction/heat WIRING -- connect the
residual witness `T` (= comps of `(∂ₜ−Δ)∇ᵏRm`) to the intrinsic reaction `nablaKRm04ReactionIntrinsic`
and assemble the eq-7.4 predicate `n` with `|reaction| ≤ c·Σⱼ√wⱼ√w_{k−j}`; plus discharging the
standing analytic inputs (`hrm`/`hchr`/`hswap`/`hbase`: Uhlenbeck base `∂ₜRm04`, time-regularity black
boxes) at each point's local frame. So: this bridge = done; `TowerHeatBoundOn` = not started; the BBS
pillar `extends_of_rmBounded` and HCG Lemma 3.11 `hShi` that ultimately consume the tower bound remain
open.

## 2026-06-13 EXECUTOR -- exact gap from `resStarBoundLF` to `TowerHeatBoundOn` (P5 plan)

Pinned the literal chain (read `IteratedRmTowerProducer.lean`, `IteratedRmTowerHeatEq.lean`,
`BernsteinShiHigher.lean`, `IteratedNablaRmTower.lean`). Corrected the stale "j-split unbuilt"
frontier note in `IteratedRmTowerProducer.lean` (dated UPDATE block + the theorem one-liner).

### The actual downstream consumer

`BernsteinShiHigher.TowerHeatBoundOn w wLap c k` (and `BernsteinTower.hheat`) wants, per (t,x):
  ∃ d, HasDerivWithinAt (fun s => w k s x) d D.carrier t ∧
       d ≤ wLap k t x + (-2 * w (k+1) t x + towerReactionSum w c k t x)
with `towerReactionSum w c k t x = Σ_{j∈range(k+1)} c·√(w j)·√(w (k-j))·√(w k)` (SUMMED form).
So the per-`j` `IteratedRmTowerOn.starBound` arrays are BYPASSED -- `TowerHeatBoundOn` only needs the
summed reaction bound and `w k = |∇ᵏRm|²` (intrinsic). No global frame; no per-`j` split.

### The chain (all but steps 4-9 already built)

1. `nablaKRm04NormHeatEquationOn_intrinsic` (PROVEN, IteratedRmTowerHeatEq): ∂ₜ(wₖ) = wLapₖ +
   (-2·w_{k+1} + nablaKRm04ReactionIntrinsic). [w_k = nIntrinsic = |∇ᵏRm|², intrinsic]
2. `nablaKRm04Reaction_orthoBasis_eq_compContract` (PROVEN, IteratedRmTowerProducer): at a g(t)-
   orthonormal basis at x, reaction = 2·Σₘ (∇ᵏRm m)·combinedStar m,
   combinedStar = ricStarArray + residual, residual = comp(Tdot − Δ∇ᵏRm) (Tdot a PARAMETER).
3. `resStarLFU` (DONE): with Tdot = the actual ∂ₜ∇ᵏRm, comp(Tdot − Δ∇ᵏRm) = comp(T), T ∈ StarSum2 k.
   (resStarLFU's HasDerivWithinAt IS `∂ₜcomp(∇ᵏRm) = comp(Δ∇ᵏRm) + comp(T)`.)
4-9 (the remaining analytic plumbing, NO new geometry, NO frame obstruction -- all pointwise
   orthonormal/intrinsic):
   4. Cauchy-Schwarz on the contraction: |reaction| ≤ 2·√(w k)·√(compNormSqMulti combinedStar).
   5. Minkowski: √(compNormSqMulti combinedStar) ≤ √(compNormSqMulti ricStar)+√(compNormSqMulti residual).
   6. ricStar (j=0) half: `abs_ricStarArray_le` (per-component) → √(compNormSqMulti ricStar) bound.
   7. residual half: `resStarBoundLF` per-component (|T y (frame·y)| ≤ C·Σⱼ√wⱼ√w_{k-j}) →
      compNormSqMulti(comp T) ≤ card^{4+k}·(C·Σⱼ...)² → √(...) ≤ card^{(4+k)/2}·C·Σⱼ√wⱼ√w_{k-j}.
   8. combine → reaction ≤ Σⱼ c·√wⱼ·√w_{k-j}·√w_k = towerReactionSum (c = some 2·card-power·(C+ric)).
   9. assemble TowerHeatBoundOn: d := the heat-eq derivative value; ≤ via steps 1-8.
   PLUS: discharge Tdot = ∂ₜ∇ᵏRm (the resStarLFU time-side inputs hrm/hchr/hswap/hbase), which bottom
   out on the Uhlenbeck base ∂ₜRm04 (largely discharged) + DeTurck time-regularity black boxes.

### WALL 2 (frame reconciliation) dissolves

`w k`, the heat eq, and the reaction are all INTRINSIC; the orthonormal basis is only a pointwise tool
for the reaction BOUND (pick any g(t)-orthonormal basis at x -- always exists). resStarBoundLF supplies
the residual bound in a smooth orthonormal frame on `u`; at x∈u that frame is orthonormal, and
`compNormSqMulti_orthoBasis_eq_normSq0S` converts the per-component bound to the intrinsic norm
|（∂ₜ−Δ)∇ᵏRm|(x). No coordinate-vs-orthonormal-frame mismatch at the scalar level.

### Smallest next brick (P5 brick 1)

`resStarNormLF` (suggested): from `resStarBoundLF`, the INTRINSIC residual norm bound
  √(normSq0S (S.base.metric t) y (T y)) ≤ card^{(4+k)/2}·C·Σⱼ √(stNormSq j ..)·√(stNormSq (k-j) ..).
Needs a NOT-yet-banked generic lemma `compNormSqMulti f ≤ (Fintype.card (Fin r → Idx))·B²` from
`∀ m, |f m| ≤ B` (Finset.sum_le_sum + Finset.sum_const / sum_le_card_nsmul; pure Mathlib), then
`compNormSqMulti_orthoBasis_eq_normSq0S` + `Real.sqrt` monotonicity. Self-contained, low risk.
Then brick 2 = ricStar intrinsic-norm bound (from abs_ricStarArray_le), brick 3 = the C-S+Minkowski
reaction bound, brick 4 = assemble TowerHeatBoundOn (given a Tdot/time-side producer), brick 5 = the
time-side discharge (Uhlenbeck + DeTurck handoff).

### Status

P5 is a genuine multi-brick phase (the analytic estimate-plumbing + the time-side discharge), NOT a
one-lemma wrap-up -- but it has NO remaining geometric frontier and NO frame obstruction. The hard
mathematical content (the residual = StarSum2 decomposition + its Σⱼ bound) is already done
(resStarLFU/resStarBoundLF). Left for the planner to sequence bricks 1-5; the genuinely-open analytic
input is only the time-side (Uhlenbeck base + DeTurck time-regularity black boxes).


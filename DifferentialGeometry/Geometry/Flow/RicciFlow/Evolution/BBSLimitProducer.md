# BBSLimitProducer — Dispatch C: `cinftyLimitData_of_solution`

## 2026-07-14 endpoint producers

`exists_endMetric` now proves G3: it constructs one smooth endpoint metric and
identifies every chart-Gram entry with its full left limit. Focused verification
passed for that theorem.

The G4 source proof is now isolated as `ricci_tendsto_left` in
`EndpointRicciLimit.lean`. Its route is sequential two-jet compactness:
`metricPreconvFull` extracts a smooth subsequential metric, G3 identifies it
with the prescribed endpoint, and `ricciConv_of_dnConv` gives Ricci convergence.
Focused verification, targeted export, and the axiom probe pass for G4. The BBS
endpoint source is wired to this producer, but its combined file remains
unverified while the G3-side Spectral dependency cache is unavailable.

Current accounting:

- G3 `exists_endMetric`: theorem **100%**, dedicated machinery **100%**.
- G4 `ricci_tendsto_left`: theorem **100%**, targeted-exported and axiom-clean.
- `cinftyLimitData_of_allMBounds`: theorem **0% until the combined file
  verifies**; its source has no remaining local `sorry`.
- Hamilton's positive-Ricci endpoint and all HCG endpoint theorems remain 0%.

The current combined focused check fails before elaborating this file because
the actively modified Spectral module `GalerkinLimitUniformMass` has no exported
object file. This is an external verification blocker, not evidence that the C3
packaging typechecks; C3 therefore remains 0%.

## 2026-07-14 C1+C2 discharge

`bbsAllMBounds` is now proved in the narrower `BBSAllMBounds.lean` module. It
derives an arbitrary-order canonical Riemann-tower bound directly from the
bounded-curvature `IsSolutionOn` input via `movingRmBoundSol`. Focused
verification and its targeted module build passed.

Current accounting:

- `bbsAllMBounds` (C1+C2): theorem **100%**, dedicated machinery **100%**.
- `cinftyLimitData_of_allMBounds` (C3): theorem **0%**. The remaining work is
  the actual smooth endpoint metric and Ricci-continuity extraction from the
  all-order bounds.
- `cinftyLimitData_of_solution`: its composition body is complete, but its
  axiom closure still contains the C3 frontier.

The direct BBS endpoint-limit route is still an alternate route rather than
the current `MaximalTime.extends_of_rmBounded` implementation. Historical
sections below that call `bbsAllMBounds` a `sorry` are superseded by this
update.

## 2026-07-14 uniform residual and C1 assembly pass

- The residual constant obstruction is solved in the verified core stack:
  `StarSum2Cost`, `commStarCost`, `gammaStarCost`, and `resStarCost` produce one
  constant depending only on `k`.
- Smooth local orthonormal frames are already supplied by `smoothOrtho_local`;
  the old G1 entry is obsolete.
- `SolutionTowerHeat.lean` now contains the full source body for `towerHeatSol`,
  directly composing the local-frame residual, inverse-metric evolution,
  pointwise norm heat equation, and reaction bound.
- `towerHeatSol` is still **0% as a theorem** until focused verification passes.
  Its dedicated machinery is about **98%**. The current stop is tooling: an
  active shared Spectral/Elliptic build is rebuilding transitive imports, so
  checks fail on moving missing `.olean` files before reaching this theorem.
- `bbsAllMBounds` remains **0% as a theorem**. After C1 verifies, C2 still needs
  the one-constant-per-target-level Bernstein slab/time-shift assembly. C3
  remains the separate hard smooth-limit and Ricci-continuity analysis.

Producer for the gating `hLimit` sorry in `MaximalTime.lean:171`: from a
bounded-curvature Ricci-flow solution on `[α,ω)`, produce the smooth limit data
`CinftyLimitData g_fam α ω hαω` at the right endpoint `ω`.

Target file (new): `Evolution/BBSLimitProducer.lean`.
Verify with `scripts/lake-locked.ps1 check`.

---

## 0. Target (from MaximalTime.md Dispatch C)

```lean
theorem cinftyLimitData_of_solution
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (… .closedOpen alpha omega hαω)}
    {Rm04 : Real → Tensor04Section (I := I) (M := M)}
    (hS  : IsSolutionOn (I := I) S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    (hbound : Rm04NormSqBoundedAt (I := I) S Rm04) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω
```

`CinftyLimitData` (`CinftyLimitGlue.lean:211`) has **three** fields:
- `limitMetric : SmoothRiemannianMetric I M`  — a **C∞** metric `g(ω)`.
- `tendsto_left : ∀ x₀ x i j, Tendsto (s ↦ chartGramMatrix (g s) x₀ x i j) (𝓝[<] ω)
                  (𝓝 (chartGramMatrix limitMetric x₀ x i j))`.
- `ricci_match : ∀ x v w, Tendsto (s ↦ ricciTensor (g s) x v w) (𝓝[<] ω)
                  (𝓝 (ricciTensor limitMetric x v w))`.

The `hLimit` call site (`MaximalTime.lean:171`) has in scope exactly `_hS`,
`_hRm`, `_hbound` (the hypotheses of `extends_of_rmBounded`), nothing more.

---

## 1. Interface map (all verbatim, gathered 2026-06-13)

### Output / engine (`CinftyLimitGlue.lean`, sorry-free)
- `CinftyLimitData` struct — `:211`.
- `tendsto_nhdsLT_of_bounded_deriv` — `:106`: `f:ℝ→F` (`F` Banach), `HasDerivAt f (f' s) s`
  on `Ioo a b`, `‖f' s‖ ≤ C` ⟹ `∃ L, Tendsto f (𝓝[<] b) (𝓝 L)`. **The C⁰-limit engine.**
- `chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv` — `:176`: scalar chart-Gram
  component version (`F=ℝ`). Drives `tendsto_left` from a `|∂ₜ chartGram| ≤ C` bound.
- `ricci_flow_extends_construction` — `:632` (BANKED, cites DeTurck via
  `ricci_flow_short_time_existence`): consumes `hleft + CinftyLimitData + glue`.

### Bernstein layer (`BernsteinShiHigher.lean` / `BernsteinShiSolution.lean`, sorry-free)
- `TowerHeatBoundOn w wLap c k` — `:478`: `∀ (t:RegularTime D) x, ∃ d,
   HasDerivWithinAt (w k · x) d D.carrier t ∧ d ≤ wLap k t x + (-2 w(k+1) t x + towerReactionSum w c k t x)`.
- `towerReactionSum w c k t x` — `:470`: `∑_{j≤k} c·√(w j)·√(w (k-j))·√(w k)`.
- `BernsteinTower (G : RealizedMetricFamily)` struct — `:493`. Fields:
  `D; w wLap : ℕ→ℝ→M→ℝ; c K α T : ℝ;`
  `hT:0<T; hc:0≤c; hK:0<K; hα:0≤α; hslab: Icc 0 T ⊆ D.carrier;`
  `hregular: t∈Icc 0 T→0<t→t∈D.regular; hw_nonneg; hw0_bound: w 0 t x ≤ K²;`
  `hTK: T ≤ α/K; hheat: ∀k, TowerHeatBoundOn w wLap c k;`
  `hLap: ∀k t∈Icc 0 T, 0<t→ heatOperatorWithDrift G t 0 (w k t) x = wLap k t x;`
  `hw_cont: ContinuousOn (w k) (spacetimeSlab T); hw_space: MDifferentiableAt …;`
  `hw_grad: MDiffAt (gradientFun (G.metric t) (w k t)) x`.
- `BernsteinTower.estimate_div` — `:1311`: `B.w m t x ≤ (towerConst c α m)²·K²/tᵐ`,
  for `t∈Icc 0 T`, `0<t`.
- `towerConst c α m = √(towerConstSq c α m)` — `:292`.

### Heat-equation layer (`Evolution/`, sorry-free)
- `NablaRm04NormHeatEquationOn w wLap w' reaction` — `NablaRiemannHeat.lean:557`:
  `∀ (t:RegularTime D) x, HasDerivWithinAt (s↦w s x) (wLap t x + (-2 w' t x + reaction t x)) D.carrier t`.
- `nablaKRm04NormHeatEquationOn_intrinsic` — `IteratedRmTowerHeatEq.lean:185`. Produces
  `NablaRm04NormHeatEquationOn (nablaKRm04NormSqIntrinsic S k) wLap (…S (k+1)) (nablaKRm04ReactionIntrinsic S k basis gInv ric Tdot)`.
  Inputs: `basis (x:M)→Basis Idx; gInv; ric; Xb; du; normSecond; nablaKRmNormLap; Tdot` plus
  `hinv` (`MetricInverseInBasis ∀t x`), `hfields` (`SmoothBasisFieldsAt`), `hdu` (`DuFieldRealizes`),
  `hHess` (`HessianRealizesNablaDuAt`), `hlapTrace` (`wLap = metricTrace0S2InBasis …`),
  **`hT`** (`∀ regular t, x, I0: HasDerivWithinAt (∇ᵏRm comp) (Tdot comp) D.carrier t`),
  **`hgInvDt`** (`∂ₜgInv = 2·∑ gInv·gInv·ric`).
- `nablaKRm04NormSqIntrinsic S k = (t,x) ↦ normSq0S (g t) x (4+k) (nablaKRm04Field S t k x)`
  — `IteratedRmTowerHeatEq.lean:116`. **`w k`** in all of the above. Frame-independent. `w 0 = |Rm04|²`.

### Reaction-bound layer (`Evolution/StarSum/TowerProducer.lean`, **GREEN, sorry/warn-free**)
- `nablaKReaction_le` — `:178`: at a `g_t`-orthonormal `basis` with `gInv t x = δ`,
  `|nablaKRm04ReactionIntrinsic S k basis gInv ric Tdot t x| ≤ towerReactionSum w c k t x`,
  `c = 2√(card^{4+k})·((4+k)·card² + Cres)`. Inputs: `horth, hgInv, hlevel, hRic, hresid`.
- `towerHeatBoundOn_of_heatReact` — `:228`: `NablaRm04NormHeatEquationOn (w k) lap (w(k+1)) reaction`
  + `∀ t x |reaction|≤towerReactionSum` + `lap = wLap k` ⟹ `TowerHeatBoundOn w wLap c k`.

### Residual layer (`Evolution/StarSum/{TimeRecursion,TowerHeat}.lean`, sorry-free, **dim-3, local-frame**)
- `resStarBoundLF` — `TowerHeat.lean:44`: produces `∃ T, StarSum2 S t k T ∧ ∃ C≥0,
   (∀ y∈u I0, HasDerivWithinAt (∇ᵏRm comp) (comp(Δ∇ᵏRm + T)) D.carrier t) ∧
   (∀ y∈u m, |T y (frame∘m)| ≤ C·∑_{j≤k} √(stNormSq j)·√(stNormSq (k-j)))`.
  Requires `hdim: finrank = 3`, a **local orthonormal frame** `frame:Fin 3→…` smooth on open `u`
  (`hframe : IsLocalFrameOn I E 1 frame u`), `horthU` (orthonormal at `t` on `u`), **and the five
  standing inputs** `hbase, hrm, hchr, hchrId, hswap` (see §3).
  This supplies BOTH the `hT` of `…_intrinsic` (per-comp derivative, `Tdot := Δ∇ᵏRm + T`) AND the
  `hresid` of `nablaKReaction_le` (`Cres := C`, residual `= T = Tdot − Δ∇ᵏRm`).

### Solution data (`Basic/Core.lean`)
- `IsSolutionOn` fields — `:508`: `smoothMetric, smoothConnection, equation, scalarCont, scalarTime,
  ricciCont, rm04Cont, nablaRicCont, ricciNormSpace, ricciNormGrad`.
- `Rm04NormSqBoundedAt S Rm04 = ∃K, ∀ t x, α≤t→t<ω→ curvatureNormSq S Rm04 t x ≤ K`
  (`MaximalTime.lean:124`); `curvatureNormSq = (t,x)↦ normSq0S (g t) x 4 (Rm04 t x)` (`:95`).
  Note `w 0 = nablaKRm04NormSqIntrinsic S 0 = normSq0S (g t) x 4 (Rm04field)` — **matches**
  `curvatureNormSq` once `hRm` identifies `Rm04 t` with the realized `S.base.rm04 t`. So
  `hbound ⟹ hw0_bound` (the `K²` is the Bernstein `K`).

---

## 2. Brick routes (exact)

### C1 — `∀k, TowerHeatBoundOn w wLap c_k k` (with `w = nablaKRm04NormSqIntrinsic S`)
Per target `(t₀,x₀)` (because `TowerHeatBoundOn` is `∀t x ∃d`, and the orthonormal collapse +
`hgInvDt` are only compatible for a basis orthonormal **at** `t₀` — the pointwise-basis subtlety,
TowerProducer.md step 3):
1. Choose a **smooth local orthonormal frame** `frame` on an open `u ∋ x₀`, orthonormal w.r.t.
   `g_{t₀}` at `t₀` on `u`. (Frame existence producer — see §4 gap G1.)
2. `resStarSol S hS hdim k t₀ frame …` ⟹ `T_k`, `C_k`, the per-comp `hT`, and the
   residual bound, with all five former standing inputs produced from the solution. Feed `hT` +
   `hgInvDt` (+ the spatial realization data `hinv/hfields/hdu/hHess/hlapTrace`
   from `hS`) to `nablaKRm04NormHeatEquationOn_intrinsic` ⟹ `NablaRm04NormHeatEquationOn …`.
3. `hRic` (= `|ric|≤card·√(w0)`) from the Ricci-controls-Rm bridge at the orthonormal frame; `hlevel`
   (= `compNormSqMulti(∇ᵏRm comps) ≤ w k`) is `compNormSqMulti_orthoBasis_eq_normSq0S` ▸ defeq.
4. `nablaKReaction_le` (collapse, `gInv=δ`) ⟹ `|reaction| ≤ towerReactionSum w c_k k`.
5. `towerHeatBoundOn_of_heatReact` ⟹ the `∃d` at `(t₀,x₀)`. Quantify over `(t₀,x₀)`.
**Output constant** `c_k = 2√(card^{4+k})·((4+k)card² + C_k)` is `k`-dependent; Bernstein needs ONE
`c`. Resolve by `c := sup_{k≤m} c_k` per target level `m` (BernsteinTower is applied per `m` in
`estimate_div`), or carry `c` as `2·card^{6+m}` as in `bernsteinShi_solution_estimate`'s constant
(`:165`). DECISION D2 (§5).

### C2 — all-`m` bounds
Assemble `BernsteinTower G` with `w = nablaKRm04NormSqIntrinsic S`:
- `hheat` = C1; `hw0_bound` = `hbound` (§1); `hLap` = `hlapTrace`-alignment from `hS`;
  `hw_cont/hw_space/hw_grad` = differential-in-metric regularity from `hS.smoothMetric`;
  `K = √(hbound.K)`; pick `α, T` with `T ≤ α/K`, `Icc 0 T ⊆ carrier` (**time-shift**: Shi measures
  `t` from slab start; to approach `ω` we apply on sub-slabs `[t₁, ω)` — reparametrize, DECISION D3).
- `estimate_div` ⟹ `w m t x ≤ (towerConst c α m)²K²/tᵐ`, i.e. `‖∇ᵐRm‖² ≤ C_m` uniformly on any
  `[t₁,ω)` with `t₁>0` (after the shift). Mechanical given C1 + the regularity fields.

### C3 — `CinftyLimitData` (hard analysis)
- `limitMetric`: For each `x₀,x,i,j`, `s↦chartGramMatrix (g s) x₀ x i j` has `|∂ₜ| = |chartGram of -2Ric|
  ≤ C·|Rm| ≤ C·K` (m=0 bound, from `hbound` alone). `chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv`
  ⟹ a C⁰ limit `L_{x₀,x,i,j}`. ASSEMBLE these into a `SmoothRiemannianMetric` — the limit's
  **smoothness** needs the all-`m` spatial bounds (C2) + a "C∞ limit object from uniform `Cᵐ` bounds"
  builder. (Gap G3 — likely the missing-infrastructure frontier; report by name+layer if so.)
- `tendsto_left`: the same component limits, by construction.
- `ricci_match`: `s↦ricciTensor (g s) x v w → ricciTensor limitMetric x v w` — needs the `m≤2` bounds
  + **Arzelà–Ascoli/equicontinuity** on chart-Gram & its 2 derivatives. (Gap G4 — "MAY need
  Sobolev/interpolation infrastructure not yet present"; report precisely if missing.)

---

## 3. Standing-input ledger (discharged)

`resStarBoundLF` carries five standing inputs. `resStarSol` now discharges all five from
`IsSolutionOn` on a strictly positive-time tail:

| input | meaning | discharged from `hS`? | by |
|---|---|---|---|
| `hbase` | `∂ₜRm04 = Δ+2B−drift` at orthonormal basis (Lemma 6.1) | **YES** | `rm04Base_of_sol` |
| `hrm` | `∂ₜ(lfBase)` frame-comp derivatives | **YES** | `tailTowerData` level zero |
| `hchr` | `∂ₜΓ` frame-comp derivatives | **YES** | `tailChristoffel` via `tailTowerData` |
| `hchrId` | `∂ₜΓ = −∇Ric−∇Ric+∇Ric` value | **YES** | `tailTowerData`, using the inverse-metric identity at an orthonormal frame |
| `hswap` | time/space derivative swap on the Rm tower | **YES** | `frameTowerSwap` via `tailTowerData` |

The old DeTurck-gate diagnosis is superseded. The current C1 frontier is downstream: construct the
smooth local frame required by `resStarSol`, expose the norm heat equation in a pointwise form that
accepts its local component derivative, and supply the scalar differential realizations. The dim-3
hypothesis remains explicit in `bbsAllMBounds`; it is not hidden by this producer.

---

## 4. Banked producers for discharge (verbatim file:line)
- `christoffelEvolution_of_solution` — `Evolution/Connection/MetricCovDerivProducer.lean:203`
  (discharges `hchr`+`hchrId` given `hmetricFrame`, `hSmooth`, `hFdiff`, `hFtdiff`).
- `nablaKRm_timeDeriv_of_solution` — `Evolution/Connection/NablaKRmTimeDeriv.lean:92`
  (all-`k` `∂ₜ∇ᵏRm`; discharges `hchr`; still needs `hrm`, `hswap`).
- `rm04HrmProducer` — `Evolution/UhlenbeckBaseProducer.lean:1486`; `rmBaseDeriv_basis` — `:613`
  (discharge `hrm` modulo `hlich`/`hsc` + `hbase`'s DeTurck smoothness).
- `metricCompInFrame_timeDeriv` — `UhlenbeckBaseProducer.lean:56` (`∂ₜg=−2Ric` from `hS.equation`).
- Frame existence: `ricciEigenBasis3` / `exists_orthonormalBasisAt` (RicciControlsRm.lean) — point
  basis; **smooth local-frame existence (G1) still to confirm**.

---

## 5. DECISIONS (planner's call — STOP per task)

**D1 (signature packaging of the DeTurck frontier).** The target cannot be `(hS,hRm,hbound)→CinftyLimitData`.
Options:
- **(a) packaged standing-input bundle**: add one hypothesis `hReg : BBSTimeRegularity S` (bundling
  `hbase`/`hswap`/metric-frame boxes ∀ regular `t` + local frame) to `cinftyLimitData_of_solution`,
  thread into `extends_of_rmBounded` (cascades to `rmUnbounded_of_maximal`, `formsSing_of_maximal*`).
  Honest, "frontiers explicit"; but changes public signatures.
- **(b) one precise frontier sorry**: keep `(hS,hRm,hbound)→CinftyLimitData` public; localize the
  DeTurck-gated all-`m` bounds to ONE named `sorry` (`bbsAllMBounds`), build C2→C3 honestly on top.
  Matches the project pattern (extends_of_rmBounded already carries precise sorries); `hLimit` wires
  immediately; no cascade. **RECOMMENDED.**
- **(c) full explicit standing-input list** (`hbase/hswap/hmetricFrame/hmix/hdim/frame` as separate
  args, mirroring `resStarBoundLF`): most faithful, heaviest signature.

**D2 (Bernstein constant).** `c_k` is `k`-dependent; `estimate_div` is per-`m`. Use `c := 2·card^{6+m}`
(as `bernsteinShi_solution_estimate`) or `sup_{k≤m} c_k`. Mechanical once D1 settled.

**D3 (slab/time-shift).** Bernstein measures `t` from slab start; approaching `ω` uses sub-slabs
`[t₁,ω)`. Reparametrize `D` or apply `estimate_div` on shifted slabs. Mechanical.

**D4 (dim-3).** Add `hdim : finrank E = 3` (or per-point) to the target. Acceptable: `ham3_main`/
`extends_of_rmBounded` are dim-3; the whole residual stack is dim-3 (Uhlenbeck KN).

---

## 6. Running status

- **2026-07-14 — the standing-input frontier is discharged.**
  `resStarSol` is focused-check and targeted-build green. It combines `tailTowerData` with
  `rm04Base_of_sol`, so `hbase`, `hrm`, `hchr`, `hchrId`, and `hswap` are no longer assumptions or
  DeTurck black boxes. `bbsAllMBounds` itself remains an unproved theorem (0%): C1 still needs the
  local-frame adapter, a pointwise norm-heat interface, and scalar derivative/Laplacian realizations;
  C2 then needs the Bernstein time-slab assembly. C3 remains the separate hard smooth-limit problem.
- **2026-06-13 (this session) — D1 = (b) “one precise frontier sorry” (user-chosen); EXECUTED.**
  Read the full interface (§1) + standing-input ledger (§3); surfaced D1; user chose the clean public
  signature with the DeTurck-gated content localized to named frontier sorries.  `BBSLimitProducer.lean`
  authored + GREEN (`lake-locked check`, exit 0):
  - `bbsAllMBounds` (theorem, `Prop`) — **frontier sorry** localizing bricks **C1+C2** (the
    DeTurck-gated all-`m` Bernstein–Bando–Shi bound).  Obstruction = the irreducible DeTurck
    time-regularity standing inputs `hbase`/`hswap` + metric-frame boxes carried by `resStarBoundLF`
    (§3) — not derivable from `IsSolutionOn`; the coworker's lane.
  - `cinftyLimitData_of_allMBounds` (`def`, `Type`) — **frontier sorry** localizing brick **C3** (the
    limit-extraction analysis).  Obstruction = **G3** (smooth-limit-metric constructor from chart-Gram
    `C⁰` limits + uniform `Cᵐ` bounds — missing infrastructure; nothing fills `CinftyLimitData`) and
    **G4** (`ricci_match` via Arzelà–Ascoli / equicontinuity on chart-Gram and its `≤2` derivatives —
    likely needs Sobolev/interpolation infra not yet present).
  - `cinftyLimitData_of_solution` (`def`) — **sorry-free composition** of the two above.  The dim-3
    target uses `hdim : Module.finrank ℝ E = 3` (D4) and the intrinsic curvature bound on
    `nablaKRm04NormSqIntrinsic S 0` via the realizing `Rm04`; `hRm`/`hbound` are the unfolded
    `MaximalTime` predicates (defeq), so no import of `MaximalTime` (no cycle).
  - **`hLimit` WIRED.**  `MaximalTime.lean:173` `extends_of_rmBounded` now calls
    `cinftyLimitData_of_solution` instead of `sorry`; `hdim` threaded through the contained cascade
    (`extends_of_rmBounded` → `rmUnbounded_of_maximal` → `formsSing_of_maximal[_metric]`, all
    MaximalTime-local; downstream references are comment-only).  MaximalTime build GREEN (exit 0,
    9465 jobs).  The old monolithic `hLimit` sorry is replaced by the two precise frontiers above.
- **NOTE — this localizes, it does not eliminate, `sorryAx`.**  `extends_of_rmBounded` still depends on
  `sorryAx` (it always did, via `hleft`/`hglue`/`IsSolutionOn Shat` + now these two frontiers); the
  value is a clean reusable producer interface + two crisp, separately-attackable, documented frontiers
  in place of one opaque sorry.
- **Next bricks (multi-session):** discharge `bbsAllMBounds` once the DeTurck standing inputs land
  (route in §2 C1/C2; banked producers in §4; G1 = smooth local-frame existence still to confirm);
  attack `cinftyLimitData_of_allMBounds` G3/G4 (the genuine analysis — report any missing
  interpolation/Arzelà–Ascoli lemma by name+layer).

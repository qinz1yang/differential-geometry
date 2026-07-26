# MaximalTime — dispatch plan for `extends_of_rmBounded`

## ★ CURRENT STATE (2026-07-04): CLOSED on the interior-restart route — 0 sorry in this file

`extends_of_rmBounded` is **proved with zero `sorry` in `MaximalTime.lean`**, rewired (Y2) onto the
interior-restart + forward-uniqueness route. Real-build axiom list:
`[propext, sorryAx, Classical.choice, Quot.sound]`, with `sorryAx` tracing to exactly the THREE
cited PDE black boxes:

1. **(N)** `ricci_flow_unif_existence` (`Evolution/ExtendViaUniqueness.lean`) — uniform short-time
   existence under bounded geometry (parabolic continuous dependence; verified non-circular).
2. **(B)** `ricci_flow_forward_unique` (same file) — forward uniqueness, smooth class (GSM77 Ch. 7 §5.2).
3. `shiCovBound_of_soln` (`ExtendShiInputs.lean`) — Shi-type covariant tail bounds
   (GSM77 Ch. 7; discharge plan = `ExtendShiInputs.md` §SHI DISCHARGE PLAN).

Proof chain: `ricciFlowPDE_Ici_of_soln` → `ric_quad_le_of_soln` (hric) → `extendInputs_of_soln`
→ (A) `ricci_flow_interior_restart` (proved from (N)) → (B) on `g_fam` vs `rr(·−t*)` →
`extend_construction_of_restart` (Brick U) → `isSolutionOn_of_extendData`. Route documentation:
`Evolution/ExtendViaUniqueness.md`, `ExtendShiInputs.md`.

**The old restart-at-ω + C∞-glue route below is HISTORICAL** — `hleft`/`hLimit`/`hglue` and the
`ricci_flow_extends_construction` call no longer exist in the proof; `CinftyLimitData`,
`restart_short_time` (Gate-R), and `BBSLimitProducer` are dead code off every critical path (marked
in their files). Everything from here down is kept as the historical dispatch record.

---

End goal: discharge `extends_of_rmBounded` (`MaximalTime.lean:153`), the BBS/long-time
pillar of Hamilton 3D (`ham3_main`). Short-time existence is the collaborator's lane
(`ricci_flow_short_time_existence`, proven modulo the single DeTurck `sorry`); assume/cite,
do not build.

## Historical state (2026-06-13, superseded)

`extends_of_rmBounded` has a **complete proof skeleton**: it calls the banked
`ricci_flow_extends_construction` (`Evolution/CinftyLimitGlue.lean:632`) with 4 sorry'd
inputs, then wraps the raw metric output into `ExtendsPastEndpoint`. The
`SolutionAgreesOn` half is fully proved; `Shat : SolutionOn` is `{ base := { metric := g_ext } }`.

Section variables now carry `InnerProductSpace ℝ E`, `NeZero (Module.finrank ℝ E)`,
`CompactSpace M`, `BoundarylessManifold I M`, `I.Boundaryless` (needed by CinftyLimitGlue).
Consumers (`rmUnbounded_of_maximal`, `formsSing_of_maximal`, `formsSing_of_maximal_metric`)
updated. `HamiltonPositiveRicci.lean` verified green (references only in comments).

### The 4 sorry's

| # | `have` | line | what | dispatch |
|---|--------|------|------|----------|
| 1 | `hleft` | ~164 | PDE on `[α,ω)` in `Set.Ici α` form | **Dispatch A** (small) |
| 2 | `hLimit` | ~171 | `CinftyLimitData` from BBS all-m bounds | **Dispatch C** (the math core) |
| 3 | `hglue` | ~175 | smooth glue across the `ω` seam | **DEFERRED** (collaborator/DeTurck) |
| 4 | `IsSolutionOn Shat` | ~195 | regularity wrapping of `g_ext` | **Dispatch B** (mechanical) |

All four are independent `have`s. The dispatch pattern (per CLAUDE.md "lowest suitable
module"): **extract each sorry'd `have` into its own named theorem in the right file,
prove it there, then call it from `MaximalTime.lean`.** Do not prove them inline.

Recommended order: **A → B → C**. A and B fully realize the plumbing (quick/mechanical);
C is the multi-session mathematical core. Sorry 3 stays a `sorry` until the collaborator's
DeTurck regularity lands.

---

## Dispatch A — `hleft`: Ricci-flow PDE in `Set.Ici α` form (SMALL)

**Target lemma** (place in `MaximalTime.lean`, just above `extends_of_rmBounded`, or in a
`Basic/` helper if it generalizes):

```lean
theorem ricciFlowPDE_Ici_of_solution
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (… .closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ Set.Ico alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * Integral.Connection.ricciTensor (I := I) (S.base.metric t) x v w)
        (Set.Ici alpha) t
```

**What's available.** `hS.equation : MetricVariationEquationOn S.family (…ricciAt)`
(`Realized/RicciFlow.lean:112`) gives, for every `t : RegularTime D` (= `t ∈ Ioo α ω`),
`HasDerivWithinAt (fun s => (g s).inner x X Y) ((-2)·Ric t x X Y) D.carrier t`, where
`D.carrier = Ico α ω` (`TimeInterval.lean:283`).

**Route.**
- Identify the Ricci values: `Integral.Connection.ricciTensor (g t) x v w` vs the equation's
  `RicciAtFamily.toTensorField S.ricciAt t x v w`. Find/prove the bridge simp lemma
  (`ricci_apply`, `ricciAt`, `metricRicci…` in `Basic/Core.lean:262,267`).
- **Interior** `t ∈ Ioo α ω`: `Ico α ω ∈ 𝓝 t` (`regular_mem_nhds`) and `Ici α ∈ 𝓝 t`
  (since `t > α`). So `HasDerivWithinAt … (Ico α ω) t ⟺ HasDerivAt … t ⟺
  HasDerivWithinAt … (Ici α) t` via `hasDerivWithinAt_iff_hasDerivAt` /
  `HasDerivAt.hasDerivWithinAt`. Mechanical.
- **Left endpoint** `t = α`: THIS IS THE GAP. `α ∉ regular`, so `hS.equation` gives nothing
  at `α`. Need the right-sided derivative `HasDerivWithinAt … (Ici α) α`.
  - `Ico α ω ∈ 𝓝[≥] α` (`= Ici α ∩ Iio ω`, `Iio ω ∈ 𝓝 α`), so it suffices to get
    `HasDerivWithinAt … (Ico α ω) α`, i.e. the PDE at the carrier point `α`.
  - `IsSolutionOn` does NOT state the PDE at the initial time. Two honest options:
    (a) **Derive by continuity of the derivative**: the derivative on `Ioo α ω` is
        `−2·Ric(g_t)`, which → `−2·Ric(g_α)` as `t → α⁺` by `hS.ricciCont` (continuity up
        to the carrier). Use a Mathlib "derivative continuous up to the endpoint ⟹ one-sided
        derivative at the endpoint" lemma (search `HasDerivWithinAt` + `Ici`/`tendsto` +
        `hasDerivWithinAt_of_tendsto…`, or `image_le_of…`/MVT-extension family). Needs
        continuity of `s ↦ (g s).inner x v w` on `Ico α ω` (from `hS.smoothMetric` /
        chart-Gram continuity) + the derivative limit.
    (b) **Add an `equationInitial` field to `IsSolutionOn`** (`Basic/Core.lean:508`) for the
        right-derivative at `D.initial`. Cleaner but touches the structure and all its
        constructors — only if (a) stalls.

**Risk/decision.** The `t = α` case is the only real content. If route (a) needs a Mathlib
lemma that does not exist in the needed form, STOP and report — the choice between (a) and (b)
is a design decision for the user. Everything else is mechanical.

**Verify.** `./scripts/lake-locked.ps1 check -Files DifferentialGeometry/Geometry/Flow/RicciFlow/MaximalTime.lean`
(plus the helper's file if separate). Then replace the `hleft` sorry with the lemma call.

---

## Dispatch B — `IsSolutionOn Shat`: regularity wrapping (MECHANICAL, larger)

> ⚠️ **2026-06-13 SUPERSEDED — read "Dispatch B execution findings" at the BOTTOM of this
> file FIRST.** The premise below ("a `chartGram → IsSolutionOn` builder already exists;
> reuse it on the shifted interval") is FALSE. The would-be builder is `ham3_short_isSolution`
> and it is itself a `sorry`; the field-by-field assembly was never finished. Worse, the task
> bottoms out on a foundational field-design blocker (`MetricFamilySmoothOn.frameCompSmooth`
> is unconstructible as stated). Dispatch B is NOT mechanical and needs a user decision.

**Target lemma** (place in `Evolution/CinftyLimitGlue.lean`, below
`ricci_flow_extends_construction`, since it consumes that theorem's output shape; or a new
`Evolution/ExtendedSolutionRegularity.lean`):

Given the raw output of `ricci_flow_extends_construction` — for `g_ext : ℝ → SmoothRiemannianMetric I M`:
chart-Gram `C∞` on `Ioo α (ω+ε) ×ˢ baseSet`, chart-Gram `ContinuousOn` on `Ico α (ω+ε) ×ˢ baseSet`,
and `HasDerivWithinAt …(−2 Ric)… (Set.Ici α)` on `Ico α (ω+ε)` — build
`IsSolutionOn (I := I) ({ base := { metric := g_ext } } : SolutionOn … (.closedOpen α (ω+ε) hwide))`.

**Fields to produce** (`IsSolutionOn`, `Basic/Core.lean:508-552`): `smoothMetric`,
`smoothConnection`, `equation`, `scalarCont`, `scalarTime`, `ricciCont`, `rm04Cont`,
`nablaRicCont`, `ricciNormSpace`, `ricciNormGrad`.

**Route.**
- `equation` (`MetricVariationEquationOn`, regular times = `Ioo α (ω+ε)`): restrict `hpde`
  from `Ico`/`Ici α` to regular times — at interior `t`, same `HasDerivAt` bridge as Dispatch A
  (here it's *easier*: no endpoint case, regular times are interior). Plus the
  `ricciTensor`↔`ricciAt.toTensorField` value bridge (reuse Dispatch A's).
- `smoothMetric` (`MetricFamilySmoothOn`): chart-Gram `C∞` on the interior + carrier
  continuity is exactly the `hsmooth`/`hcont` output. Find the constructor/iff for
  `MetricFamilySmoothOn` from chart-Gram data (`grep MetricFamilySmoothOn` in
  `Geometry/Curvature/Realized/` and `Integration/`; the existing solution already proves
  this direction somewhere — `ricci_flow_short_time_existence`'s consumers build a SolutionOn,
  so the chart-Gram→smoothMetric bridge likely exists. REUSE it).
- `smoothConnection`, `ricciCont`, `rm04Cont`, `nablaRicCont`, `ricciNormSpace`,
  `ricciNormGrad`, `scalarCont`, `scalarTime`: all are `≤k`-order differential expressions in
  the metric, so they follow from `smoothMetric` (interior `C∞`) + carrier continuity. Look
  for how the EXISTING short-time `SolutionOn`/`IsSolutionOn` is assembled (grep for
  `IsSolutionOn.mk` / `⟨…⟩ : IsSolutionOn` / the file that turns `ricci_flow_short_time_existence`
  into an `IsSolutionOn`). If that assembly exists, this dispatch is mostly "apply the same
  builders to `g_ext` on the shifted interval."

**Key search first.** Before writing anything, find whether a `chartGram C∞ → IsSolutionOn`
builder already exists (it very likely does, used to certify the short-time solution). If yes,
this collapses to reusing it. Record the finding in this note.

**Risk.** Larger surface but no new mathematics. If a specific field's builder is genuinely
missing (e.g. `nablaRicCont` from chart-Gram), report that one missing builder as the frontier.

**Verify.** Same `lake-locked check` on the helper's file, then `MaximalTime.lean`.

---

## Dispatch C — `hLimit`: `CinftyLimitData` from BBS all-m bounds (THE MATH CORE, multi-session)

**This is the gating sorry.** It is itself a 3-brick chain (old Leaves A/B/C). Give it an
independent session; first read this note + `Evolution/StarSum/TowerProducer.md` (endgame map)
+ memory `bbs-allk-route-status.md`. Produce a `BBSLimitProducer.md` plan, then execute brick
by brick. Target file: new `Evolution/BBSLimitProducer.lean`.

**Target lemma:**

```lean
theorem cinftyLimitData_of_solution
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (… .closedOpen alpha omega hαω)}
    {Rm04 : Real → … .Tensor04Section (I := I) (M := M)}
    (hS : IsSolutionOn (I := I) S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    (hbound : Rm04NormSqBoundedAt (I := I) S Rm04) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω
```

(Fields: `limitMetric`, `tendsto_left` chart-Gram convergence, `ricci_match` —
`CinftyLimitGlue.lean:211`.)

### Brick C1 — `∀ k, TowerHeatBoundOn` from `IsSolutionOn` (analytic plumbing)
The tensor-algebra core is DONE in `Evolution/StarSum/TowerProducer.lean` (steps 1–3, GREEN):
`nablaKReaction_le` (intrinsic reaction ≤ `towerReactionSum`) and `towerHeatBoundOn_of_heatReact`
(heat-eq + reaction bound → `TowerHeatBoundOn`). C1 = feed them real inputs:
- For each `k`, `(t,x)`: pick a `g_t`-orthonormal basis at `(t,x)`.
- Instantiate `nablaKRm04NormHeatEquationOn_intrinsic` (`Evolution/IteratedRmTowerHeatEq.lean:185`)
  with `IsSolutionOn`'s regularity data → `NablaRm04NormHeatEquationOn`. SUB-NEEDS: construct
  its `Xb, du, normSecond, nablaKRmNormLap, Tdot` + 7 regularity hyps from `hS`; `hT` from
  `resStarLFU`/`resStarBoundLF` (`Evolution/StarSum/TowerHeat.lean`, `TimeRecursion.lean`);
  `hRic` from the Ricci-trace-Rm bridge.
- Apply `nablaKReaction_le` at the orthonormal frame (`gInv = δ`) and
  `towerHeatBoundOn_of_heatReact`. (Pointwise-in-`(t,x)`: see the basis subtlety note in
  TowerProducer.md — heat-eq wants `∂ₜgInv = 2gInv²ric`, collapse wants `gInv t = δ`;
  compatible only for a basis orthonormal AT that `t`.)
- CLASSIFICATION: analytic regularity plumbing, not tensor algebra.

### Brick C2 — `BernsteinTower` → all-m bounds (mechanical)
`TowerHeatBoundOn` (C1) + regularity fields (`hw_cont, hw_space, hw_grad, hLap` from `hS`) +
curvature bound (from `hbound`) + a time bound → build `BernsteinTower`
(`Evolution/BernsteinShiHigher.lean:493`); then `BernsteinTower.estimate_div`
(`:1311`) gives `‖∇ᵐRm‖² ≤ (towerConst …)²·K²/tᵐ` for all `m`.

### Brick C3 — all-m bounds → `CinftyLimitData` (HARD analysis)
- `limitMetric`: the `C⁰` chart-Gram limit as `t → ω⁻`. The Stage-1 engine is banked in
  `CinftyLimitGlue.lean` (`chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv` and the Cauchy-limit
  lemmas at `:94+`). The `m=0` curvature bound (`|∂ₜg| = 2|Ric| ≤ C|Rm| ≤ CK`) drives `tendsto_left`.
- `ricci_match`: Ricci continuity across `ω` from the `m≤2` bounds (Arzelà–Ascoli on chart-Gram
  components / equicontinuity). MAY need Sobolev/interpolation infrastructure not yet present —
  if so, report the missing analysis lemma as the frontier.
- CLASSIFICATION: the genuinely hard analytical piece.

**Stop conditions.** Per brick: 3 different routes fail, or a real missing API / wrong
statement / design choice / mathematical obstruction. C3 is the most likely to surface a
missing-infrastructure frontier — report it precisely (which Arzelà–Ascoli / interpolation
lemma, in which layer) rather than faking it.

**Verify.** `lake-locked check` on `BBSLimitProducer.lean`, then wire into `MaximalTime.lean`.

---

## Sorry 3 — `hglue`: DEFERRED (collaborator/DeTurck)

`CinftyGlueData` (`CinftyLimitGlue.lean:567`: `gram_smooth, gram_cont, metric_match`) has NO
banked producer. `gram_smooth/gram_cont` require the glued family to be jointly `C∞`/`C⁰`
ACROSS the `ω` seam — i.e. the restart (from `ricci_flow_short_time_existence`) matches the
limit metric to the regularity the parabolic smoothing provides. That smoothing is exactly the
DeTurck content carried as the single `sorry` in
`deturck_ricci_flow_parabolic_short_time_existence` (`ShortTime/DeTurckRicciPde.lean:128`).
`metric_match` alone is derivable from `hLimit.tendsto_left`. Keep `hglue` as a `sorry` (or a
clearly-labelled standing input) until the collaborator's DeTurck regularity lands; do not
fabricate it.

## 2026-06-13 EXECUTOR — Dispatch A (`hleft`): STOP, blocker is the `metricRicciAt↔ricciTensor` bridge

Investigated; did NOT edit `MaximalTime.lean`. The blocker is NOT the `t = α` analysis (that is
already solved), but the Ricci bridge that `hleft` needs at EVERY `t`.

### The `t = α` analytic case is already done (route (a) does not stall)

`ShortTimeAssembly/RicciFlowPdeAtZero.lean` has `ricci_flow_pde_at_zero` (abstract, `g_fam`-level):
from `h_cont` (metric continuity on `Ico 0 T`), `h_ric_cont` (`ContinuousWithinAt (-2·ricciTensor (g_fam ·) x v w) (Ioi 0) 0`),
and `h_interior` (interior `HasDerivWithinAt … (Ici 0)`), it produces the boundary right-derivative
`HasDerivWithinAt … (-2·ricciTensor (g_fam 0) x v w) (Ici 0) 0`, via Mathlib's
`hasDerivWithinAt_Ici_of_tendsto_deriv` (Calculus/FDeriv/Extend.lean) + `interior_ici_deriv_to_ordinary`.
A general-`α` analog is the same short proof. So route (a) is feasible; the prompt's flagged risk
(deriving-by-continuity vs `equationInitial`) does NOT bite — `equationInitial` is not needed.

### The actual blocker: `S.ricci (= metricRicciAt) ↔ ricciTensor`

`hS.equation` (`MetricVariationEquationOn`) gives, at every `RegularTime` (`Ioo α ω`):
`HasDerivWithinAt (fun s => (g_fam s).inner x X Y) (-2 · RicciAtFamily.toTensorField S.ricciAt t x X Y) (Ico α ω) t`,
and `RicciAtFamily.toTensorField S.ricciAt t x X Y = S.ricciAt t x (vec2 X Y) = metricRicciAt (g_fam t) x (vec2 X Y)`
(`toTensorField_apply`, `SolutionOn.ricciAt_eq`, `SolutionFamily.ricciAt`).
The `hleft` goal needs `-2 · ricciTensor (g_fam t) x v w`.  `ricciTensor g x v w` is the **stitched-
LeviCivita** Ricci (`RicciConnection.lean:221`, trace of `riemannOp (LeviCivita g)`), NOT defeq to
`metricRicciAt` (the metricCov/Koszul Ricci). The only bridge is
`metricRicciAt_apply_eq_ricciTensor` (`Geometry/Curvature/MetricLeviCivitaReconcile.lean:165`):
`metricRicciAt g x (vec2 v w) = ricciTensor g x v w`, but it REQUIRES
`hcov₂ : ContMDiffCovariantDerivativeLocally (LeviCivita g) ∞`.

**No producer for `ContMDiffCovariantDerivativeLocally (LeviCivita g) ∞` exists.** Confirmed:
- the global instance `LeviCivita_isContMDiff` (`LeviCivita/Defs.lean:347`) gives only the GLOBAL
  `ContMDiffCovariantDerivative`; the codebase's own `Connection/Smooth.lean:22-37` doc states the
  global form does NOT imply the Locally form (no bump-extension for generic scalar fields).
- `metricCov_smooth` / `leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally` give the
  Locally form only for `metricCov g = leviCivitaConnectionOfMetric g` (Koszul), which is a
  STRUCTURALLY DIFFERENT connection from the stitched `LeviCivita g` — `LeviCivita/Reconcile.lean:23`
  explicitly: "Structure-level equality `LeviCivita g = leviCivitaConnectionOfMetric g` is not expected".
- the solution provides (via `connSmoothOfSol`) `…Locally (S.family.connection t) ∞` =
  `…Locally (leviCivitaConnectionOfMetric (g_fam t)) ∞` — again the Koszul one, not stitched.

So the bridge cannot be discharged from anything currently available.

### Design decision for the user (pick one)

(A) **Add a producer** `ContMDiffCovariantDerivativeLocally (LeviCivita g) ∞` for smooth metrics
   (LeviCivita layer; likely from `LeviCivita_section_contMDiffOn_univ` restricted to opens + chart
   connection-endomorphism smoothness). Then `hleft` = bridge (per `t`) + `ricci_flow_pde_at_zero`
   (general-α analog) + the mechanical interior `Ico→Ici` HasDerivAt step. RECOMMENDED if provable.
(B) **Prove the solution-level bridge** `metricRicciAt (g_fam t) x (vec2 v w) = ricciTensor (g_fam t) x v w`
   via the CHART route (reuse `ShortTimeAssembly/RicciContinuityInMetricTime.lean`, which already builds
   `ricciTensor (g_DT ·)` continuity from chart Gram iteratedFDeriv), avoiding the LeviCivita-Locally
   reconcile. Heavier.
(C) **Restate** `hleft`/`ricci_flow_extends_construction` to consume `metricRicciAt`/`S.ricci` instead
   of `ricciTensor` (then `hS.equation` feeds it directly, no bridge). Changes the banked construction's
   interface — only if (A)/(B) are undesirable.

### Banked pieces ready once the bridge is available
`ricci_flow_pde_at_zero` (t=α), `hasDerivWithinAt_Ici_of_tendsto_deriv` (Mathlib), `hS.ricciCont`
(`Tensor0SFamilyContinuousOnSet 2 D.carrier (S.ricci)` → for `h_ric_cont` after the bridge + section-
eval continuity), `toTensorField_apply`/`ricci_apply`/`ricciAt_eq` (the algebraic half of the bridge),
`SolutionOn.family_metric` (`g_fam = S.family.metric`, rfl). Interior: `regular_mem_nhds` +
`hasDerivWithinAt_iff_hasDerivAt` + `HasDerivAt.hasDerivWithinAt`.

## 2026-06-13 EXECUTOR — Dispatch B (`IsSolutionOn Shat`): STOP. Mis-scoped + foundational field blocker

Investigated thoroughly; did NOT edit `MaximalTime.lean` (made only this note + the ⚠️ pointer on
the Dispatch B header). The plan's premise — "a `chartGram → IsSolutionOn` builder already exists,
reuse it on the shifted interval; mechanical" — is FALSE. Two independent problems.

### Problem 1 — the builder does NOT exist; it is the UNBUILT `ham3_short_isSolution`
The only `chartGram → IsSolutionOn` assembler in tree is
`DimensionThree/HamiltonPositiveRicci.lean:554 ham3_short_isSolution`, and its proof is a `sorry`
(line ~571). Its own docstring concedes the raw chart-Gram data "pins only the 1st time derivative
and the open-interval smoothness." The field-by-field assembly was scoped (see
`HamiltonPositiveRicci.md` 2026-06-13 sections) but only the FIRST brick is done:

DONE infrastructure (reusable, verified, no sorry):
- `metricTensorCont_of_chartGram` (`Curvature/Realized/MetricFamilyContinuity.lean:176`) — builds
  the `metricTensor_cont` field from joint chart-Gram C⁰; generic in the time set `K`.
- `tensor0SFamilyContinuousOnSet_of_chartComp` / `…_of_chartBasisComp` (same file) — Keystone A,
  the component→section bundle-continuity constructor.
- `metricCLMSection_jointContMDiffOn_of_chartGram` (`ShortTimeFlow/ConjugatingFlowProperties.lean:3570`)
  — a GENERIC smooth keystone: chart-Gram C∞ on `Ioo 0 T ×ˢ baseSet` → joint `ContMDiffOn` of the
  metric bilinear-CLM bundle section on `Ioo 0 T ×ˢ univ`. Hardcoded to `(0,T)`; would need interval
  generalization (free) or a time-shift to serve `(α, ω+ε)`.
- curvature joint `(t,x)` continuity: `chartRicci_jointContinuousOn`, `chartRiemann_jointContinuousOn`,
  `ricciChartFrameComp_jointContinuousOn` (`ShortTimeAssembly/RicciContinuityInMetricTime.lean`,
  generic in the metric family) + the two-LC reconciliation (`Connection/LeviCivita/Reconcile.lean`).
- `contMDiff_section_apply_gen` (`Tensor/Multilinear/BundleSmoothEvalRealized.lean:691`) — eval a
  smooth section against smooth frame fields.

NOT done (the rest of the 10 fields):
- the chart-Gram-`ContMDiffOn` → `iteratedFDeriv (chartGramOnE)` joint-jet bridge (HamiltonPositiveRicci.md
  step (a)) that feeds `jointRicci/Riemann_continuousOn` — "the only genuinely short-time-coupled,
  fiddly step";
- `ricciCont`/`rm04Cont`/`scalarCont`/`nablaRicCont` assembly on top of it;
- `equation` (needs the SAME `metricRicciAt↔ricciTensor` bridge that blocks Dispatch A — see above);
- `smoothConnection`, `scalarTime`, `ricciNormSpace`, `ricciNormGrad` (fixed-time; constructible but
  unbuilt as generic-from-`SmoothRiemannianMetric` lemmas);
- a Dispatch-B-ONLY extra: the carrier-continuity curvature fields are on `Ico α (ω+ε)` (closed at α);
  raw data gives only joint *metric* C⁰ up to α, not joint *curvature* C⁰. The up-to-α curvature
  continuity must be glued from `_hS` (which supplies `ricciCont`/`rm04Cont`/`scalarCont` on `[α,ω)`,
  and `g_ext = g_fam` there) with the interior continuity on `(α, ω+ε)`. The union
  `Ico α (ω+ε) = Ico α ω ∪ Ioo α (ω+ε)` has both pieces RELATIVELY OPEN in the carrier, so a
  `Tensor0SFamilyContinuousOnSet` "union-gluing" lemma (inverse of the existing `.mono`) closes it.
  That gluing lemma is clean/self-contained but not yet written; it is NOT in `ham3_short_isSolution`'s
  plan (that route recenters into the open interior to dodge t=0; Dispatch B canNOT recenter — it must
  certify the literal `[α, ω+ε)` solution for `ExtendsPastEndpoint`).

### Problem 2 — FOUNDATIONAL BLOCKER: `MetricFamilySmoothOn.frameCompSmooth` is unconstructible as stated
`MetricFamily.lean:495` field `frameCompSmooth` reads: for EVERY `IsLocalFrameOn I E 1 frame u`
(i.e. a merely **C¹** frame — Mathlib `IsLocalFrameOn _ _ k`: each section is `Cᵏ`), and all `i j`,
`(g p.1).inner p.2 (frame i p.2)(frame j p.2)` is jointly **C∞** (`⊤`) on `D.regular ×ˢ u`.

This universally-quantified statement is FALSE for arbitrary C¹ frames, for ANY metric: pick a
C¹-not-C² frame, then `g(frame_i, frame_j)` is C¹-not-C². (Concretely on `M = ℝ`, `g` standard,
`frame(x) = (1+|x|^{3/2})∂_x`: output `(1+|x|^{3/2})²` is C¹ not C².) So no theorem — not chart-Gram
data, not the short-time PDE, nothing — can CONSTRUCT this field. It is consumable-but-not-constructible:
`_hS.smoothMetric.frameCompSmooth` (an ASSUMED field of the input hypothesis) happily hands consumers
C∞ output, which is why downstream code (`Basic/Core.lean:816`, `Evolution/Metric/Basic.lean:88`,
`ParabolicRescaling.lean:463`, `HCGCompactness/MetricCovDerivTimeDeriv.lean:619`) works — they all
pass C∞ trivialization frames `e.localFrame b`. But producing a fresh `MetricFamilySmoothOn` (what
sorry #4 AND `ham3_short_isSolution` BOTH need) requires inhabiting `frameCompSmooth`, which is
impossible. This is the real reason `ham3_short_isSolution` has never been filled.

`frameCompSmooth` is the UNIQUE structurally-impossible field; every other field is constructible (the
other 9 are continuity / fixed-time / interior-C∞ statements, just laborious).

CLASSIFICATION: design obstruction (over-strong public structure field), NOT local proof search.
SMALLEST HONEST FIX (a user DESIGN DECISION — touches the foundational `MetricFamilySmoothOn` structure
and its consumers, so requires approval per CLAUDE.md): strengthen the field's frame hypothesis from
`IsLocalFrameOn I E 1` to `IsLocalFrameOn I E ⊤` (C∞). Then `(g·)(frame i)(frame j)` = a finite
`Σ cᵏᵢ cˡⱼ · chartGram` of jointly-C∞ factors → C∞, constructible from chart-Gram C∞. Caveat: some
consumers BUILD `IsLocalFrameOn I E 1` frames explicitly (`Regularity.lean:323`,
`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean:378,831`); they would need to build `⊤`-frames
(their underlying `e.localFrame b` is genuinely C∞, so this is mechanical but non-zero churn).

### Verdict / scope
sorry #4 is NOT dischargeable this pass. It is a multi-brick, multi-session assembly (comparable in
ENGINEERING effort to Dispatch C, though "assembly" not "hard analysis"), gated FIRST on the
`frameCompSmooth` design decision. No fundamental math wall (every constructible field is feasible;
the user's "recenter" insight + the existing curvature-continuity machinery make the analysis routine),
but the plan's "mechanical, reuse existing builder" framing is wrong.

Honest project placement: of the 10 `IsSolutionOn` fields, 1 (`metricTensor_cont`) has a ready generic
builder, ~4 (the curvature/`equation` fields) have most of their machinery built but need the jet-bridge
+ `metricRicciAt↔ricciTensor` bridge + assembly, ~4 (fixed-time) are easy-but-unwritten, and 1
(`frameCompSmooth`) is unconstructible pending a structure redesign. Call sorry #4 itself ~10–15% done
(only `metricTensor_cont` is turnkey); its dedicated machinery ~50% (Keystone A + smooth keystone +
curvature joint-continuity lemmas exist). This is one of 4 sorrys in `extends_of_rmBounded`, which is
the BBS/long-time pillar of `ham3_main`; the whole HCG/Hamilton-3D endgame remains a multi-month frontier.

NEXT (after the user decides on `frameCompSmooth`):
1. [design] approve+apply the `frameCompSmooth` frame-hypothesis strengthening (or decide to keep
   sorry #4 as a documented frontier).
2. [if approved] write the generic `metricFamilySmoothOn_of_chartGram` builder (smooth keystone +
   `metricTensorCont_of_chartGram` + the C∞-frame eval) → discharges `smoothMetric`.
3. write the `Tensor0SFamilyContinuousOnSet` union-gluing lemma (cross-α primitive, in `MetricFamily.lean`).
4. resolve the `metricRicciAt↔ricciTensor` bridge (shared with Dispatch A) → `equation` + curvature fields.
5. assemble all 10 fields into `isSolutionOn_of_extendData` (new `Evolution/ExtendedSolutionRegularity.lean`),
   call it from `MaximalTime.lean:195`.

## 2026-06-14 — BOTH RECORDED BLOCKERS RESOLVED by the curvature/foundation refactor

Re-audit of `extends_of_rmBounded`. Current sorries are now **3** (Dispatch C / `hLimit` is DONE —
`MaximalTime.lean:173` `hLimit := cinftyLimitData_of_solution …`, no sorry): `hleft` (line 171),
`hglue` (line 186, DeTurck — stays), `IsSolutionOn Shat` (line 198).

**The two interface walls recorded above are GONE** (dissolved by the 2026-06-13/14 refactor sessions,
NOT by new PDE work):

- **Dispatch A's blocker is resolved.** `metricRicciAt_apply_eq_ricciTensor`
  (`Geometry/Curvature/MetricLeviCivitaReconcile.lean:163`) is now **hypothesis-free** — it no longer
  needs `ContMDiffCovariantDerivativeLocally (LeviCivita g) ∞`; it supplies the producer internally via
  `leviCivita_contMDiffCovariantDerivativeLocally` (the LeviCivita→Koszul Stage-1 collapse). So the
  `metricRicciAt ↔ ricciTensor` value-bridge that `hleft` needs at every `t` is now freely available.
  Combined with the already-banked t=α lemma (`ricci_flow_pde_at_zero`) and the mechanical interior
  `Ico→Ici` `HasDerivAt` step, **`hleft` is now fully dischargeable** following the Dispatch-A "banked
  pieces" recipe above. (Bonus: bucket-A also added `metricRm13At_eq_riemannCurvatureAt` /
  `metricRm04At_eq_riemannCurvature04At` for the Rm-level analogs.)

- **Dispatch B's foundational blocker is resolved.** `MetricFamilySmoothOn.frameCompSmooth`
  (`Curvature/Realized/MetricFamily.lean`) was strengthened from `IsLocalFrameOn I E 1` (C¹) to
  `IsLocalFrameOn I E (∞ : WithTop ℕ∞)` (C∞) — the "smallest honest fix" flagged above was applied and
  the whole tree is green. So `MetricFamilySmoothOn` is now **constructible** from chart-Gram C∞ data,
  unblocking the `smoothMetric` field (and `ham3_short_isSolution`). The remaining Dispatch-B work is the
  (laborious but math-free) 10-field assembly + the cross-α `Tensor0SFamilyContinuousOnSet` union-gluing
  lemma — no design wall left.

**Revised dispatch state:** `hleft` = SMALL, now unblocked (do first). `IsSolutionOn Shat` = MEDIUM
assembly, now unblocked (no design decision pending). `hglue` = the ONLY genuine remaining frontier
(collaborator's DeTurck short-time regularity). Net: once `hleft` + `IsSolutionOn Shat` land,
`extends_of_rmBounded` drops to a SINGLE `sorry` (DeTurck), which honestly reflects that the only missing
mathematics is the collaborator's short-time-existence regularity.

**Statement is correct** (audited): hypotheses (`IsSolutionOn` + bounded realizing `Rm04`, dim 3) and
conclusion (`ExtendsPastEndpoint` = a genuine `IsSolutionOn` extension agreeing on `[α,ω)`) are the right
BBS extension theorem. The "not proving what we should" feeling was the unwired interfaces (the proof
sorried `hleft`/`IsSolutionOn Shat` instead of extracting them from `_hS`/the construction outputs) — now
both are extractable.

## 2026-06-14 EXECUTOR — `hleft` DISCHARGED ✅ (sorries 3 → 2)

Dispatch A done. `extends_of_rmBounded`'s `hleft` is now a real proof; verified green (focused
`lake env lean` + targeted build, only the expected `declaration uses sorry` from the remaining 2 leaves).
All in `MaximalTime.lean` (surgical), added above `extends_of_rmBounded`:
- `hasDerivWithinAt_Ici_boundary` (private, generic `f e : ℝ → ℝ`, general endpoint `a < b`): interior
  right-derivatives + boundary continuity of `f` and the value field ⇒ right-derivative at the closed
  endpoint. Rewrite of `ricci_flow_pde_at_zero`'s core (avoids importing the DeTurck-heavy file).
- `tensor2_eval_contOn` (private): scalar `ContinuousOn` of a `(0,2)` tensor time-family evaluated at a
  fixed point/vectors, via `Tensor0SFamilyContinuousOnSet.eval_continuous` (constant base + constant
  vectors ⇒ `hv := continuous_const`, simpler than `coordMetricContOn`).
- `ricciFlowPDE_Ici_of_solution` (private adapter): interior via `metricDerivAt` + `metricRicciAt_apply_eq_ricciTensor`
  (the now-free Ricci bridge); `t = α` via the boundary lemma, fed by `tensor2_eval_contOn` on
  `hS.smoothMetric.metricTensor_cont` (metric cont) and `hS.ricciCont` (ricci cont, bridged to `ricciTensor`).
  `hleft := ricciFlowPDE_Ici_of_solution _hS`.
- Imports added: `Curvature.MetricLeviCivitaReconcile` (bridge) + `Mathlib.Analysis.Calculus.FDeriv.Extend`
  (`hasDerivWithinAt_Ici_of_tendsto_deriv`); plus `open …Integral.Connection`.

GOTCHAS (for the next dispatch): `ω` is a RESERVED Mathlib token — cannot be a binder name (use `a b`).
`Tensor0SSpace`/`metricTensorField_apply` live in `Tensor0SBundle` (NOT `Integral.Connection`) — qualify.
The set-restriction lemma is `ContinuousWithinAt.mono_of_mem_nhdsWithin` (not `mono_of_mem`). `closedOpen`'s
`carrier = Ico`, `regular = Ioo` are `rfl`, so `⟨t, ht⟩ : RegularTime` from `ht : t ∈ Ioo α ω` works directly,
and the `S.ricci ↔ metricRicciAt` reduction is `simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
SolutionFamily.ricciAt]`.

**Remaining in `extends_of_rmBounded`: 2 sorries** — `hglue` (DeTurck, collaborator) and `IsSolutionOn Shat`
(Dispatch B, now design-unblocked). Signature unchanged, so downstream consumers are unaffected (no full
build needed).

## 2026-06-14 — Dispatch B (`IsSolutionOn Shat`) 2h time-box: GATE PASSED, full Shat DEFERRED

Time-boxed attempt (user: 2h, else fall back to refactoring). Outcome: the **decisive feasibility gate
passed** and the key reusable builder is banked; the full `IsSolutionOn Shat` is confirmed multi-session,
so per the checkpoint we fall back. `MaximalTime.lean`'s `IsSolutionOn Shat` sorry is UNTOUCHED (tree green).

**Banked (verified, in NEW `Evolution/ExtendedSolutionRegularity.lean`):**
`metricCLMSection_jointContMDiffOn_of_chartGram_Ioo` — generalizes the `(0,T)`-hardcoded keystone
`metricCLMSection_jointContMDiffOn_of_chartGram` (`ConjugatingFlowProperties.lean:3570`) to ANY open
interval `Ioo a b`, by an affine time-shift (apply the keystone to `g (·+a)` on `Ioo 0 (b-a)`, transport
along `t ↦ t±a` via `ContMDiffOn.comp`; the keystone only used openness, so the shift is clean). This is
the hard core of `smoothMetric.frameCompSmooth`; it proves the linchpin `metricFamilySmoothOn_of_chartGram`
is CONSTRUCTIBLE. **Reusable for BOTH `IsSolutionOn Shat` AND `ham3_short_isSolution`.**

**Remaining (the multi-session tail, NOT done):**
- Finish the linchpin `metricFamilySmoothOn_of_chartGram` (4 fields): `frameCompSmooth` via
  `clm_bundle_apply₂` against the C∞ frame on top of the new `…_Ioo` keystone; `coeff`/`coeff_cont` by
  time-slicing the joint section (`contMDiffOn 𝓘(ℝ,ℝ) ↔ contDiffOn ℝ`, compose with `t ↦ (t,x)`);
  `metricTensor_cont` via `metricTensorCont_of_chartGram` (ready). ~100 laborious-but-mechanical lines.
- The other `IsSolutionOn` fields: `equation` (reuse `ricciFlowPDE_Ici_of_solution`, interior-only),
  `smoothConnection`/`ricciNormSpace`/`ricciNormGrad` (low), `scalarCont`/`scalarTime`/`ricciCont` (via a
  cross-α `Tensor0SFamilyContinuousOnSet` union-gluing primitive, to be written), `nablaRicCont` (medium),
  and **`rm04Cont` — genuinely UNBUILT** (no (0,4)-Riemann carrier-continuity-from-chartGram lemma; the
  single remaining real frontier of Dispatch B, ~adapt the `jointRicci_continuousOn` chain to (0,4)).

**Verdict:** Dispatch B is design-unblocked and now feasibility-proven (gate brick green), but it is a
genuine multi-session assembly whose last frontier is `rm04Cont`. Matches the 2026-06-13 estimate
("multi-brick, ~one BBS brick"). Resume by importing `ExtendedSolutionRegularity.lean` into `MaximalTime`
once the linchpin + `rm04Cont` land.


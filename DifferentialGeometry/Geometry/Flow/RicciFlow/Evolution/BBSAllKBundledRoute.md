# BBS all-`k` reaction: the bundled `StarSum2` route (GPT Pro validated)

**Goal.** Discharge `IteratedRmTowerOn.heatEq` + `IteratedRmTowerOn.starBound` at
every `k` from a `SolutionOn`, then connect `IteratedRmTowerOn → BernsteinShiSolution
→ |∇ᵏRm| ≤ CₖK/t^{k/2} → extends_of_rmBounded`.

This note records the route validated by an external GPT-Pro consultation + a
full grep audit of the tree (2026-06-07). It supersedes the pessimistic footers of
`NablaRiemannCommutator.lean` / `NablaRiemannCommutatorBound.lean` (see "Stale
walls" below).

## The reduction (both fields collapse to ONE thing)

`towerReactionMulti level star k = nablaRmReactionMulti (level k) (star k)
  = Σ_{j∈range(k+1)} 2·Σ_m (∇ᵏRm m)·(star j m)`  (`NablaRiemannHeat.lean:351`).

`abs_nablaRmReactionMulti_le` (`NablaRiemannHeat.lean:367`) already turns
`hstar : ∀ j∈range(k+1), ∀ m, |star j m| ≤ card²·√(w j)·√(w (k−j))` into the eq-7.4
bound. And `nablaKRm04Reaction_orthoBasis_eq_compContract`
(`IteratedRmTowerProducer.lean:434`) gives, in a `g`-orthonormal basis, the actual
reaction `= 2·Σ_m (∇ᵏRm m)·(combinedStarArray m)`,
`combinedStarArray = ricStarArray ric (∇ᵏRm) + comp((∂ₜ−Δ)∇ᵏRm)`.

**So both `heatEq` and `starBound` reduce to: a family `star j` (j=0..k) with**
1. **split**  `Σⱼ star j = combinedStar` (componentwise, ortho frame), and
2. **bound**  `|star j m| ≤ card²·√(w j)·√(w (k−j))`.

No shortcut (`star_0 := combinedStar`, rest 0) works: the cross terms
`∇^{k/2}Rm ∗ ∇^{k/2}Rm` are bounded by `w_{k/2}`, not `√(w_0)√(w_k)`. The genuine
BBS decomposition `(∂ₜ−Δ)∇ᵏRm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm` is required.

## GPT Pro's structural insight (the `StarSum2` class)

- Maximum principle needs only a **norm-level** inequality, NOT an exact tensor
  identity. BUT a bare norm bound cannot be inducted in Lean: the recursion
  contains `∇E_{k-1}` and `|E_{k-1}|≤…` says nothing about `|∇E_{k-1}|`.
- So carry the **structural** middle layer: prove `E_k := (∂ₜ−Δ)∇ᵏRm` is a
  *controlled star-sum* — a finite sum of genuine `∇ᵃRm ∗ ∇ᵇRm` (a+b=k)
  contractions — with closures `.nabla`, `.add`, `.bound`. Weaker than the full
  enumerated tensor identity, stronger than a norm bound; exactly enough for
  Cauchy–Schwarz.
- One-step peeling (NOT the explicit `[Δ,∇ᵏ]` blow-up):
  `E_k = ∇E_{k-1} + (∂ₜΓ)∗T_{k-1} − [Δ,∇]T_{k-1}`,
  `[Δ,∇]S = Rm∗∇S + ∇Rm∗S`, base `E_0 = (∂ₜ−Δ)Rm = Rm∗Rm` (Uhlenbeck).
- Sign corrections to honor: `∂ₜg⁻¹=+2Ric`; `[Δ,∇]` sign by bracket orientation;
  our `Δ‖T‖²=2⟨ΔT,T⟩+2‖∇T‖²` ↔ positive `gⁱʲ∇ᵢ∇ⱼ`, good term `−2|∇T|²`.

## KEY FINDING: the k=1 "wall" was a coordinate-frame artifact

`NablaRiemannCommutator*.lean` did k=1 **component-level in `coordinateFrameAt`**
(the chart frame, NOT orthonormal), and got stuck bounding `∇(Rm∗Rm)` because that
needs `∇g⁻¹=0` raising-commutation which can't be trivialized in a non-orthonormal
frame. The bundled route (do the recursion frame-free via `nabla0SFun_product_eval`,
collapse to an ortho frame only at the end — `nablaKRm04Reaction_orthoBasis_eq_compContract`)
sidesteps this entirely. The footers' "no `∇(Rm∗Rm)` Leibniz / `∇g⁻¹=0` not
statable" claims are STALE: written before `inverseMetricCovDerivForMetricCompInFrame_eq_zero`
(∇g⁻¹=0) and `ContractionLeibniz.lean` existed.

## Grep-verified primitive inventory (2026-06-07)

CONFIRMED in formalism A (`nabla0SFun`/`totalNabla0S`/`Tensor0SField`, where
`nablaKRm04Field` lives):
- `nabla0SFun_product_eval` — tensor-product Leibniz `∇(A⊗B)=∇A·B+A·∇B`
  (`ContractionLeibniz.lean:122`). **Keystone.**
- `nabla_metricPow_zero` — `∇(g^{⊗r})=0` (`ContractionLeibniz.lean:428`);
  `nabla0SFun_metricPow_contraction_eval` (`:480`).
- `inner0S_nabla` — full-contraction Leibniz (`Tensor0SInnerLeibniz.lean:642`).
- `nablaKRm04_ricciIdentityAt` — single commutator `[∇,∇]∇ᵏRm = curvatureAction(rm13)(∇ᵏRm)`,
  ALL k (`RmRealizationBridgeAllK.lean:274`).
- `abs_curvatureAction0SAt_orthoBasis_le` — `|Rm∗T|` CS bound, all s
  (`NablaRiemannT2Bound.lean:230`); `abs_ricStarArray_le` j=0 (`IteratedRmTowerProducer.lean:246`).
- `partialEval0SField`/`nabla_partialEval0S` — slot-freeze + its ∇ rule
  (`Tensor0SBochnerProduct.lean:85,251`).
- `roughLap0STensor` — frame-free rough-Laplacian tensor (`RoughLaplacian.lean:712`).
- `christoffelSymbolTimeDerivativeInFrame` (`Christoffel.lean:208`); `∂ₜg⁻¹`
  `inverse_metric_derivative_solve`; `inverseMetricCovDerivForMetricCompInFrame_eq_zero` (∇g⁻¹=0).
- Consumer `abs_nablaRmReactionMulti_le`; bridge `nablaKRm04Reaction_orthoBasis_eq_compContract`.

NEEDS A BRIDGE (unblocked, but real work — honest scope):
- **Curvature-action Leibniz** `∇(Rm∗S)=∇Rm∗S+Rm∗∇S` in formalism A. Route:
  express `Rm∗S` via the LOWERED `Rm04` + `g⁻¹` raising (not the (1,3) `rm13`), then
  `nabla0SFun_product_eval` + `∇g⁻¹=0` give `∇Rm04∗(·)+Rm04∗(·)∇S` — both bounded
  (`∇Rm04=nablaRm04Field`). Needs the `rm13 = raise(rm04)` identification (the
  realization predicates `Rm13RealizesConnection`/`Rm04RealizesConnection` relate them).
- **Metric-trace/∇-commute in formalism A.** `metricTrace2_covDeriv_comm` exists
  (`MetricTraceIntertwining.lean:98`) but in formalism B (`tensorCov`/`TensorRSModel`);
  port/bridge to `nabla0SFun`, OR derive `∇(metricTrace2 T)=metricTrace2(∇T)` from
  `∇g⁻¹=0` + product Leibniz directly in A.
- **Frame reconciliation** (ortho `gInv=δ` collapse vs the `∂ₜ` in `coordinateFrameAt`).

PARTIAL (conditional assembly): Uhlenbeck base `∂ₜRm=ΔRm+Rm∗Rm` —
`uhlenbeckCurvatureEvolution_of_solution_components` (`Uhlenbeck.lean:1122`) is
sorry-free but takes the pullback / B-tensor / Ricci-drift evolution as HYPOTHESES
(`hiota`/`hpull`/`hlap`/`hB`/`hrm`); its docstring flags "the remaining proof
frontier is still the raw product-rule cancellation in
`uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow` (`:987`)". So the base is
built-but-conditional — the hypotheses must still be discharged for a real
solution (the "banked but unbuilt" Lemma 6.1). Task #43 = discharge these +
bridge to formalism A.

## Build stages (tasks #39–46)

39. `genStar` reusable contraction + ∇-Leibniz + ortho bound (tensor layer).
40. `IsGenStarSum a b F` (factors ∇ᵃRm,∇ᵇRm) + bound + ∇-step (a→a+1 ⊕ b→b+1).
41. `StarSum2 k E` j-bucketed + `.nabla`/`.add` + j-indexed bound extraction.
42. Spatial `[Δ,∇ᵏ]Rm ∈ StarSum2 k` via one-step peeling + `nablaKRm04_ricciIdentityAt`.
43. Uhlenbeck base (verify `Uhlenbeck.lean` shape; bridge to formalism A).
44. Time recursion `∂ₜ∇ᵏRm=∇(∂ₜ∇^{k-1}Rm)+∂ₜΓ∗∇^{k-1}Rm` → `E_k ∈ StarSum2 k`.
45. Frame reconciliation.
46. Assemble `combinedStar=Σⱼ star_j` → heatEq+starBound → IteratedRmTowerOn →
    BernsteinShiSolution → BBS bounds → extends_of_rmBounded; full build + axiom sweep.

## Honest status

The route is sound and most primitives are in-tree (the over-counting lesson held:
~5 "missing" pieces were present). It is NOT pure assembly — the curvature-action
Leibniz (via lowered `Rm04`+`g⁻¹`) and the formalism-A trace/∇-commute are genuine,
unblocked bridges. Substantially de-risked from "deferred hard frontier"; a
tractable multi-stage build.

## Build progress (2026-06-07)

**Brick 1 GREEN** — `nablaKRm_product_eval` (`Evolution/StarSum/ProductLeibniz.lean`,
focused `lake env lean` check passes). The bundled product Leibniz for two iterated
curvature derivatives `∇(∇ⁱRm ⊗ ∇ʲRm) = ∇^{i+1}Rm⊗∇ʲRm + ∇ⁱRm⊗∇^{j+1}Rm`, a direct
specialisation of `nabla0SFun_product_eval` to `nablaKRm04Field_realizes`. This
**empirically validates the route**: the frame-free `∇`-step works, the realization
API plugs in, and the rank defeq `4+(i+1) ≡ (4+i)+1` goes through. The `k=1`
coordinate-frame wall is genuinely avoided.

**Next brick: trace/∇-commute in formalism A.** `∇(metricTraceFirstTwo0S T)` vs
`metricTraceFirstTwo0S(∇T)`. NOT directly in tree (only `metricTrace2_covDeriv_comm`
in formalism B; `roughLap0STensor = metricTraceFirstTwo0STensor`, RoughLaplacian.lean:712).
Key structural insight for the `StarSum2` closure: `∇` commutes with the `g⁻¹` trace
EXACTLY (no curvature term, by `∇g⁻¹=0`) but with a SLOT SHIFT — the trace moves from
slots (1,2) of `T` to slots (2,3) of `∇T` (the new derivative slot is prepended).
Relating the shifted trace to the standard one invokes the Ricci identity, whose
output `Rm ∗ ∇ᵏRm` stays TWO-FACTOR — so the controlled-star class is closed under
`∇` (GPT Pro's point, now concretely understood). Time-space swap exists
(`iteratedRmComp_hasDerivWithinAt`).

Also: deleted stray `_AxiomProbe.lean` (leftover prior-session probe) from the root.

## Codex live audit and next Claude handoff (2026-06-07)

### Current live status

Focused checks pass for the current critical chain:

- `Evolution/StarSum/ProductLeibniz.lean`
- `Evolution/RmRealizationBridgeAllK.lean`
- `Evolution/NablaRiemannHeatFull.lean`
- `Evolution/IteratedRmTowerHeatEq.lean`
- `Evolution/IteratedRmTowerProducer.lean`
- `Evolution/BernsteinShiSolution.lean`

No proof-body `sorry`/`admit`/new `axiom` was found in the checked core files;
the remaining `axiom` hits are documentation text about axiom-clean audits.

Tracked/untracked caution:

- `IteratedRmTowerHeatEq.lean` and `IteratedRmTowerProducer.lean` are tracked.
- `BBSAllKBundledRoute.md` and `Evolution/StarSum/ProductLeibniz.lean` are
  currently untracked in this checkout, even though `ProductLeibniz.lean`
  focused-checks.
- `DifferentialGeometry/_AxiomProbe.lean` is deleted in the worktree; it appears
  to have been a leftover probe.

`BernsteinShiSolution.lean` still correctly consumes
`IteratedRmTowerOn`; there is no hidden `estimate_of_hheat` or wrapper bypassing
the producer frontier.

### Updated frontier classification

Closed:

- all-`k` realization bridge for bundled `nablaKRm04Field`;
- k = 1 full heat-bound infrastructure;
- intrinsic all-`k` norm heat equation
  `nablaKRm04NormHeatEquationOn_intrinsic`;
- orthonormal reaction-form bridge
  `nablaKRm04Reaction_orthoBasis_eq_compContract`;
- Ricci half of the star bound via `abs_ricStarArray_le`;
- product Leibniz brick for two iterated curvature factors,
  `nablaKRm_product_eval`.

Still open:

- the actual `StarSum2` / controlled-star-sum structure is not implemented in
  Lean;
- no theorem in Lean relates the concrete residual
  `(partial_t - Delta) nabla^k Rm` to a j-bucketed family
  `star k j` satisfying the `starBound` shape;
- formalism-A metric-trace/nabla commute is still the next bridge:
  `nabla (metricTraceFirstTwo0S T)` versus
  `metricTraceFirstTwo0S (nabla T)`, with the derivative slot shift;
- Uhlenbeck base hypotheses remain conditional producer work, not the next small
  brick for the StarSum2 induction;
- frame reconciliation remains a later assembly issue.

### Next Claude plan

Do not try to assemble `IteratedRmTowerOn` yet.  The next small useful producer
is the metric-trace/nabla commute bridge in the `nabla0SFun` /
`TotalNabla0SRealizes` formalism, because it is needed to differentiate the rough
Laplacian term in the one-step peeling:

```text
E_k = (partial_t - Delta) nabla^k Rm
    = nabla E_{k-1} + (partial_t Gamma) * nabla^{k-1}Rm
      - [Delta, nabla] nabla^{k-1}Rm.
```

#### Target file placement

Start in the tensor metric-trace layer, not in a Ricci-flow file.

Preferred options:

- extend `Tensor/RSTensor/MetricTrace/Higher.lean`; or
- add a focused new file under `Tensor/RSTensor/MetricTrace/`, imported by
  `Higher.lean` or by the future StarSum module.

Only after the tensor theorem is proved should a thin Ricci-flow specialization
be added under `Evolution/StarSum/`.

#### Theorem shape to build first

Use the existing `nablaTrace02` / `nablaTrace04` pattern.  The desired theorem is
not the old formalism-B statement
`metricTrace2_covDeriv_comm`; it should be stated directly in formalism A:

```lean
-- schematic shape, not final syntax
theorem nabla_metricTraceFirstTwo0S
    (cov : CovariantDerivative ...)
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible_gen cov g)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (T : Tensor0SField ... (s + 2))
    (nablaT : Tensor0SField ... (s + 3))
    (hreal : TotalNabla0SRealizes ... T nablaT)
    ... :
    nabla0SFun ... cov X (traceFirstTwoField g T) x tail
      =
    metricTraceFirstTwo0SAt g
      (nablaT x) (slotShift X tail)
      + controlled curvature/slot-shift correction if needed
```

Important: first prove the exact commutation with the correct slot shift.  Do
not fold the Ricci-identity correction into a vague "controlled term" unless the
slot-shift comparison really demands it.  The note's current expectation is:

- trace itself commutes with `nabla` by metric compatibility;
- comparing the shifted trace to the standard rough-laplacian trace is where
  the Ricci-identity/curvature-action term enters.

#### Existing templates to inspect first

- `Tensor/RSTensor/MetricTrace/NablaTrace02.lean`
  - `nablaTrace02`
  - basis-free upgrade below it
- `Tensor/RSTensor/MetricTrace/Higher.lean`
  - `middleFreezeNabla`
  - `nablaTrace04`
- `Geometry/Curvature/Order2Defect/MetricTraceIntertwining.lean`
  - `metricTrace2_covDeriv_comm`
  - use as reference only; it lives in formalism B.
- `Geometry/Operator/RoughLaplacian.lean`
  - `metricTraceFirstTwo0STensor`
  - `roughLap0STensor`

#### After the trace/nabla bridge checks

1. Add the Ricci-flow specialization:

   ```lean
   theorem nabla_roughLap0S_nablaKRm
       ...
   ```

   This should express the derivative of the rough-Laplacian trace of
   `nabla^k Rm` in terms of the trace of `nabla^{k+3}Rm`, with the slot-shift
   made explicit.

2. Use `nablaKRm04_ricciIdentityAt` to convert the slot-shift discrepancy into a
   controlled `Rm * nabla^k Rm` / `nabla Rm * nabla^{k-1}Rm` star contribution.

3. Only then introduce a minimal `StarSum2` predicate:

   ```lean
   structure StarSum2 ... where
     split : ...
     bound : ...
   ```

   Keep it small: enough for `.add`, `.nabla`, and extraction of the per-j
   `starBound`; do not build a large algebraic hierarchy.

#### Stop conditions

Stop and record the exact blocker if:

- the formalism-A trace field cannot be expressed as a `Tensor0SField`;
- `nablaTrace02` / `nablaTrace04` cannot be generalized beyond fixed rank without
  new frame-free freezing infrastructure;
- the slot-shift comparison requires a Ricci identity theorem not available for
  `nablaKRm04Field`;
- the proof starts unfolding `Tensor0SSpace` internals or Hom representations
  instead of using `component0S`, `tensor0SComponent`, and existing realization
  APIs;
- ProductLeibniz cannot be imported cleanly into the next module because the
  current `StarSum/ProductLeibniz.lean` file is still untracked or missing from
  the root import path.

#### Acceptance

- No new `sorry`.
- Focused checks pass for the touched tensor metric-trace file and the thin
  Ricci-flow StarSum consumer.
- `#print axioms` on new public theorems shows only
  `[propext, Classical.choice, Quot.sound]`.
- Update this note with whether the trace/nabla bridge passed or the exact
  theorem that blocked it.

### Claude prompt

```text
Work in E:\testdifferential-geometry. DifferentialGeometry/ is primary;
RicciFlower/ is reference only.

Live status:
- IteratedRmTowerHeatEq.lean and IteratedRmTowerProducer.lean focused-check.
- StarSum/ProductLeibniz.lean focused-checks but is currently untracked.
- BernsteinShiSolution.lean still correctly consumes IteratedRmTowerOn.
- The all-k intrinsic heat equation is done, but IteratedRmTowerOn is not
  produced because the concrete residual has not been decomposed into j-indexed
  controlled star arrays.

Task:
Build the next StarSum2 brick: metric-trace/nabla commutation in formalism A
(`nabla0SFun` / `TotalNabla0SRealizes`), not the old formalism-B
`tensorCov` / `TensorRSModel` route.

Start by inspecting:
- Tensor/RSTensor/MetricTrace/NablaTrace02.lean
- Tensor/RSTensor/MetricTrace/Higher.lean
- Geometry/Curvature/Order2Defect/MetricTraceIntertwining.lean
- Geometry/Operator/RoughLaplacian.lean

Implement the smallest tensor-layer theorem saying that covariant derivative
passes through `metricTraceFirstTwo0S` under metric compatibility, with the new
derivative slot shift made explicit. Then add a thin Ricci-flow specialization
for the rough Laplacian of `nablaKRm04Field`.

Do not:
- assemble IteratedRmTowerOn yet;
- add assumptions equivalent to starBound/heatEq;
- unfold Tensor0SSpace/Hom internals;
- use coordinateFrameAt as if it were orthonormal;
- rely on the formalism-B metricTrace2_covDeriv_comm except as a proof template.

Stop if the formalism-A trace field cannot be expressed as a Tensor0SField, if
rank-uniform freezing is missing, or if the slot-shift comparison needs a
missing all-k Ricci identity. Report the exact missing theorem and target file.

Verification:
Run focused lake-locked checks for touched files and #print axioms for new public
theorems. Update BBSAllKBundledRoute.md with the result.
```

## Brick result (2026-06-07, metric-trace/∇ bridge)

**The stop condition (need new general-`s` freezing infra) WAS hit — but it is NOT
a wall.** Confirmed: the formalism-A trace/∇-commute reduces (via the
`nablaTrace02`/`nablaTrace04` pattern) to freezing the non-traced slots into a
smooth `(0,2)` field + `nablaTrace02`; the `d(gInv)≠0` variation is absorbed only
covariantly through `inner0S`, so freezing is genuinely required. All in-tree
freezes are arity-fixed (`freezeHead03Field`/`freezeTail04Field`/`freezeMiddle04Field`
rank 3-4; `freezeLastTwo0S3`; `freezeAllBut04Field`); `partialEval0SField` freezes
only the first slot. So the general-`s` smooth freeze-tail wrapper was the missing
piece — and it is buildable.

**BUILT (focused `lake env lean` GREEN, EXIT 0):**
`freezeTailField {s} (A : (0,s+2)) (Y : Fin s → section) : (0,2)`
(`Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`) + `freezeTailField_apply`.
The rank-`s` smooth-field wrapper freezing the last `s` slots, leaving the first
two free — the direct generalisation of `freezeTail04Field`. Key point: the
pointwise `freezeFirstTwo0S` is already rank-uniform, and the wrapper's OUTPUT is
always `(0,2)`, so the bundle-trivialisation half of the smoothness proof is
identical to the `s=2` case; only the `Fin (s+2)` input slot tuple generalises
(slot reductions via `metricTraceInput = Fin.cases _ (Fin.cases _ _)`, with the
`Fin.succ 0` vs literal `1` normalisation handled by `simp only` keeping succ form).

**Sub-bricks for `nabla_metricTraceFirstTwo0S` (the target theorem):**
1. ✅ **GREEN** — `metricTraceFirstTwoField {s} g (A : (0,s+2)) : (0,s)`
   (`NablaTraceGen.lean`): the smooth trace field (trace first two, leave tail),
   rank-`s` generalisation of `trace04Field` (no `domDomCongr`, output `(0,s)`).
   With helpers `traceFirstTwoIdx`, `metricTraceInput_coordFrame`,
   `metricTraceFirstTwoEvent`, `metricTraceFirstTwoCoeff`.
2. ✅ **GREEN** — `tailFreezeNablaGen` (`NablaTraceGen.lean`):
   `∇(freezeTailField A Y) (X,U,V) = ∇A (X, U, V, Y)` for `Y` parallel-at-`x`.
   Rank-`s` generalisation of `tailFreezeNabla`; `Fin (s+2)` correction sum
   vanishes termwise (`Finset.sum_eq_zero` + parallel slots +
   `metricTrace_tensor0S_update_zero`).
3. ✅ **GREEN + AXIOM-CLEAN** — `nabla_metricTraceFirstTwo0S` (`NablaTraceGen.lean`):
   `∇(metricTraceFirstTwoField g A)(cons X tail)
      = Σᵢⱼ gⁱʲ · ∇A (cons X (metricTraceInput (basis i)(basis j) tail))`.
   Assembled from (1)+(2)+`nablaTrace02` mirroring `nablaTrace04`: realise `tail`
   by `Vtail : Fin s` parallel-at-`x` sections (`choose … exists_cov_zero_at_apply`),
   `B := freezeTailField A Vtail`, `nablaTrace02` on `B`, each `∇B` term converted
   via `tailFreezeNablaGen`. Helper `metricTraceFirstTwo0STensor_eq_pair_freeze`
   (per-point `coordinateFrameAt_toBasis`). Clean commute, NO curvature term.

**TRACE/∇ BRIDGE COMPLETE (2026-06-07).** All four pieces GREEN + the two public
theorems AXIOM-CLEAN (`[propext, Classical.choice, Quot.sound]`), confirmed by
targeted `lake-locked` builds (`+…NablaTraceGen` 3551 jobs, `+…RoughLapNablaK`
3633 jobs):
- `Tensor/RSTensor/MetricTrace/NablaTraceGen.lean` — `freezeTailField`,
  `tailFreezeNablaGen`, `metricTraceFirstTwoField`, `nabla_metricTraceFirstTwo0S`.
- `Evolution/StarSum/RoughLapNablaK.lean` — `nabla_roughLap0S_nablaKRm`, the
  Ricci-flow specialisation: `∇(Δ∇ᵏRm)(X :: tail)
    = Σᵢⱼ gⁱʲ · ∇^{k+3}Rm (X :: eᵢ :: eⱼ :: tail)` (via `nablaKRm04Field_succ`
  identifying `totalNabla0SFun(∇^{k+2}Rm) = ∇^{k+3}Rm`).

This discharges the formalism-A metric-trace/∇ commute (StarSum2 build stage,
the `[Δ,∇]` ingredient). Files are verified standalone (focused + targeted build)
but not yet wired into the root import — they will be imported by the StarSum2
consumer.

## Spatial commutator (2026-06-07) — GREEN + axiom-clean

`spatialComm_nablaKRm_traceDiff` (`Evolution/StarSum/RoughLapNablaK.lean`, targeted
build EXIT 0, `#print axioms` = `[propext, Classical.choice, Quot.sound]`): the
all-`k` spatial Laplacian–covariant commutator, the bundled analogue of the `k=1`
`nablaLapComm_trace`:

`Δ(∇^{k+1}Rm)(X,tail) − ∇(Δ∇ᵏRm)(X,tail)
  = Σᵢⱼ gⁱʲ · [ ∇^{k+3}Rm(eᵢ,eⱼ,X,tail) − ∇^{k+3}Rm(X,eᵢ,eⱼ,tail) ]`.

LHS = `[Δ,∇_X]∇ᵏRm` (`Δ(∇^{k+1}Rm)=roughLap=metricTraceFirstTwo0STensor(∇^{k+3}Rm)`,
trace of the two outer derivative slots; `∇(Δ∇ᵏRm)` = `nabla_roughLap0S_nablaKRm`,
trace of the two middle slots). RHS = the cyclic antisymmetrisation of the three
leading derivative slots of `∇^{k+3}Rm`.

**NEXT bridge (the genuine remaining hard one): convert the RHS bracket to
controlled `Rm∗∇ᵏRm` star terms.** Telescope the bracket via the middle slot
`∇^{k+3}Rm(eᵢ,X,eⱼ,tail)`:
- the slots-(0,1) swap `∇^{k+3}Rm(eᵢ,X,eⱼ,..) − ∇^{k+3}Rm(X,eᵢ,eⱼ,..)`
  = `curvatureAction(rm13)(∇^{k+1}Rm)(eᵢ,X,eⱼ::tail)` directly via
  `nablaKRm04_ricciIdentityAt` at level `k+1` (needs `hS : IsSolutionOn` +
  `t : RegularTime D`) — controlled, easy;
- the slots-(1,2) swap `∇^{k+3}Rm(eᵢ,eⱼ,X,..) − ∇^{k+3}Rm(eᵢ,X,eⱼ,..)`
  = `∇_{eᵢ}([∇_{eⱼ},∇_X]∇ᵏRm)` = `∇(curvatureAction)` — **the curvature-action
  Leibniz `∇(Rm∗S)=∇Rm∗S+Rm∗∇S`**, the one the `k=1` `NablaRiemannCommutatorBound`
  footer got stuck on in the chart frame; now approachable frame-free via GPT Pro's
  route (express `curvatureAction(rm13)(S)` as a `gInv`-contraction of `Rm04 ⊗ S`
  using `Rm04LowersRm13At`, then `nabla0SFun_product_eval` + `∇gInv=0`). This is a
  substantial fresh bridge, comparable in size to the trace bridge.

After that: the `StarSum2` class + the one-step peeling + Uhlenbeck base + frame
reconciliation + assembly → `IteratedRmTowerOn`.

## Full `extends_of_rmBounded` chain + the gating theorem (2026-06-07, /goal)

`extends_of_rmBounded` (`MaximalTime.lean:151`, a single `sorry`) = the WHOLE BBS
pillar:
```
extends_of_rmBounded                         (MaximalTime.lean:151, sorry)
 └ ricci_flow_extends_construction           (CinftyLimitGlue.lean:632 — built;
   │                                          carries DeTurck sorryAx via restart_short_time)
 └ CinftyLimitData + glue (CinftyGlueData)   (C∞ convergence from BBS bounds — NOT built)
 └ bernsteinShi_solution_estimate            (BernsteinShiSolution.lean:139 — built,
   │                                          consumes IteratedRmTowerOn)
 └ IteratedRmTowerOn                          (NOT produced — the StarSum2 route)
   └ heatEq/starBound reaction decomposition  (E_k = Σⱼ ∇ʲRm∗∇^{k-j}Rm)
     └ one-step peeling E_k=∇E_{k-1}+∂ₜΓ∗T_{k-1}−[Δ,∇]T_{k-1}
       └ [Δ,∇]: spatialComm_nablaKRm_traceDiff ✅ + the curvature-action Leibniz ⛔ (GATING)
```
Remaining after the gate: StarSum2 class, Uhlenbeck base, time recursion, frame
reconciliation, IteratedRmTowerOn assembly, C∞-convergence wiring, final
extends_of_rmBounded assembly — ~7 substantial bricks + the DeTurck sorryAx.
Multi-session.

### GATING theorem: curvature-action Leibniz `∇(Rm∗S)=∇Rm∗S+Rm∗∇S`

This is exactly the theorem `NablaRiemannCommutatorBound.lean`'s footer + third-
attempt addendum documents as having FAILED THREE genuinely different routes:
1. **coordinate-frame component ∇** (`T₁ = ∇_a K` via `eval_C1_slots`): produced
   `extDerivFun(curvatureAction) − Σ Christoffel-corrected curvatureActions`, but
   neither summand is bounded by `|Rm||∇Rm|` (only their covariant combination is);
   `∇rm13` undefined in the frame.
2. **field-level `domDomCongr`/∇-commutation**: declared blocked at the field level.
3. **rm04-contraction route**: "not assemblable in the current tree at the four
   points itemised" — (a) `∇g⁻¹=0` not statable; (b) `rm13=raise rm04` not a usable
   field lemma; (c) `∇rm13` needs a `(1,3)` realization absent from the tree; (d)
   frame mismatch (chart frame not orthonormal at centre).

**4th route — now VIABLE (the over-count correction).** All four of route-3's
obstructions are now lifted:
- (a) `∇g⁻¹=0` IS available: `inverseMetricCovDerivForMetricCompInFrame_eq_zero`.
- (b) `Rm04LowersRm13At` (`Curvature/Components/Lowering.lean:32`): `Rm04(X,Y,Z,W) =
  Rm13(W♭)(X,Y,Z)`, hence `Rm13(ω)(X,Y,Z) = Rm04(X,Y,Z, sharp ω)`.
- (c) `∇rm13` is now expressible: `cotangentSharp_gen` (the raising of a covector)
  exists WITH its covariant derivative `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
  and basis form `cotangentSharp_eq_sum_inv_gen` (`Tensor0SRiemannian/Smooth.lean`,
  `Product.lean`); so `∇(Rm13(ω)) = ∇(Rm04(·, sharp ω))` via the sharp's ∇ + `∇g⁻¹=0`.
- (d) frame mismatch is avoided by the bundled/frame-free route (collapse to an
  orthonormal frame only at the end, as in the trace bridge).
The 4th route: express `curvatureAction0SAt(rm13)(S)(X,Y,slots) =
−Σ_q Rm04(X,Y,slots_q, cotangentSharp(oneFormAtSlot0S S slots q))`, then bundled ∇
via `nabla0SFun_product_eval` + `cotangentSharp`'s ∇ + `∇g⁻¹=0`. It is a substantial
fresh build (comparable to the trace bridge), NOT a wall. Equivalently (route 4'),
fold it into the `StarSum2` class by expressing the single commutator output
`curvatureAction(rm13)(∇ᵏRm)` as a metric-trace star `metricTrace(Rm04 ⊗ ∇ᵏRm)`
(same `Rm04`+sharp expression) so the class's `.nabla` handles the ∇ generically.

### Route 4 — FOUNDATION BUILT (2026-06-07, /goal, count reset)

✅ **GREEN + targeted-built** (`Geometry/Curvature/CurvatureActionLower.lean`,
3570 jobs):
`curvatureAction0SAt_eq_rm04` — the curvature action through the lowered `Rm04`,
all rank `s`, component form:
```
curvatureAction0SAt Rm13 S X Y slots
  = −Σ_q Σ_p (Σ_r gⁱ ᵖ ʳ · S(slots[q ↦ e_r])) · Rm04(X,Y,slots_q,e_p).
```
**No `(1,3)` tensor remains** — only `Rm04`, `gInv`, `S`. Assembled cleanly from
`rm13_oneForm_apply_eq_sum_inv_flat` (`Contractions.lean`) + `Rm04LowersRm13At`
(`Components/Lowering.lean`). This is precisely the key the prior 3 routes lacked
(over-counting lesson again: it was buildable from existing machinery). Route 4 is
**viable and advancing — NOT a wall**.

**Route-4 continuation (the substantial next piece):** the BUNDLED covariant
derivative of the curvature action. The component identity above is the stepping
stone; the bundled `∇(curvatureAction) = ∇Rm∗S + Rm∗∇S` needs the curvature action
as a bundled tensor (a `gInv`-contraction of `Rm04 ⊗ S`) + its ∇ via
`nabla0SFun_product_eval` + `∇g⁻¹=0` + parallel-section slots — the same technique
as the trace bridge, ~150 lines. Then it feeds the spatial-commutator term-B
(slots-(1,2)-swap) bound.

✅ **GREEN + axiom-clean** — `spatialComm_nablaKRm_split` (`Evolution/StarSum/RoughLapNablaK.lean`):
the all-`k` spatial commutator with the controlled curvature half split off:
```
[Δ,∇]∇ᵏRm = Σᵢⱼ gⁱʲ · ( (∇^{k+3}Rm(eᵢ,eⱼ,X,t) − ∇^{k+3}Rm(eᵢ,X,eⱼ,t))   -- term-B (route-4 residual)
                       + curvatureAction(rm13)(∇^{k+1}Rm)(eᵢ,X,eⱼ::t) ) -- controlled (Ricci k+1)
```
The controlled term is bounded by `|Rm|·|∇^{k+1}Rm|` (`abs_curvatureAction0SAt_orthoBasis_le`);
term-B = `∇_{eᵢ}([∇_{eⱼ},∇_X]∇ᵏRm)` is the residual the route-4 bundled
curvature-action Leibniz closes. Telescoping via the middle ordering `(eᵢ,X,eⱼ)`,
slots-(0,1) swap → Ricci `nablaKRm04_ricciIdentityAt` (k+1), defeq `cons X ∘ mTI =
mTI X ∘ cons`, `linarith`.

**Segment summary (this /goal segment, count-reset): 5 axiom-clean theorems** on the
gating frontier — `nabla_metricTraceFirstTwo0S`, `nabla_roughLap0S_nablaKRm`,
`spatialComm_nablaKRm_traceDiff`, `curvatureAction0SAt_eq_rm04`,
`spatialComm_nablaKRm_split`. Route 4 is **viable and advancing** — the prior
3-routes "wall" is dissolved.

### DECISIVE: the curvature-action Leibniz is fully proven for k=1 — term-B is route-clear

Reading the existing tree (over-counting lesson again): the **entire k=1
curvature-action Leibniz already exists, no sorry**:
* `nabla2Rm04Field_antisym_eq_curvatureAction_field` / `nabla2Rm04Field_slot01_antisym`
  (`NablaRiemannCommutatorBound.lean:263,334`) — the level-1 Ricci identity as a field.
* `nabla3_antisym_eq_covDeriv_curvatureAction_covConst`
  (`NablaRiemannReactionBound.lean:378`) — **term-B (k=1) = `extDerivFun(K)`** on
  cov-constant sections, via `eval_smooth_slots` + vanishing corrections.
* `nablaLapComm_T1_eq_rm04_raise_leibniz` (`NablaRiemannReactionBound.lean:513`) —
  **term-B (k=1) = `−Σ_q (∇Rm04∗Rm04 + Rm04∗∇Rm04)` raise contractions** (exactly
  the `cotangentSharp_gen` + `rmFrozenSlotField` raise route planned here).
* the bound `|∇(curvatureAction rm13 rm04)| ≤ C(card)·|Rm04|·|∇Rm04|`
  (`IteratedNablaRmTower.md:320`).

So my all-k `spatialComm_nablaKRm_split` is the all-k analog of the k=1 reaction-term
decomposition `nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction`,
and **term-B's all-k bound is the all-k generalization of `NablaRiemannReactionBound`**,
not a fresh frontier. Generalization map (each step has a complete k=1 template):
`nabla2Rm04Field → nablaKRm04Field…(k+2)`, `nabla3Rm04Field → …(k+3)`,
`Fin 6 → Fin (6+k)`, `Fin 4 → Fin (4+k)`, `S.base.rm04 → nablaKRm04Field…k`,
`rm04_ricciIdentityAt → nablaKRm04_ricciIdentityAt…k`,
`nabla2SlotSections → all-k cons-slot-sections`,
`nabla3Rm04Field_realizes → nablaKRm04Field_realizes (k+3)`. The slot-section
cov-constant proofs are `Fin.cases`-twice + tail, length-independent, so they
generalize mechanically. **Verdict: route 4 is proven; the remainder is a careful
all-k port of one file.**

Remaining on the immediate critical path: all-k port of `NablaRiemannReactionBound`
(term-B bound, ~1 file), then `StarSum2` class + Uhlenbeck + time recursion + frame +
assembly + C∞-convergence + final wiring + DeTurck sorryAx.

### All-k port IN PROGRESS — covDeriv conversion BUILT (2026-06-07)

✅ **GREEN + axiom-clean** — `Evolution/StarSum/NablaReactionAllK.lean` (3695 jobs):
* `nablaKSlotSections` / `nablaKSlotSections_apply` — the all-k `∇^{k+2}Rm` slot
  sections `Fin.cons Vb (Fin.cons Vc Vm)` (`Fin (4+(k+2))`), rank-uniform port of
  `nabla2SlotSections`.
* **`nablaK_antisym_eq_covDeriv_curvatureAction`** — the all-k port of the k=1
  `nabla3_antisym_eq_covDeriv_curvatureAction_covConst`: on cov-constant sections,
  **term-B = `extDerivFun(K)`**, `K(y) = curvatureAction(rm13)(∇ᵏRm y)(Vb,Vc,Vm)`.
  Proof = the mechanical generalization: `eval_smooth_slots` of
  `nablaKRm04Field_realizes S t (k+2)`, corrections vanish (`map_update_zero` on
  cov-constant slots), difference field = `nablaKRm04_ricciIdentityAt … k`.

Lean notes for the port: (a) index the slot family as `Fin (4+(k+2))` (the
realization's rank), NOT `Fin (4+k+2)` — they are defeq but `rw`/`∑` need the
syntactic match; (b) fold the connection in the `eval_smooth_slots` output with
`rw [← hcov_def] at hbc hcb` before the correction rewrite (the `set cov` does not
fold freshly-produced terms); (c) coerce the realization's `∇^{(k+2)+1}Rm` to the
statement's `∇^{k+3}Rm` via `have ebc : … := hbc` (defeq through `exact`, not `rw`).

**Segment tally: 6 axiom-clean all-k theorems.** Next on the all-k port: the
raise-Leibniz `extDerivFun(K) = −Σ_q (∇Rm04∗∇ᵏRm + Rm04∗∇^{k+1}Rm)` (port of
`nablaLapComm_T1_eq_rm04_raise_leibniz`), needing the level-`k` frozen-slot
one-form machinery (`rmFrozenSlotField`/`nablaRmFrozenSlotField` at `∇ᵏRm`), then
the norm bound, then `StarSum2` + the rest of the pillar.

### Raise-Leibniz port — frozen-slot machinery BUILT (2026-06-07/08)

✅ **GREEN** — `Evolution/StarSum/FrozenSlotAllK.lean` (full build, 3634 jobs):
`freezeAllBut0SField` (+ `_apply`, `_apply_vec`) — the **rank-generic** frozen-slot
one-form field, a verbatim `Fin 4 ↦ Fin s` port of `freezeAllBut04Field` (all the
smoothness inputs were already rank-uniform). Needs `open
DifferentialGeometry.Tensor.Coordinates Filter`.

✅ **GREEN (focused)** — added to `Evolution/StarSum/NablaReactionAllK.lean`:
`nablaKRmFrozenSlotField` (= `freezeAllBut0SField (∇ᵏRm) q Y`, level-`k` frozen
one-form of `∇ᵏRm`), `nablaKRmFrozenSlotField_apply_vec`,
`nablaKRmNablaFrozenSlotField` (its `∇`), `nablaKRmNablaFrozenSlotField_realizes`.
Mechanical ports of `rmFrozenSlotField`/`nablaRmFrozenSlotField`.

🟢 **FREE (over-counting again)** — `curvatureAction0SAt_eq_rm04_raise`
(`RmRaisingBridge.lean:172`) is **already generic in `alpha`** (any rank `s`):
`curvatureAction Rm13 α X Y slots = −Σ_q Rm04(X,Y,slots_q, g♯(oneFormAtSlot0S α slots q))`.
So the raise form is free for `α = ∇ᵏRm`; no port.

KEY STRUCTURE NOTE for the per-`q` Leibniz: the **outer `Rm04` is always rank 4**
(the curvature), so `rmRaiseSlotSections` stays `Fin 4` `![Vb, Vc, Vm q, g♯β_q]` and
`nablaRm04Field_realizes` (rank 4→5) is UNCHANGED for all `k`; only the raised frozen
one-form `g♯β_q` (its section + smoothness) and `q : Fin (4+k)` are `k`-dependent.
So `rmRaise_summand_covDeriv` ports by swapping `rmFrozenSlot*` → `nablaKRmFrozenSlot*`.

### ★ MILESTONE: the all-k curvature-action Leibniz is COMPLETE (2026-06-08) ★

✅ **GREEN + axiom-clean** (full build 3696 jobs) — `Evolution/StarSum/NablaReactionAllK.lean`:
the raised-frozen-one-form section + smoothness + `mdiffAt` (ports of `rmFrozenSlotSharpSection`
etc.), the per-`q` Leibniz **`nablaKRmRaise_summand_covDeriv`** (verbatim port of
`rmRaise_summand_covDeriv`, outer `Rm04` rank-4 = `k`-independent), and the assembly

**`nablaK_antisym_eq_rm04_raise_leibniz`** (axiom-clean):
```
∇^{k+3}Rm(X, Vb, Vc, Vm) − ∇^{k+3}Rm(X, Vc, Vb, Vm)
  = −Σ_q [ (∇Rm04)(X,Vb,Vc,Vm_q, g♯β_q) + Rm04(Vb,Vc,Vm_q, g♯(∇_X β_q)) ]
```
i.e. **term-B = `∇Rm04∗∇ᵏRm + Rm04∗∇^{k+1}Rm`**, the curvature-action Leibniz
`∇(Rm∗∇ᵏRm)=∇Rm∗∇ᵏRm+Rm∗∇^{k+1}Rm` for ALL `k`, with NO `∇rm13`.  **This is the
exact content the prior "3-routes wall" was stuck on — route 4 is proven.**

Lean note: `curvatureAction0SAt_eq_rm04_raise` is generic in `α`; the `hKfield` step
closes with `rfl` (`oneFormAtSlot0S (∇ᵏRm)(Vm) q = nablaKRmFrozenSlotField` definitionally).
Need opens `Tensor.Coordinates`, `Integral.Measure` (chartBasisVecFiber),
`Integral.DivergenceTheorem` (cotangentSharp/`T%`).

### ★ MILESTONE 2: the all-k term-B NORM BOUND is COMPLETE (2026-06-08) ★

✅ **GREEN + axiom-clean** — the all-k `|term-B|` bound, completing the analytic heart
of the BBS reaction:
* `FrozenSlotAllK.lean`: `allBut0SFreezeNabla` (rank-generic frozen-slot `∇` identity,
  port of `allBut04FreezeNabla`).
* `NablaReactionAllK.lean`: `nablaKRmFrozenSlot_eval` (`∇β_q ↔ ∇^{k+1}Rm`),
  **`abs_nablaK_antisym_covConst_le`** and **`abs_nablaK_antisym_basis_le`**:
  ```
  |∇^{k+3}Rm(a, b, c, m) − ∇^{k+3}Rm(a, c, b, m)|
    ≤ (4+k)·card·( |∇Rm|·|∇ᵏRm| + |Rm|·|∇^{k+1}Rm| )
  ```
  the two BBS reaction star terms `∇Rm∗∇ᵏRm + Rm∗∇^{k+1}Rm`.

KEY: the k=1 file (`NablaRiemannReactionBound`) is really the **`k = 0`** case (curvature
action on `∇⁰Rm = Rm04`, where `|∇⁰Rm|=|Rm|`, `|∇¹Rm|=|∇Rm|` collapse the two terms into
one `|Rm||∇Rm|`); the all-k version carries **four distinct norms** (`Nnab=|∇Rm|` rank 5,
`NRm=|Rm|` rank 4, `Nk=|∇ᵏRm|`, `Nk1=|∇^{k+1}Rm|`). The Cauchy–Schwarz helpers
(`abs_tensor05/04_sharp_last_le`, `sum_sq_update_le_compNormSqMulti`,
`cotangentSharp_orthoBasis_expand'`) are generic and reused directly. Lean notes: index
the `∇^{k+1}Rm` tuples as `Fin (4+k+1)` (the natural `cons` output, defeq to the field's
`Fin (4+(k+1))`, bridged by `exact`); the final constant reconciliation needs
`le_of_eq` before `push_cast; ring` (the goal is `≤`, not `=`).

### ★ MILESTONE 3: the full all-k SPATIAL commutator bound is COMPLETE (2026-06-08) ★

✅ **GREEN + axiom-clean** — the entire spatial half of the BBS reaction, all `k`
(`NablaReactionAllK.lean`):
* `abs_spatialBracket_nablaKRm_ortho_le` — per-`(i,j)` bracket bound (term-B +
  controlled curvature action) via `abs_nablaK_antisym_basis_le` +
  `abs_curvatureAction0SAt_orthoBasis_le` (both generic in the acted-on tensor).
* **`abs_spatialComm_nablaKRm_ortho_le`** — the full `[Δ,∇]∇ᵏRm` ortho-frame bound:
  ```
  |Δ(∇ᵏRm) − ∇(Δ∇ᵏRm)| ≤ card·( (4+k)·card·(|∇Rm||∇ᵏRm| + |Rm||∇^{k+1}Rm|)
                                 + (4+k+1)·card·(|Rm||∇^{k+1}Rm|) )
  ```
  via `spatialComm_nablaKRm_split` with `gInv = δ` (Kronecker, the orthonormal
  inverse metric, `hinv` built as in `cotangentSharp_orthoBasis_expand'`), the
  inner sum collapsing `simp [ite_mul, Finset.sum_ite_eq]` to the diagonal.

Lean notes: the `metricTraceInput ↔ Fin.cons` slot conversions on `∇^{k+3}Rm` must go
through `congrArg` (cheap, tuple-level) — direct defeq times out `whnf` (unfolds the
deeply-nested `∇^{k+3}Rm`); the curvature-action slot `cons (basis j)(basis∘m') ↔
fun p => basis ((cons j m') p)` is NOT defeq for open `p` (needs `funext`+`Fin.cases`);
`Fin.cons j m'` needs a `: Fin _ → Fin n` annotation (motive metavar).

**Remaining**: the **TIME half** — see the full map below.

### TIME SIDE — fully worked out (2026-06-08, /goal)

The time-side **evolution identities are already BANKED** (component level):
* `christoffelEvolution_of_metricFrameTimeRegularity` (`Connection/Producers.lean:75`,
  Lemma 6.2) — produces `∂ₜΓ = −g(∇Ric…)` (`ChristoffelEvolutionEquationInFrameOn`).
* `christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`
  (`Ricci/GammaCoord.lean:141`) — `∂ₜ(R^l_{ijk})` from the Christoffel variation.
* `iteratedRmComp_hasDerivWithinAt` (`IteratedRmTowerHeatEq.lean:430`) — `∂ₜ∇ᵏRm`
  from the level-0 `∂ₜRm` (`hrm`), `∂ₜΓ` (`hchr`), and the time/space swap (`hswap`).
* `IsSolutionOn.equation : MetricVariationEquationOn` supplies `∂ₜg = −2Ric`.

**The genuine remaining frontier is the differentiability-REGULARITY WEB** — the
hypotheses the banked theorems consume, which have **no solution-facing dischargers**:
* `MetricCovDerivDerivativeComponentsInFrameOnLocal` (`Connection/Components.lean:416`)
  — `∂ₜ(∇^t g_s)_{ij}` *exists* (the deep one); its *value* is trivially `−2∇Ric`
  (`MetricCovDerivDerivativeIsRicciFlowInFrame`, line 452, definitional).
* `MetricFrameTimeRegularityInFrameOnLocal`, `ConnectionPairingDerivativeInFrameOnLocal`,
  `ChristoffelVariationMixedDerivativeInFrameOnRegular` (`hmix`), and the
  `iteratedRmComp_hasDerivWithinAt` `hswap` — all differentiability claims about the
  solution's metric/Christoffel components in a frame, from the metric-family
  smoothness + `∂ₜg = −2Ric`. Each is a substantial fixed-base time-derivative proof.

Then: ∂ₜRm04 realization+lowering (`∂ₜRm04 = ∂ₜg·Rm13 + g·∂ₜRm13`) → `hrm`; feed
`hrm`/`hchr`/`hswap` into `iteratedRmComp_hasDerivWithinAt` → `∂ₜ∇ᵏRm`; then the
**residual star decomposition** (`E_k = (∂ₜ−Δ)∇ᵏRm = Σⱼ ∇ʲRm∗∇^{k−j}Rm` — the spatial
half `abs_spatialComm_nablaKRm_ortho_le` is DONE; the time `Rm∗∇ᵏRm` from Uhlenbeck);
then the **heatEq** via the generic Bochner stack → `IteratedRmTowerOn` (its `starBound`
spatial factors now bounded) → C∞-convergence wiring → final `extends_of_rmBounded`
+ DeTurck `sorryAx`.

**Assessment:** the time side is *not* a single theorem — it is a multi-session
regularity-discharge + assembly effort. The deepest single frontier is
`MetricCovDerivDerivativeComponentsInFrameOnLocal_of_solution` (the `∂ₜ∇g` fixed-base
time-derivative from the metric-family smoothness). Classify: **missing
groundwork/API** (the solution-facing differentiability dischargers), not a math
obstruction — the evolution *identities* are all banked.

### ★ CORRECTION + BUILD (2026-06-08, /goal time-side): the time side is BUILDABLE ★

The "deep frontier" assessment above was **too pessimistic**. Genuine build attempt
found the mixed time/space derivative **swap discharger already exists**:
`fixedBaseOnReg_of_timeDerivWithin` (`Bundle/PartialMfderiv/FixedBase.lean:633`) —
manifold-level, from spacetime `ContMDiffAt` + pointwise time derivatives. And the
spatial-`MDiff` inputs are dischargeable: `ricciTensor_apply_smooth`
(`Curvature/.../RicciConnection.lean:260`, Ricci of a smooth metric is smooth),
`inner_smooth_scalar`, `TensorMultilinear.contMDiffAt_section_apply_gen`, with the
canonical-Ricci bridge `SolutionOn.ricciAt_eq`.

✅ **GREEN + axiom-clean** (full build) — `Evolution/Connection/MetricCovDerivProducer.lean`:
`metricFrameComp_fixedBaseSwap_of_solution` — the metric frame-component swap
`∂ₛ(extDeriv g_s(e_a,e_b)) = extDeriv(∂ₛ g_s(e_a,e_b))`, with **`hTime` discharged
from the solution's metric variation `∂ₛg = −2Ric`** (`IsSolutionOn.equation`); the
spatial regularity `hSmooth`/`hFdiff`/`hFtdiff` taken as inputs (the genuine
prerequisites the producer supplies). The genuinely new content is wiring the
solution's `equation` into the swap's `hTime` slot. NB `frameCompSmooth` forces
`Idx : Type` (universe-monomorphic).

**Remaining wiring:** (1) discharge `hFdiff`/`hFtdiff` (metric/Ricci frame-component
spatial `MDiff`); (2) assemble the three terms (the swap +
the two fixed-vector metric-variation terms) into
`MetricCovDerivDerivativeComponentsInFrameOnLocal_of_solution` with
`metricCovDerivDt = −2·ricciCovDerivCompInFrame`; (3) feed it (+ `hmix`, `hswap`,
the connection-pairing regularity) into the banked Christoffel evolution
(`christoffelEvolution_of_metricFrameTimeRegularity`) → curvature-coeff deriv →
`∂ₜRm04` → `iteratedRmComp_hasDerivWithinAt` → `∂ₜ∇ᵏRm`; (4) heatEq/tower.

### hFdiff obstruction (2026-06-08, /goal, 3 routes attempted)

Step (1) `hFdiff` (`MDifferentiableAt (fun y ↦ g_s(e_a,e_b)(y))`) hit a real wall —
the **metric-inner `MDifferentiableAt` is trapped in private, `∞`-section-only lemmas**:
* Route 1 — `inner_smooth_scalar` / `inner_mdiffAt_scalar` (`Curvature/.../RicciConnection.lean:393,413`):
  **`private`** and require `ContMDiff … ∞` sections; frames are C¹.
* Route 2 — `TensorMultilinear.contMDiffAt_section_apply_gen`
  (`Tensor/Multilinear/BundleSmoothEvalRealized.lean:854`): its `hv` also demands
  `ContMDiffAt … ∞` sections — same `∞` wall.
* Route 3 — the public metric-inner API (`Tensor0SBundle.continuous_inner_of_smooth_sections`,
  `continuous_g_inner_of_smooth_sections`): delivers **continuity only**, not `MDiff`.

So the foundational swap (`metricFrameComp_fixedBaseSwap_of_solution`, BUILT, axiom-clean)
takes `hFdiff`/`hFtdiff` as hypotheses precisely because no public `MDiff`-level
metric-inner lemma exists.

✅ **RESOLVED (2026-06-08): the obstruction was mechanical, not a wall — no consult.**
Built `metricInner_mdiffAt` (`Evolution/Connection/MetricCovDerivProducer.lean`, GREEN,
full build 3685 jobs): the **public** metric-inner `MDifferentiableAt` for `∞`-smooth
sections, re-proved self-contained from the public `g.contMDiff` (metric bundle
smoothness) + `ContMDiff.clm_bundle_apply` + `cotangentCov_pairing_contMDiff` — **no
edit to the core curvature file, no parallel API** (the private `inner_mdiffAt_scalar`
is genuinely inaccessible). Needs `[InnerProductSpace Real E]` + `[NeZero (finrank Real E)]`.
This discharges `hFdiff` (and, with `ricciTensor_apply_smooth` + `SolutionOn.ricciAt_eq`,
`hFtdiff`) once the producer is instantiated with the **`∞` coordinate frame**
(`coordinateFrameAt_isLocalFrame`, which meets the C¹ requirement and supplies `∞`
sections).

**Remaining (bounded plumbing):** instantiate the swap + `hFdiff`/`hFtdiff` at the `∞`
coordinate frame → assemble `MetricCovDerivDerivativeComponentsInFrameOnLocal_of_solution`
(steps 2–4 above) → the banked Christoffel/curvature/iterated `∂ₜ` chain → heatEq/tower.

### TIME SIDE — `∂ₜ∇g` producer BUILT (2026-06-08)

✅ **GREEN, full build** — `Evolution/Connection/MetricCovDerivProducer.lean`, three
landed lemmas:
* `metricInner_mdiffAt` — public metric-inner `MDifferentiableAt` (the `hFdiff` unblock).
* `metricFrameComp_fixedBaseSwap_of_solution` — the mixed `∂ₜ`/spatial swap, `hTime`
  from `IsSolutionOn.equation`.
* **`metricCovDerivDeriv_of_solution`** — discharges
  `MetricCovDerivDerivativeComponentsInFrameOnLocal` with `metricCovDerivDt =
  −2·ricciCovDerivCompInFrame` (the `−2∇Ric` Ricci-flow form). Proof = swap (term 1) +
  `equation` (terms 2,3 frozen-vector), value via `extDerivFun_const_mul` + `ring`.
  Spatial regularity (`hSmooth`/`hFdiff`/`hFtdiff`) taken `∀ a b` (dischargeable at the
  `∞` coordinate frame via `frameCompSmooth` / `metricInner_mdiffAt` /
  `ricciTensor_apply_smooth`+`ricciAt_eq`).

This is the key input (`hmetric`) to the banked **Lemma 6.2**
`christoffelEvolution_of_metricFrameTimeRegularity` → `∂ₜΓ`.

### TIME SIDE — `∂ₜΓ` (connection evolution) BUILT (2026-06-08)

✅ **GREEN, full build (3697 jobs)** — two more landed in `MetricCovDerivProducer.lean`:
* `connectionVariationBlackBox_of_solution` — discharges
  `ConnectionVariationBlackBoxInFrameOn` (its `metricCovDerivDerivative` field IS
  `metricCovDerivDeriv_of_solution`; `metricCovDerivRicciFlow` is `rfl`).
* **`christoffelEvolution_of_solution`** — `∂ₜΓ`
  (`ChristoffelEvolutionEquationInFrameOn`, `nablaRic = ricciCovDerivCompInFrame`) via
  `christoffelEvolution_of_blackBox`, with the connection black box discharged and only
  the standing `hmetricFrame` (`MetricFrameTimeRegularityInFrameOnLocal`) black box left.

KEY: `ChristoffelEvolutionEquationInFrameOn = ChristoffelVariationEquationInFrameOn`
(both are `HasDerivWithinAt (christoffelSymbolInFrame …)`, defeq with
`rhs = christoffelEvolutionRHSInFrame gInv nablaRic`), so `christoffelEvolution_of_solution`
**directly feeds** `christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`.

### Standing regularity black boxes (endpoint gaps — like the DeTurck `sorryAx`)
`MetricFrameTimeRegularityInFrameOnLocal.metricSmooth` wants `ContDiffOn ⊤` time-smoothness
on **`D.carrier`**, but the solution gives only interior (`D.regular`) `C∞` + carrier
continuity (the weakened `MetricFamilySmoothOn`). So `hmetricFrame` (and the analogous
`hmix` = `ChristoffelVariationMixedDerivativeInFrameOnRegular`, `hswap`) are **not fully
dischargeable** at the closed endpoint — they are standing regularity assumptions, carried
as hypotheses (the BBS analogue of the DeTurck short-time `sorryAx`).

**Remaining (banked realization/assembly, coordinate frame, modulo the black boxes):**
`christoffelEvolution_of_solution` (= `hvar`) + `hmix` →
`christoffelCurvCoeffAt_hasDerivWithinAt` (`∂ₜR^l_{ijk} = ∂ₜRm13`) → metric lowering →
`∂ₜRm04` (the `hrm`/`baseDt` input) → `iteratedRmComp_hasDerivWithinAt` (+ `∂ₜΓ` = `hchr`,
+ `hswap`) → **`∂ₜ∇ᵏRm`**.

### TIME-SIDE MAP COMPLETE — single frontier = Uhlenbeck base `∂ₜRm04` (2026-06-08)

The full time side reduces to **one** genuine math frontier; everything else is built/banked:

* **`hchr` (tower `∂ₜΓ` input)** = `christoffelEvolution_of_solution` at `coordinateFrameAt x₀`.
  `realizedChr S x₀ s x i a p := christoffelSymbolInFrame (conn s) (coordinateFrameAt x₀) … x i a p`
  (`RmRealizationBridge.lean:358`) is **definitionally** the LHS of
  `ChristoffelEvolutionEquationInFrameOn`. So `hchr` is my built `∂ₜΓ` specialized to the
  coordinate frame (needs `coordInv`/`gInvDt`/`hmetricFrame`/spatial-reg plumbing; goes in a
  high assembly file importing both `MetricCovDerivProducer` + `RmRealizationBridge`).
* **`hrm` (tower `∂ₜRm04` = `baseDt` input)** = `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`
  (`Uhlenbeck.lean:727`): `∂ₜRm04 = ΔRm04 + 2(B_{ijkl}−B_{ijlk}+B_{ikjl}−B_{iljk}) − ricciDrift`.
  **THE GENUINE FRONTIER (Lemma 6.1).** Route from my `∂ₜΓ`: `christoffelCurvCoeffAt_hasDerivWithinAt`
  (`∂ₜRm13`, banked) → lower (`∂ₜRm04 = δg·Rm13 + g·δRm13`) → **second-Bianchi + algebraic
  curvature computation** to hit `ΔRm04 + 2B − drift`. This last step is the substantial content.
* **Uhlenbeck pullback** `∂ₜRm04 → ∂ₜpulledRm = Δ_D Rm + 2Bpull` (moving-orthonormal frame,
  const metric) — **BANKED**: `uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow` (`Uhlenbeck.lean:987`,
  pure rearrangement of `hrm`), `uhlenbeckCurvatureEvolution_of_solution_components` (1122).
* **`∂ₜ∇ᵏRm` assembly** `iteratedRmComp_hasDerivWithinAt` (`IteratedRmTowerHeatEq.lean:430`) +
  k=1 `iteratedRmComp_one_hasDerivWithinAt` (`NablaRiemannTimeDeriv.lean:249`) — **BANKED**;
  consume `hrm`+`hchr`+`hswap`.

So: **`∂ₜΓ` built → only the Uhlenbeck base `∂ₜRm04` (the `δRm = ΔRm + Rm∗Rm` second-Bianchi
computation) remains as genuine math**; pullback + `∂ₜ∇ᵏRm` assembly are banked; `hmetricFrame`/
`hmix`/`hswap` are standing endpoint-gapped regularity black boxes.

### TIME SIDE ASSEMBLED — `∂ₜ∇ᵏRm` produced (2026-06-08, GREEN, axiom-clean)

Three new producers (all `#print axioms` = `propext/Classical.choice/Quot.sound`, no `sorryAx`):

* `Connection/Rm13DerivProducer.lean` — **`rm13Deriv_of_solution`** (`∂ₜRm13`): feeds
  `christoffelEvolution_of_solution` (= `hvar`) + `hmix` into
  `christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`. (build 3698)
* `Connection/NablaKRmTimeDeriv.lean`:
  - **`realizedChr_hasDerivWithinAt`** — `∂ₜΓ` as the tower `hchr` input (defeq:
    `realizedChr = christoffelSymbolInFrame (coordinateFrameAt x₀)`, so it's
    `christoffelEvolution_of_solution` directly).
  - **`nablaKRm_timeDeriv_of_solution`** — **the assembled BBS time side**: for every level
    `k`, `∂ₜ(iteratedRmComp … k) = iteratedRmCompDt …` at the frame centre `x₀`, via
    `iteratedRmComp_hasDerivWithinAt` with `hchr` **discharged** from my `∂ₜΓ`. (build 3738)

The time side is now a **complete named producer** `∂ₜ∇ᵏRm`. `∂ₜΓ` is genuinely computed from
the Ricci-flow PDE (`∂ₜg = −2Ric`). The remaining analytic content is isolated as **two explicit
standing inputs** (not hidden): `hrm` = the Uhlenbeck base `∂ₜRm04`
(`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, Lemma 6.1, the `δRm=ΔRm+Rm∗Rm` second-Bianchi
computation — the single genuine math frontier), and `hswap` (time/space derivative commutation).
These join `hmetricFrame`/`hmix` as the project's standing black boxes (the BBS analogue of the
DeTurck short-time `sorryAx`).

### Honest scope of `extends_of_rmBounded` (the /goal target)

It is the WHOLE BBS pillar — ~8 substantial bricks beyond the gate, genuinely
multi-session: (1) finish route-4 bundled `∇(curvatureAction)`; (2) the `StarSum2`
class; (3) Uhlenbeck base `∂ₜRm=ΔRm+Rm∗Rm`; (4) time recursion `E_k∈StarSum2`;
(5) frame reconciliation; (6) `IteratedRmTowerOn` assembly; (7) `CinftyLimitData`
C∞-convergence wiring from the BBS bounds; (8) final `extends_of_rmBounded`
assembly via `ricci_flow_extends_construction` — which itself carries the DeTurck
short-time `sorryAx` (a legitimate deep-PDE black box). The gating theorem
(curvature-action Leibniz) is no longer a 3-routes-wall: route 4 is built at the
foundation and viable.

Verification status: `NablaTraceGen.lean` focused-checks (EXIT 0);
`StarSum/ProductLeibniz.lean` unchanged (still focused-checks). No new public
*theorem* yet (only the `freezeTailField` def + `rfl` apply lemma), so the axiom
sweep is pending the target theorem.

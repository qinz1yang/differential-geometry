# MetricCovDerivBridge — the `normBridge` design note (item-6 brick 2a, D2)

Ratified home (planner, 2026-07-24) for the reusable norm bridge

```
normBridge (h gBase : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
  ‖(iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h)).toSection x‖
    = Real.sqrt (normSq0S gBase x (j+2) (metricCovDeriv h gBase j x))
```

that lets `UnifCurvatureJetBound.lean`'s order-`≤2` jet envelope consume
`MetricCovDerivOrderBoundOn` (which is stated in `normSq0S`/`metricCovDeriv`
currency).

## SESSION 9 (2026-07-24, executor e87b): SECOND GATE found, then dissolved; clean route

Discharging the sorry surfaced a **second** gate the session-8 recipe missed, and a
cleaner overall route that dissolves it.  Durable findings:

### The norm half (b) is NOT the chain the session-8 note claimed.
The RS-bundle norm `‖W.toSection x‖` (with the `tensorRS_riemannianBundle` instance)
reduces, via `norm_toSection_eq_sqrt_riemannianFiberNormSq` →
`riemannianFiberNormSq_eq_tensorInnerPointwise`, to `tensorInnerPointwise_0s` (the
**chart-model** fibre inner, `gramMatrixAt⁻¹` on `chartModelBasis E`).  But
`normBridge`'s RHS `normSq0S = inner0S` is the **intrinsic** recursive fibre inner
(`tensor0SMetricData`).  These are TWO parallel `(0,s)`-inner APIs with **no
identification lemma anywhere in the tree** (exhaustively grep-verified;
`Tensor0SMetricContinuity.md:74` documents it as a deferred shim).  So the
session-8 claim "half (b) UNBLOCKED via `tensorInnerPointwise_0s … = inner0S`" was
wrong — that bridge does not exist.

### The clean route (avoids a per-step cast; isolates ONE tractable new bridge).
`metricCovDerivNorm N h gRef x` (`AllTimesBounds.lean:661`) is *by definition*
`√normSq0S gRef x (N+2) (metricCovDeriv h gRef N x)` = `normBridge`'s RHS.  And
`MetricCovDerivArityBridge.metricCovDerivNorm_eq_iterCov` already proves, at a
`gRef`-orthonormal basis, `metricCovDerivNorm N h gRef x =
√normSq0S gRef x (2+N) (iterCov gRef 2 (metricTensorField h) N x)`.  So the RHS is
`√normSq0S gBase x (2+j) (iterCov gBase 2 (metricTensorField h) j x)` — arity `2+j`,
matching the RS tower's `2+j`.  **No `2+j = j+2` cast is needed in the tower match**
(the cast lives entirely inside `metricCovDerivNorm_eq_iterCov`, already discharged).

Remaining obligations, both tractable:
- **(A) tower match (no cast):** `(iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h)).toSection x (unitZeroSec x) = iterCov gBase 2 (metricTensorField h) j x`, by induction on `j`.
  - base `j=0`: `(metricCcTensor gBase h).toSection x unit = metricTensorField h x = iterCov … 0 x`.
  - step: `iteratedCovGrad_succ` → `curry_covGrad_unit_eval_genVal` → `tensorCovDerivAt = tensorRSCovariantDerivative` → `covDeriv_unit_eval_eq_genVal` → field-IH rewrite → `nabla0SFun_eq_tensor0SCovariantDerivative` (the resolved agreement, reversed) → `totalNabla0SFun_apply_section` (= `covStep`/`iterCov_succ`).  Every tuple is `Fin.cons (v 0) (vecTail v)`, closed by `ContinuousMultilinearMap.ext`.
- **(B) fibre-inner bridge (the real new content):** `riemannianFiberNormSq gBase 0 s x (W.toSection x) = normSq0S gBase x s (W.toSection x unit)` for `W : SmoothCcTensor gBase 0 s`.  Route: pick a `gBase(x)`-ON basis `frame` (`exists_gOrthonormalBasis`); expand LHS by `riemannianFiberNormSq_eq_tensorInnerPointwise` + `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame` (`RiemannianFiberNormSqTensorInnerBridge.lean:391`) and RHS by `normSq0S_identity_eq_sum_sq` (`Tensor0SMetric.lean`, used at `MetricCovDerivArityBridge.lean:179`) — both become `∑_φ (component in `frame`)²`; components match through the `toModel`/`lowerAllUpperIndices (r=0)` evaluation identity (`TangentSpace I x = E` defeq).  Kept as a private lemma in this file (correct layer would be `FiberMetric/`; planner may relocate).

Status: **(A)+(B) IMPLEMENTED, sorry removed.**  `MetricCovDerivBridge.lean` now proves
`normBridge` outright.  New private helpers in the file:
- `iterCovGrad_unit_eq_iterCov` — the tower match (A), induction on `j`; succ step uses
  `covGrad_apply_unit_eval_genVal` → `tensorCovDerivAt_def` → `covDeriv_unit_eval_eq_genVal`
  → `ih` (field rewrite) → `nabla0SFun_eq_tensor0SCovariantDerivative` (the agreement) →
  `iterCov_succ`/`covStep_apply`/`totalNabla0SFun_apply_section`, closed on
  `LeviCivita = leviCivitaConnectionOfMetric` (rfl).  Base = `ccTensorMultilinear_apply`
  + `metricCcTensorFib_apply` = `metricTensorField_apply`.
- `lowerAllUpper_zero_eq_unit` — the `r=0` index-lowering crux (replica of the private upstream
  `lowerAllUpperIndices_zero_apply_unitModel`), via `lowerAllUpperIndices_apply` +
  `separableFormAt_zero` + `toModel_tensorRS_apply` + `rfl`.
- `rfns_eq_normSq0S_unit` — the fibre-inner bridge (B): both sides expanded in one `gBase`-ON
  frame (`exists_gOrthonormalBasis`), model side by `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`,
  intrinsic side by `normSq0S_identity_eq_sum_sq`; matched by `Fintype.sum_equiv` over
  `arrowCongr (finCongr (zero_add s).symm)` + the crux + `Fin.ext`.

Verification: **COMPLETE.**  Authoritative `lake build`: "Build completed successfully (9582 jobs)".
Axiom audit (verbatim): `'DifferentialGeometry.PDE.RicciFlow.normBridge' depends on axioms:
[propext, Classical.choice, Quot.sound]` — sorryAx GONE, exact clean triple.  Final focused
`lake env lean` after stripping the audit line + docstring refresh: exit 0, no error/sorry/warning.

KEY LESSON (this session): the whole envelope stays in `normSq0S`/`iterCov` currency — the
`2+j = j+2` cast never enters the tower match (already discharged inside
`metricCovDerivArityBridge.metricCovDerivNorm_eq_iterCov`), so the tower match is at uniform
arity `2+j`.  The genuinely new content was the fibre-inner bridge (B), NOT a false wall:
`Tensor0SSpace.toModel` is `id` on the carrier (rfl) and `TangentSpace I x = E` defeq, so the
existing orthoFrame diagonal-sum lemmas made both norms `∑_φ (component)²`.  Main Lean friction:
`show …→L… from` elaborates to a `have`-wrapper that blocks `rw` (fix: `change` to plain FunLike,
or keep the wrapper to match the target lemma); toModel-based `_apply_eval` lemmas are handled by
routing through `Tensor0SSpace.toModel_injective` + `ContinuousMultilinearMap.ext`.

## GATE RESOLVED (2026-07-24): the upstream agreement is now PROVED

The missing `nabla0SFun ↔ tensor0SCovariantDerivative` `(0, s)` agreement (the framework
gate below) is **landed, sorry-free, axiom-clean**:

```
DifferentialGeometry/Geometry/Connection/ChartTensorNabla/Agreement/Nabla0SFunAgreement.lean
  nabla0SFun_eq_tensor0SCovariantDerivative (g s X α x) :
    nabla0SFun s (LeviCivita g) X α x
      = tensor0SCovariantDerivative I M s (LeviCivita g) (fun y => α y) x (X x)
```

Axiom audit: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  It was proved by a
cleaner route than either sketched below: both sides have a closed intrinsic smooth-slot
form (`nabla0SFun_eval_smooth_slots` and the new abstract Leibniz rule
`abstractDerivEval_aux`), which match verbatim — no `chartTensor0S`, no chart/Christoffel
bookkeeping.  See `Nabla0SFunAgreement.md`.

**`normBridge` is therefore no longer gated on a missing agreement.**  What remains to
discharge `normBridge`'s sorry is the *tower + norm assembly* (still a real, separate,
multi-step effort — NOT attempted this session, so the honest documented `sorry` at
`MetricCovDerivBridge.lean` is left in place rather than relocated):

- **(a-step) tower match** `iteratedCovGrad`/`covGrad` (abstract) ↔ `metricCovDeriv`/nabla.
  My agreement bridges the *pointwise directional* step; the tower step additionally needs
  `iteratedCovGrad_succ` + `covGrad` unit-eval (`curry_covGrad_unit_eval_genVal`,
  `covDeriv_unit_eval_eq_genVal`) on one side and `metricCovDeriv_succ_apply_section`
  (`HCGCompactness/MetricCovDerivCoordStep.lean:43`, already `nabla0SFun`-based) on the
  other, glued by `nabla0SFun_eq_tensor0SCovariantDerivative`, plus the `2+j = j+2` HEq
  cast.
- **(a-base) `j = 0`** derivative-free (as mapped below).
- **(b) norm reconciliation** chain (as mapped below), independent of the gate.

Wiring: `import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement`
into `MetricCovDerivBridge.lean` (no cycle; the agreement is upstream of HCG).

## HEADLINE (session 8 recon, now SUPERSEDED by the gate resolution above): the original gate analysis

The two sides of `normBridge` live in **two different covariant-derivative
formalisms**, and the crossing between them is a repeatedly-flagged MISSING bridge:

- **Envelope side (LHS) — ABSTRACT.**  `iteratedCovGrad`/`covGrad` differentiate
  via the bundled Mathlib `tensor0SCovariantDerivative` / `tensorRSCovariantDerivative`
  (`Geometry/Connection/TensorNabla/Tensor0SNabla.lean:493`, recursive Hom-bundle
  construction).  This side is fully bridged *internally*:
  `Tensor0SRSCovariantDerivativeAgreement.lean` (`tensor0SCovariantDerivative ↔
  tensorRSCovariantDerivative 0 s`, all `s`), `covDeriv_unit_eval_eq_genVal`,
  `curry_covGrad_unit_eval_genVal` (`Curvature/CovGradRoughLap/GradientField.lean`).
- **`metricCovDeriv` side (RHS) — CHART / MODEL.**  `metricCovDeriv`
  (`PointedConvergence.lean:80`) iterates `metricCovDerivStep = totalNabla0S`
  (`Tensor/RSTensor/NablaOnTensors/HigherOrder.lean:156`), whose pointwise value is
  `nabla0SFun` (`Tensor/RSTensor/Derivation/NablaOnTensors.lean:987` =
  `mcovariantDeriv_tensor0SFromConnection`, built by trivializing to the model and
  reading `connectionEndomorphismInChartL`).  EVERY `metricCovDeriv` eval lemma
  (`metricCovDeriv_one_apply_section`, `_eval_smooth_slots`, `_eval_localFrame`) is
  `nabla0SFun`-based.

**The crossing `nabla0SFun ↔ tensor0SCovariantDerivative` (chart ↔ abstract) is NOT
proved for `(0, s)` tensors** and is a repeatedly-flagged framework frontier:
`Evolution/NablaRiemannT1Bound.lean:75-76`, `Evolution/IteratedNablaRmTower.md:729,
748, 777, 868` (these flag it "at rank `r ≥ 1`"; the **`r = 0` case is simply absent** —
`nabla0SFun` occurs NOWHERE in the whole `Connection/ChartTensorNabla/` agreement tree).
The proven chart↔abstract agreement there is for a DIFFERENT chart construction,
`chartTensor0SCovariantDerivative` (`Agreement/ChartTensor0SCovariantDerivativeAgreement*.lean`,
base + succ, sorry-free), which has **no stated link to `nabla0SFun`**
(`chartTensor0SCovariantDerivative ≠ nabla0SFun`; independent chart machineries).

This corrects the session-7 optimism ("single frontier = assembly"): the true gate is
this missing agreement, not a mere index-cast.  No convention/slot-order/connection
mismatch (all resolved session 7); the gate is a **formalism-bridge** gap.

## The smallest unblocking lemma (propose to an upstream lane — outside this editable set)

```
nabla0SFun_eq_tensor0SCovariantDerivative     -- (r = 0, all s), directional
  (g : SmoothRiemannianMetric I M) (s : ℕ)
  (X : ContMDiffSection I E ∞ (TangentSpace I))
  (α : Tensor0SField … s)        -- smooth
  (x : M) :
  nabla0SFun s (LeviCivita g) X α x
    = tensor0SCovariantDerivative I M s (LeviCivita g) α x (X x)
```

Home: `Geometry/Connection/ChartTensorNabla/Agreement/` (beside the proven
`chartTensor0SCovariantDerivative_eq_abstract_{zero,succ}`).  Feasibility: **plausible**
— it is the `nabla0SFun` analogue of the already-proven `chartTensor0S` agreement; the
likely route is either (i) `nabla0SFun = chartTensor0SCovariantDerivative` (both concrete
chart `∂ + Γ` derivatives with the same LeviCivita Christoffel) then chain the existing
agreement, or (ii) a direct induction on `s` mirroring `…AgreementSucc.lean`.  Either is a
NEW multi-lemma effort in the Connection layer.  NOT attempted here (editable set =
`MetricCovDerivBridge.{lean,md}` + `UnifCurvatureJetBound.{lean,md}`).

Once that lands, `normBridge` is the assembly below (all pieces cited/confirmed).

## `normBridge` assembly plan (everything EXCEPT the gate is confirmed present)

Let `T_j := iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h) : SmoothCcTensor gBase 0 (2+j)`.

- **(b) norm reconciliation [UNBLOCKED — landing this session].**
  `‖T.toSection x‖ = √(normSq0S gBase x s (T.toSection x (unitZeroSec x)))` for any
  `T : SmoothCcTensor gBase 0 s`.  Route: `norm_toSection_eq_sqrt_riemannianFiberNormSq`
  (`Sobolev/TensorHilbert/MetricArmCoeffJetTower.lean:904`) →
  `riemannianFiberNormSq_eq_tensorInnerPointwise` → the RS↔0S fibre-inner bridge
  `tensorInnerPointwise_0s … = inner0S` (`Geometry/Metric/TensorInner/…`,
  `Tensor0SMetricContinuity.md:82`) → `normSq0S_eq_inner`
  (`Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean:459`).
- **(a) tower match [base UNBLOCKED; step GATED].**
  Need `T_j.toSection x (unitZeroSec x) = cast_{2+j = j+2} (metricCovDeriv h gBase j x)`.
  - Base `j = 0`: `metricCovDeriv h gBase 0 = metricTensorField h` (`PointedConvergence.lean:184`,
    rfl); `(metricCcTensor gBase h).toSection x (unit) = metricCcTensorFib h x` (via
    `metricCcTensor_apply` machinery); `metricCcTensorFib h x = metricTensorField h x`
    (both `h.inner`, `metricCcTensorFib_apply` = `metricTensorField_apply`).  **Derivative-free —
    no gate.**
  - Step `j → j+1`: `iteratedCovGrad_succ` → `covGrad` → (unit-eval) abstract
    `tensor0SCovariantDerivative` (via `curry_covGrad_unit_eval_genVal` +
    `covDeriv_unit_eval_eq_genVal`) vs `metricCovDerivStep = totalNabla0S`/`nabla0SFun`.
    **Closing this step is exactly the `nabla0SFun ↔ tensor0SCovariantDerivative` GATE.**
    HEq: the `2+j` vs `j+2` index cast is handled by a small `Nat.add_comm`/`heq`-congr
    lemma (cf. `CovGrad/CovariantBilinearLeibniz.lean:100 norm_toSection_heq_congr`).

Then `normBridge = (b) ∘ (a)` with the cast lemma.

## Envelope assembly (back in `UnifCurvatureJetBound.lean`, after `normBridge`)

- Linearity split `metricDiff_iterCovGrad_sub` (LANDED session 7).
- `j ≥ 1` self-zero of the `metricCcTensor gBase gBase` tower: from `normBridge` +
  `metricCovDeriv gBase gBase j = 0` (build from `nabla_metric_zero`,
  `Tensor/RSTensor/MetricCompatibility.lean:117`); ⟹ the `j≥1` difference terms `=
  √normSq0S(metricCovDeriv g₀ gBase j) ≤ Λ` from `MetricCovDerivOrderBoundOn`.
- `j = 0` term: `‖metricDifferenceCcTensor.toSection x‖ = √riemannianFiberNormSq`
  bounded `≤ finrank·(Λ−1)` from Discharger-1's op bound (Parseval / `_eq_coord`).
- **Pinned `c₀(n) = finrank ℝ E = n`; `B(Λ) = n·(Λ−1) + 2Λ`.**

## Status
- 2026-07-24 (session 8): recon of the two derivative formalisms COMPLETE.  **Gate
  found: `normBridge` requires the missing upstream `nabla0SFun ↔
  tensor0SCovariantDerivative` (r=0) agreement.**  Half (b) confirmed unblocked
  (`norm_toSection_eq_sqrt_riemannianFiberNormSq` + `tensorInnerPointwise_0s` +
  `normSq0S_eq_inner`); base case (j=0) confirmed derivative-free.
  - **LANDED:** the `normBridge` STATEMENT (`MetricCovDerivBridge.lean:88`), pinned and
    typechecked; proof = ONE documented `sorry` at the gate, nothing else.  `lake build`:
    `Built …MetricCovDerivBridge`, "Build completed successfully (9417 jobs)", EXIT=0.
    Axiom audit (verbatim, INTENTIONALLY not stripped — the honest frontier marker):
    `'DifferentialGeometry.PDE.RicciFlow.normBridge' depends on axioms:
    [propext, sorryAx, Classical.choice, Quot.sound]`.
  - Instance note: the LHS `Norm (TensorRSSpace 0 (2+j))` needs
    `set_option synthInstance.maxHeartbeats 1600000` + the FULL 4-instance
    `attribute [-instance]` removal (`tensorRSSpace_normedAddCommGroup/…normedSpace` +
    `Bundle.continuousMultilinearMap.mixed_inst…`), mirroring `RealizedJet2CovGradBound`.
    `lake env lean` FALSE-GREENED this (cached instance); only `lake build` caught the
    synthesis timeout.
  - NEXT (separate planner dispatch): the upstream agreement
    `nabla0SFun_eq_tensor0SCovariantDerivative` (r=0), then discharge the `sorry` (base +
    step + cast + half (b)), then the envelope assembly + `j=0` Parseval bound back in
    `UnifCurvatureJetBound.lean`.  Single-link / 2a-tel distance unchanged (blocked behind
    the gate).

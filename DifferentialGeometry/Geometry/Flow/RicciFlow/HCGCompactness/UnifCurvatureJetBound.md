# UnifCurvatureJetBound — brick (2a) design note (item-6 S1 gate)

Session 3 recon (Opus 4.8, LANE C) in worktree
`C:/Users/liao9/.codex/worktrees/e87b/...`, branch `codex/analytic-producers-e87b`.
**No `.lean` written this session** (see §6 for why — two design-gating findings
need planner ratification before a build commits).  This is the design note for
the FUTURE leaf `HCGCompactness/UnifCurvatureJetBound.lean`.

## Target (planner-ratified brick 2a, order-generic)

`MetricCovDerivOrderBoundOn Set.univ (≤ b+2) g₀ gBase Λ` + `Λ`-comparability ⟹
`sup_x ‖∇^{g₀,a} Riemann(g₀)‖_{g₀} ≤ F(Λ, n)` for every `a ≤ b`, in the currency
`ccR/ccdR` consume (the appFullSec window sups of the Riemann hom-fields `H_R`,
`H_dR` — `PointwiseTensorCurvFirstOrderSection.lean:1444`, built from
`gradArmSection`/`diffArmSection`, i.e. from `Riemann(g₀)` and `∇Riemann(g₀)`).
`UnifBochnerGap.lean` (S1) plugs this into `K 0 = √(2·ccR 0 + 2·ccdR 0)` and the
commutator `Cfun` (audit §7.2 of `UNIF_ITEM6_RECON.md`).

## FINDING A (de-risking) — (2a) is an ASSEMBLY of existing jet-envelope machinery, NOT a missing layer

The curvature-difference + connDiff jet-envelope estimates already exist:

- `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`
  (`Geometry/Curvature/PerturbedRiemannOpDifferenceBound.lean:88`): for
  `g₁ = g₀ + P` with `∑_{j<3}‖∇^{g₀,j}P‖ ≤ B` and `gFibreOpBound g₀ (…P) δ`,
  `δ ≤ δ₀ < 1`, gives `‖Riemann(g₁) − Riemann(g₀)‖²_{g₀} ≤ C(δ₀,B)²·|v|²|w|²|u|²`,
  `C = √(2·CA + 2·C0²B²)`.  **This is the order-0 curvature difference** (I had
  wrongly listed it "missing" in the session-1 recon).
- `exists_norm_covGrad_connDiffSection_le_of_jetEnvelope`
  (`Geometry/Curvature/CovDerivConnDiffQuadraticBound.lean:43`): the connDiff
  order-1 covGrad bound from the same jet-envelope.
- `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope`,
  `connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one`,
  `rfns_raisedKoszul_le_of_lt_one`, … (same file family) — the Koszul /
  Christoffel-difference building blocks.
- HCG layer: `CurvDerivBoundOn` / `CurvDerivBoundsOnWindow`
  (`AllTimesBounds.lean:3556/3572`) is a curvature-derivative bound predicate
  ALREADY paired with `MetricCovDerivOrderBoundOn` (Lemma 3.11 content, `:3760`);
  `normSqRS_connDiff_eq_componentL2Sq3` relates connDiff to metric-jet components
  in the `MetricCovDerivOrderBoundOn` context (`AllTimesBounds.lean:1975/2473`).
- The Christoffel-difference tensor `A = connDiff g₁ g₀` with the Koszul identity
  `2g₁(A(X,Y),Z) = (∇⁰g₁)(Y,Z)+(∇⁰g₁)(X,Z)−(∇⁰g₁)(Z,·)`
  (`ChristoffelDifferenceKoszul.lean:105 connDiff_koszul`).

So the mathematical content of (2a) exists; (2a) is assembling it at the g₀/gBase
pair under the class hypotheses — **modulo the two gating findings below.**

## FINDING B (gating, scope-changing) — the machinery is SMALL-PERTURBATION only (`Λ < 2`)

`gFibreOpBound g h δ` (`PosDefPerturbation.lean:70`) is the **g-operator-norm**:
`|h x v w| ≤ δ·√(g v v)·√(g w w)`.  The whole difference chain requires
`δ ≤ δ₀ < 1` (the `_of_lt_one` family).  For the (2a) role-assignment
base = gBase, `P = g₀ − gBase`, `Λ`-comparability `(1/Λ)gBase ≤ g₀ ≤ Λ·gBase`
gives `gBase`-op-norm `|g₀ − gBase|_{gBase-op} ≤ Λ − 1`, and `≥ Λ − 1` from the
upper side.  So `δ = Λ − 1`, and `δ < 1 ⟺ Λ < 2`.  Basing at g₀ instead gives the
same `Λ − 1`.  **The existing curvature-difference machinery covers only `Λ < 2`,
not the full class `Λ ≥ 1`.**

Resolution options for the full class (planner design choice):
- **(a) Telescoping chain (recommended).**  Interpolate `g_t = (1−t)gBase + t·g₀`,
  sample `t₀=0 < t₁ < … < t_N=1` with each link `|g_{t_{k+1}} − g_{t_k}|_{g_{t_k}-op}
  < 1`.  Since op-speed `≈ Λ−1`, need `N ≈ Λ` links.  Apply the order-0 asset per
  link, compose curvature differences by triangle.  Each `g_{t_k}` is a convex
  combo, so its `∇^{gBase}`-jets and its comparability are bounded by those of
  `g₀,gBase` (Λ-controlled); the composed constant is `F(Λ,n)` (poly/exp in `Λ`,
  fine for a bound).  Reuses the existing bounds as black boxes.  ~1–2 sessions.
- **(b) Large-δ re-derivation.**  General-`δ₀` analogs of the `_of_lt_one`
  lemmas.  The `1/(1−δ₀)` factors (`CovDerivConnDiffQuadraticBound:72
  s0 = finrank²·(1/(1−δ₀))²`) stay finite for `δ₀ = 1−1/Λ` (`= Λ`), so the
  algebra likely survives — but it touches many committed `_of_lt_one` lemmas
  (churn / statement-risk).  Not recommended.

## FINDING C (layering, changes S1's interface)

`MetricCovDerivOrderBoundOn` lives in `HCGCompactness/AllTimesBounds.lean`, which
is **downstream** of `Analysis/` (where S1's `UnifBochnerGap.lean` lives).  So S1
CANNOT import a bridge stated in `MetricCovDerivOrderBoundOn` terms without an
import cycle.  Correct design (mirrors the plan's `forward_ode2_of_bound` /
item-4 abstraction):

- **S1 (`Analysis/…/UnifBochnerGap.lean`)** takes the curvature-jet bound as an
  ABSTRACT hypothesis bundle `hcurv : ∀ a ≤ b, sup_x ‖∇^{g₀,a}Riemann(g₀)‖ ≤ Fc a`
  (in the ccR/ccdR-consumable currency), and produces the Λ-uniform Gårding
  constant `F(Λ,n)` as a functional of `Fc`.
- **(2a) (`HCGCompactness/UnifCurvatureJetBound.lean`, downstream)** discharges
  `hcurv` from `MetricCovDerivOrderBoundOn Λ` at the (N)-assembly level.

This **corrects `UNIF_ITEM6_RECON.md §5`**: S1's home stays `Analysis`, but it
consumes the curvature bound abstractly; (2a)'s home is `HCGCompactness` (beside
the `MetricCovDeriv*` bridges), importing the `Geometry/Curvature/` difference
assets (upstream of HCG, so importable).

## FINDING D (currency + order budget)

- Jet-envelope currency: the asset's `B` bounds `∑_{j}‖∇^{g₀,j}P‖` (the **g₀**
  connection).  `MetricCovDerivOrderBoundOn` bounds `‖∇^{gBase,j}g₀‖` (the
  **gBase** connection).  Bridge: `∇^{gBase,j}gBase = 0` for `j ≥ 1`
  (metric compat) ⟹ `∇^{gBase,j}P = ∇^{gBase,j}g₀` for `j≥1`; then convert
  `∇^{gBase}` ↔ `∇^{g₀}` via `connDiff` (a bounded, Λ-controlled conversion).
  Net: envelope `B ≤ F(Λ, metricCovDeriv jets ≤ Λ)`.  Real but bounded.
- Order: the assets are **order-0** (`riemannOp` difference) and **order-1**
  (connDiff covGrad).  (2a) needs `∇^{g₀,a}Riemann` for all `a ≤ b`.  Higher
  orders need iteration: `∇^{g₀}` of the curvature difference, converting slots
  via connDiff and re-applying — an extension of the order-0 asset the current
  file does NOT provide.  Per audit §7.4, `b` runs to `≈ a+2` (top order), so
  metric jets to `≈ A(n)+2` are consumed (order-generic statement, no hardcode).

## Sub-brick decomposition (2a)

- **2a-abs** [Analysis, landable now]: the abstract `hcurv` interface in
  `UnifBochnerGap.lean` — S1 consumes the curvature-jet bound as a hypothesis.
  This is really S1 scaffolding (Finding C); flag to planner.
- **2a-0** [HCG, Λ<2]: `sup_x‖Riemann(g₀)‖ ≤ F(Λ)` in the small-perturbation
  regime, from the order-0 asset (base=gBase, P=g₀−gBase) + fixed `Riemann(gBase)`
  sup + the Finding-D envelope bridge.  First concrete landable HCG lemma.
- **2a-tel** [HCG]: telescoping to full `Λ` (Finding B option a).
- **2a-hi** [HCG]: higher orders `∇^{g₀,a}Riemann`, `a ≤ b` (order-generic
  iteration; needs the higher-order curvature-difference extension).
- **2a-pkg** [HCG/Curvature]: package `sup‖∇^a Riemann‖` into the `H_R/H_dR`
  appFullSec window-sup currency (2b).

## Smallest first Lean brick + recommendation

Two candidates, planner to pick:
1. **2a-abs** (in `Analysis/…/UnifBochnerGap.lean`): the abstract curvature-jet
   hypothesis interface + the Λ-uniform Gårding-constant functional.  Landable in
   `Analysis` NOW (no downstream dep), unblocks all of S1 independent of the
   Λ<2 / telescoping question, and is mandated by the Finding-C layering.  **This
   is the highest-value first brick** — it lets S1 proceed while (2a) proper is
   built downstream.
2. **2a-0** (in `HCG/UnifCurvatureJetBound.lean`): the order-0 Λ<2 curvature sup.
   Concrete (2a) progress but blocked behind the telescoping design choice
   (Finding B) for the full class and the envelope bridge (Finding D).

Recommendation: ratify **Finding C** (S1 takes curvature abstractly) and dispatch
**2a-abs** first (unblocks S1), then **Finding B option (a)** for 2a-tel, then
2a-0/2a-hi/2a-pkg.  Before 2a-0, confirm the telescoping route and the
`g₀`↔`gBase` envelope-connection bridge (Finding D) are acceptable.

## Session 10 (2026-07-24, LANE C, Opus) — 2a-tel (a) LINK LEMMAS; moving-base currency is the block

Mission: extend `unifCurvatureSup_singleLink` (Λ<2) to the full class `Λ ≥ 1` by `convexComb`
telescoping.  OUTCOME: the two **(a) link lemmas** are landed (comparability + fixed-`gBase`
jet inheritance); the composition (b) to the full class is NOT closed — it needs the metric
jets against the MOVING base `g_{t_k}` (`k ≥ 1`), the order-`≤2` change-of-reference-connection
currency, a declared frontier of the ACTIVE lane `UnifCovSumCross.lean` plus an ungated
`∇connDiff` bound.  This is the STOP condition the plan flagged for (a)(ii).

### LANDED in `UnifCurvatureJetBound.lean` (leaf; new import `Geometry.Metric.ConvexCombination`)
- **`convexCombPath g₀ gBase t ht`** (def) `= convexComb g₀ gBase (fun _ => t) …`: the path
  `g_t = t·g₀ + (1−t)·gBase`, `t=0 ↦ gBase`, `t=1 ↦ g₀`.  `convexCombPath_inner`: fibre
  `= t·g₀.inner + (1−t)·gBase.inner`.
- **`convexCombPath_comparable`** (a)(i): `|g_t(v,v) − g_s(v,v)| ≤ |t−s|·Λ(Λ−1)·g_s(v,v)` from
  `Λ`-comparability of `g₀/gBase`.  Two-sided `(1±μ)` link comparability, `μ = |t−s|·Λ(Λ−1)`,
  link constant `Λ_link = (1−μ)⁻¹ < 2` when `μ < ½`, i.e. `N ≈ 2Λ(Λ−1)` equal links each land
  in the single-link `< 2` regime.
- **`metricTensorField_convexCombPath`** / **`metricCovDeriv_convexCombPath`(`_succ`)**:
  `metricCovDeriv` is linear in the metric argument at fixed reference (`metricCovDeriv =
  covDerivOfField ∘ metricTensorField`, `covDerivOfField_add/_smul`), so `∇^{gBase,a} g_t =
  t·∇^{gBase,a} g₀ + (1−t)·∇^{gBase,a} gBase`; for `a+1` the `gBase`-tower vanishes
  (`covDeriv_self_succ`) leaving `t·∇^{gBase,a+1} g₀`.
- **`convexCombPath_jetBound`** (a)(ii): `MetricCovDerivOrderBoundOn (a+1) g₀ gBase Λ ⟹
  MetricCovDerivOrderBoundOn (a+1) g_t gBase Λ` (`‖∇^{gBase,a+1} g_t‖ = |t|·‖∇^{gBase,a+1} g₀‖
  ≤ Λ`, `sqrt_normSq0S_smul`).  **Exactly discharges the FIRST link's jets (base = gBase).**

Verification: **GREEN, axiom-clean** (resumed 2026-07-25 once the concurrent lane's marathon
cleared).  `lake build …HCGCompactness.UnifCurvatureJetBound` EXIT=0, "Build completed
successfully (9654 jobs)".  `#print axioms` on all five public names (`convexCombPath`,
`convexCombPath_comparable`, `metricCovDeriv_convexCombPath`, `metricCovDeriv_convexCombPath_succ`,
`convexCombPath_jetBound`) = **`[propext, Classical.choice, Quot.sound]`** exactly — no `sorryAx`.
Two elaboration fixes were needed: `le_or_lt`→`le_total`+sign-split in `convexCombPath_comparable`,
and the section-eval `(t•F) x` in `convexCombPath_jetBound` (`simp only [ContMDiffSection.coe_smul,
Pi.smul_apply]`, the idiom the leaf's `metricDiff_orderPos_bound` uses for `coe_sub`); all other new
declarations (incl. the `metricTensorField` double-`DFunLike.ext` and the `covDerivOfField` rw
chain) elaborated clean on first pass.  `git diff` of the `.lean` = exactly the +1 import and the
+149-line block — no diamond-lane edits mixed into this file (the lane's uncommitted
`Defs.lean` / `TensorRSContRiemannianBundle.lean` edits are upstream and not ours).

### WHY (b) does not close — the moving-base currency (recon this session)
Single-link at link `k = (g_{t_k}, g_{t_{k+1}})` needs `MetricCovDerivOrderBoundOn 1/2
g_{t_{k+1}} g_{t_k} Λ_link` — jets against the MOVING base `g_{t_k}`.  For `k=0` (base `=gBase`)
these ARE the fixed-`gBase` jets that `convexCombPath_jetBound` discharges.  For `k≥1` the
reference `g_{t_k} ≠ gBase` is a different connection.  It is NOT shortcuttable: the single-link
curvature output is uniform ONLY if `Kbase` is chained from `gBase` forward
(`exists_uniform_riemannOp_LeviCivita_gNorm_bound g` is an UNCONTROLLED per-metric existential),
so the base must move, so the jets are moving-base.  Recon verdict (exhaustive subagent):
- change-of-reference IDENTITY exists, all orders, ungated: `iterCov_telescoping`
  (`MetricCovDerivLinear.lean:421`), bridged via `covDerivOfField_eq_iterCov`
  (`MetricCovDerivArityBridge.lean:66`);
- order-1 norm bound exists, ungated: `diffStep_norm_le` (`UnifCovSumCross.lean:324`);
- order-0 `connDiff` comparability bound exists, ungated: `connDiff_le_covOne`
  (`AllTimesBounds.lean:2298`) / `lcDiff_norm_le` (`MetricLapDiff.lean:164`),
  `‖connDiff(h,g)‖ ≤ (3/2)√(C³)·metricCovDerivNorm 1 h g x`;
- **GAPS (both needed for a=2, which single-link also consumes):** (i) the assembled order-`≥2`
  iterated change-of-connection norm bound — a DECLARED frontier being actively built in
  `UnifCovSumCross.lean:24,270–275` (do not touch); (ii) an ungated `∇connDiff` bound (only the
  `δ<1`-gated `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope` exists;
  `covDerivConnDiff_g1inner_eq_secondCovGrad_lowerArms`,
  `ConnectionDifferenceJetTower.lean:387`, is the nearest ungated starting identity).

`unifCurvatureSup` is therefore NOT stated: a top-level `sorry` would hide a whole missing
layer, and taking the moving-base jets as a hypothesis bundle is the forbidden frontier-wrapper
pattern.  The (a) lemmas here are the exact convex-combination inputs the moving-base bridge
consumes.  Remaining 2a distance: 2a-tel (b) blocked on the two gaps above; 2a-hi / 2a-pkg
unchanged.  Full-class order-0 `unifCurvatureSup` as a stated theorem: 0% (not started);
its convex-comb link infra: (a) done.

## Session 9 (2026-07-24, LANE C, Opus) — ENVELOPE + Λ<2 single link (normBridge now DISCHARGED)

`normBridge` landed sorry-free in `MetricCovDerivBridge.lean` (session 8's gate is OPEN).
Mission: build the order-`≤2` jet envelope + the assembled `unifCurvatureSup_singleLink`
(Λ<2 regime) in this leaf.  Confirmed API inventory (all public unless noted):

- **normBridge** (`MetricCovDerivBridge.lean:238`): `‖(iteratedCovGrad gBase 0 2 j
  (metricCcTensor gBase h)).toSection x‖ = √(normSq0S gBase x (j+2) (metricCovDeriv h gBase j x))`
  under `letI := tensorRS_riemannianBundle gBase 0 (2+j)`.
- **difference asset** (`PerturbedRiemannOpDifferenceBound.lean:88`): role base=gBase,
  g₁=g₀, P=metricDifferenceCcTensor gBase g₀; needs hδ₀:δ₀<1, B, hB; then per (g₁,P,δ,hδ_le,
  hδ,htie,x): envelope `∑_{j<3}‖(iteratedCovGrad gBase 0 2 j P).toSection x‖ ≤ B` ⟹
  `gBase(R(g₀)−R(gBase),·) ≤ C²·gBase-quad`.  δ IMPLICIT with `hδ_le : δ ≤ max δ₀ 0`.
- **MetricCovDerivOrderBoundOn K a h gRef C** (`AllTimesBounds.lean:691`) `:= ∀ x∈K,
  metricCovDerivNorm a h gRef x ≤ C`, single order `a`; `metricCovDerivNorm a h gRef x =
  √(normSq0S gRef x (a+2)(metricCovDeriv h gRef a x))` (`:661`, rfl).
- **iteratedCovGrad_zero** (`SobolevEmbeddingCm.lean:102`, simp): `… 0 T = T`.
- **norm_toSection_eq_sqrt_riemannianFiberNormSq** (`MetricArmCoeffJetTower.lean:904`, public):
  `‖W.toSection x‖ = √(riemannianFiberNormSq gBase r s x (W.toSection x))`.
- **normSq0S_le_card_of_component_bound** (`Comparison.lean:240`): ON-frame component bound
  `≤ B` ⟹ `normSq0S ≤ card(Fin s→Idx)·B²`.  (j=0 Parseval tool; card(Fin 2→Fin n)=n².)
- **ccTensorBilin_abs_le_fibreNorm_mul_sqrt** (`TensorHsRealize.lean:163`, public): its proof
  contains inline the Parseval identity `∑_{i,j}(ccTensorBilin gBase T x (e i)(e j))² =
  ‖T.toSection x‖²` (`have hcompsq`, lines 279-299) over an ON frame from
  `tangent_frame_expansion`.  (Fallback source if no standalone public Parseval bridge.)
- **metricCovDeriv_succ** (`MetricCovDerivLinear.lean:81`, OTHER-executor file — USE ONLY):
  `metricCovDeriv h gRef (a+1) = metricCovDerivStep gRef a (metricCovDeriv h gRef a)` (rfl).
- **metricCovDeriv_succ_apply_section** (`MetricCovDerivCoordStep.lean:43`): `… (a+1) x
  (Fin.cons (X x) slots) = nabla0SFun (a+2)(leviCiv gRef) X (metricCovDeriv h gRef a) x slots`.
- **nabla_metric_zero** (`MetricCompatibility.lean:117`): `nabla0SFun 2 cov X (metricTensorField
  g) x = 0` (cov metric-compat); **nabla_zero** (`:151`): `nabla0SFun s cov X 0 x = 0`.
- **leviCivitaConnectionOfMetric_isMetricCompatible** (`Integral.Connection`): `IsMetricCompatible_gen
  (leviCivitaConnectionOfMetric g) g`.
- **ext0S_basis** (`CoordinateBasis.lean:207`), **component0S_apply** (`:150`, rfl),
  **iteratedCovGrad_sub** (`IteratedCovGradLinear.lean:91`).
- **metricCovDeriv gBase gBase 0 = metricTensorField gBase** (rfl, `PointedConvergence.lean:96/184`).

### Route
1. **j=0** (`‖metricDiff.toSection x‖ ≤ n·(Λ−1)`): `norm_toSection_eq_sqrt_rfns` →
   bridge rfns=normSq0S(unit) [PENDING agent: public or reproduce ~30 lines] →
   `normSq0S_le_card_of_component_bound` (component = ccTensorBilin = g₀−gBase, |·|≤Λ−1 on
   ON frame via `metricDiff_gFibreOpBound`) → √(n²(Λ−1)²)=n(Λ−1).
2. **j∈{1,2}** (`≤ Λ`): `metricDiff_iterCovGrad_sub` split; `metricCcTensor gBase gBase` half
   →0 via normBridge + selfZero (`metricCovDeriv gBase gBase j = 0`) + normSq0S 0 =0;
   `metricCcTensor gBase g₀` half = normBridge = metricCovDerivNorm ≤ Λ [hjet_j].
   Needs: toSection-sub additivity [PENDING agent], selfZero1/selfZero2 (build via
   succ_apply_section + nabla_metric_zero/nabla_zero + ext0S_basis).
3. **envelope**: sum = n(Λ−1)+Λ+Λ = **n(Λ−1)+2Λ**.  c₀(n)=n.
4. **single link**: obtain asset C=Cd; discharge hdiff via P/htie(`metricDiff_tie`)/hδ
   (`metricDiff_gFibreOpBound`,δ=Λ−1<1 from hΛ2)/envelope; feed
   `unifCurvatureSup_singleLink_of_diff`.  **F = Λ²·(Cd + √Kbase)**.

RISK: RiemannianBundle `letI` + `attribute [-instance] tensorRSSpace_normedAddCommGroup/
normedSpace` juggling must mirror asset/normBridge exactly (norm-instance defeq).

### LANDED (sorry-free, axiom-clean — `[propext, Classical.choice, Quot.sound]` on all 4 public)
`lake build +…UnifCurvatureJetBound` EXIT=0 (9653 jobs). New declarations in the leaf:
- **`metricDiff_order0_bound`** (public): `‖(metricDifferenceCcTensor gBase g₀).toSection x‖ ≤
  n·(Λ−1)`, `n = finrank ℝ E`.  Route: `norm_toSection_eq_sqrt_riemannianFiberNormSq` →
  reproduced `rfns_eq_normSq0S_unit'` → `normSq0S_le_card_of_component_bound` (card `n²` via
  `Fintype.card_fun`) with component = `ccTensorBilin = g₀−gBase`, `|·|≤Λ−1` from
  `metricDiff_gFibreOpBound` on the ON frame (`gBase(eᵢ,eᵢ)=1`).
- **`metricDiff_orderPos_bound (a)`** (public): `‖(iteratedCovGrad gBase 0 2 (a+1) …).toSection x‖
  ≤ Λ`.  `metricDiff_iterCovGrad_sub` split; the `metricCcTensor gBase gBase` half has norm 0 via
  `normBridge gBase gBase (a+1) x` + **`covNorm_self_succ`** (ConvFieldInputs — the self-zero
  ALREADY EXISTS, no reproof needed); `SmoothCcTensor.toSection_sub` + `norm_eq_zero`; the g₀ half
  = `normBridge g₀ gBase (a+1) x` = `metricCovDerivNorm (a+1) g₀ gBase x ≤ Λ` from the jet hyp.
- **`metricDiff_jetEnvelope`** (public): `∑_{j<3} ‖…‖ ≤ n·(Λ−1) + 2Λ` via `Finset.sum_le_sum`
  with per-`j` bound `if j=0 then n(Λ−1) else Λ` (`fin_cases` + defeq-tolerant `simpa`/`exact`).
  **B(Λ) = n·(Λ−1) + 2Λ, c₀(n)=n.**
- **`unifCurvatureSup_singleLink`** (public, THE endpoint): `hΛ:1≤Λ, hΛ2:Λ<2, hcomp,
  hjet1/hjet2 (MetricCovDerivOrderBoundOn univ 1/2 g₀ gBase Λ)` ⟹ `∃F≥0, ∀ x v w u,
  g₀(R(g₀)vwu,·) ≤ F²·g₀-quad`.  Discharges the asset `hdiff` (P=metricDifferenceCcTensor,
  htie=`metricDiff_tie`, hδ=`metricDiff_gFibreOpBound` δ=Λ−1<1, env=`metricDiff_jetEnvelope`),
  feeds session-4 `unifCurvatureSup_singleLink_of_diff`.  **F = Λ²·(Cd + √Kbase)** where Cd =
  the asset's difference constant at δ₀=Λ−1, B=n(Λ−1)+2Λ; Kbase = fixed gBase curvature.
- Reproduced private helpers (MetricCovDerivBridge's are `private`, can't edit that file):
  `lowerAllUpper_zero_eq_unit'`, `rfns_eq_normSq0S_unit'`, `component0S_unit_eq_ccBilin`.
- Imports added: `MetricCovDerivBridge`, `ConvFieldInputs`, `Geometry.Curvature.RicciOperatorNormBound`;
  `open DifferentialGeometry.HCGCompactness`.

Lean lessons: (1) the RiemannianBundle→`Norm` synth needs `set_option synthInstance.maxHeartbeats
1600000 in` (default 20000 times out) — mirror normBridge, scope per-decl.  (2) inline `letI` in a
`have :` Prop misparses (`‖…‖` applied to the bundle) — infer the summand via `Finset.sum_le_sum
(g:=…) ?_` instead of re-typing it.  (3) `reduceIte` does NOT fire in `simp only` here — reduce
ites with explicit `if_pos/if_neg`.  (4) `finrank (TangentSpace I x) = finrank E` is rfl but `rw`'s
auto-close uses reducible transparency; `change` to `finrank E` first.  (5) `0+1`/`2+0` vs `1`/`2`:
use `exact`/`simpa` (defeq-tolerant), never `linarith` (syntactic atoms).

### 2a-tel (Λ ≥ 2, full class) — what remains (NOT in this session)
The single link is `Λ < 2` only (asset needs `δ₀ = Λ−1 < 1`).  For the full class: telescope
`g_t = convexComb g₀ gBase (const t)`, `N ≈ Λ` links each op-step `<1`; per link need (a) convexComb
comparability + jet inheritance (NEW lemmas on `SmoothRiemannianMetric.convexComb`, see session-4
block), (b) apply `unifCurvatureSup_singleLink` per link, (c) compose ~2Λ(Λ+1) curvature
differences by g-norm triangle.  The per-link discharge (tie/D1/envelope) is now DONE; 2a-tel is
the convexComb-inheritance + composition layer only.

STATUS: **ENVELOPE + Λ<2 single link COMPLETE, verified, axiom-clean.**

## Session 8 (2026-07-24, LANE C, Opus) — D2 `normBridge` GATED on a missing upstream agreement (corrects session 7)

Session 7 called D2 a "single-frontier assembly."  Session 8 recon of the two
covariant-derivative FORMALISMS shows the frontier is bigger: `normBridge` (now homed in
the ratified `MetricCovDerivBridge.lean`, statement pinned + `sorry`-at-gate, builds green,
axioms `[propext, sorryAx, Classical.choice, Quot.sound]`) is **gated on a missing upstream
framework agreement `nabla0SFun ↔ tensor0SCovariantDerivative` (r=0)**:
- envelope side (`iteratedCovGrad`/`covGrad`) = ABSTRACT `tensor0SCovariantDerivative`;
- `metricCovDeriv` side = CHART/model `nabla0SFun`/`totalNabla0S`
  (`totalNabla0S_apply` → `fderivWithin` + `connectionEndomorphismInChartL`);
- the crossing is flagged-missing (`Evolution/NablaRiemannT1Bound.lean:75`,
  `Evolution/IteratedNablaRmTower.md:729,748,777,868`); the proven chart↔abstract agreement
  (`Connection/ChartTensorNabla/Agreement/`) is for the DIFFERENT
  `chartTensor0SCovariantDerivative`, no `nabla0SFun` link.
No convention/slot-order/connection mismatch (session-7 verdict stands).  Full analysis,
assembly plan, and the proposed upstream lemma live in **`MetricCovDerivBridge.md`**.
D2 / single-link / 2a-tel remain blocked behind that upstream agreement (a separate planner
dispatch).

## Session 7 (2026-07-24, LANE C, Opus) — D2 recon COMPLETE: decisive risk RESOLVED; single-frontier decomposition

### VERDICT — the coordinator's decisive risk (convention / slot-order / connection mismatch) is RESOLVED (no mismatch)
Deep recon of both covariant-derivative iterations settles the session-6 worry:
- **Connection: identical, definitionally.** `covGrad` differentiates against
  `LeviCivita g` (`CovGrad/Defs.lean` → `covGradGradSection` uses
  `tensorRSCovariantDerivative … (LeviCivita g)`), and
  `LeviCivita g = leviCivitaConnectionOfMetric g` by **`rfl`**
  (`Connection/LeviCivita/Defs.lean:262 LeviCivita_eq_leviCivitaConnectionOfMetric`;
  the project's LeviCivita→metricCov collapse).  `metricCovDerivStep` uses
  `leviCivitaConnectionOfMetric gRef`.  Same connection — NO mismatch.
- **Slot order: identical (derivative-slot-first, both towers).**
  `metricCovDeriv` places derivative slots first (Defs docstring).  `covGrad` also
  prepends the new slot: `curry_covGrad_unit_eval_genVal`
  (`Curvature/CovGradRoughLap/GradientField.lean:183`) reads slot `0` as the
  derivative direction.  NO slot-order mismatch.
- **The `r ≥ 1` "no bridge to totalNabla0S" frontier** flagged in
  `Evolution/IteratedNablaRmTower.md:571,590` **does NOT apply here** — our tensor is
  `(0, 2)` (`r = 0`), and the `r = 0` RS↔0S bridges EXIST:
  `covDeriv_unit_eval_eq_genVal` (`GradientField.lean:257`:
  `tensorRSCovariantDerivative 0 s (LeviCivita g) σ · (unit) = tensor0SCovariantDerivative s (LeviCivita g) (σ·(unit))`).

So D2 is mathematically SOUND and reduces to **ONE reusable frontier lemma**; everything
else composes from existing API.

### The SINGLE genuine frontier lemma (reusable; belongs upstream, NOT in this leaf)
```
normBridge (h gBase : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
  ‖(iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h)).toSection x‖_{tensorRS_riemannianBundle gBase 0 (2+j)}
    = Real.sqrt (normSq0S gBase x (j+2) (metricCovDeriv h gBase j x))
```
Two halves, both multi-lemma, HEq-heavy (index cast `2+j` vs `j+2`; cf.
`CovGrad/CovariantBilinearLeibniz.lean:100 norm_toSection_heq_congr` already needed for
`(s+1)+m = s+(m+1)`):
- **(a) tower match**: `iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h) .toSection x (unit) = metricCovDeriv h gBase j x`, by induction on `j`.  Base: `metricCovDeriv h gBase 0 = metricTensorField h` (`PointedConvergence.lean:184`) and `metricCcTensor gBase h .toSection x (unit) = metricTensorField h x` (`metricCcTensorFib_apply` = `metricTensorField_apply`, both `= h.inner x (v0) (v1)`).  Step: `curry_covGrad_unit_eval_genVal` + `covDeriv_unit_eval_eq_genVal` + `totalNabla0SFun_apply_section` (the `metricCovDerivStep` operator) + `nabla0SFun ↔ tensor0SCovariantDerivative` identification.
- **(b) norm reconciliation**: `riemannianFiberNormSq gBase 0 s x (T.toSection x) = normSq0S gBase x s (T.toSection x (unit))`, via `norm_toSection_eq_sqrt_riemannianFiberNormSq` (`Sobolev/TensorHilbert/MetricArmCoeffJetTower.lean:904`, clean) + `_eq_coord` on both sides (Hom-from-`Tensor0SSpace 0 = ℝ` isometry).
Proposed home: `Analysis/Spectral/Tensor/CovGrad/` or `HCGCompactness/` beside the
`metricCovDeriv*` bridges (reusable — connects the two derivative APIs).  Per mission
protocol (upstream bridge ⟹ stop-and-propose), NOT placed in this leaf.

### Composition around the frontier (all from EXISTING API — no new frontiers)
- **Envelope shape is a named def**: `iteratedCovGradJetSum gBase S x = ∑_{j<3} ‖(iteratedCovGrad gBase 0 2 j S).toSection x‖` (`MetricRealization/RealizedJet2CovGradBound.lean:262`).  Consumer = `MetricArmCoeffJetTower`'s `(1+R)^j` tower `R`-input currency (my `S = metricDifferenceCcTensor gBase g₀`).
- **RS linearity**: `iteratedCovGrad_sub` (`CovGrad/IteratedCovGradLinear.lean:91`), `covGrad_sub`, `covGrad_zero` all exist.
- **j≥1 self-zero (0S-world, AFTER the bridge)**: `metricCovDeriv gBase gBase j = 0` from `nabla_metric_zero` (`Tensor/RSTensor/MetricCompatibility.lean:117`, `∇g = 0`) iterated + `metricCovDeriv gBase gBase 0 = metricTensorField gBase`.  So the `metricCcTensor gBase gBase` tower vanishes for `j ≥ 1`; the difference-envelope's `j≥1` terms reduce to `√normSq0S(metricCovDeriv g₀ gBase j) ≤ Λ` directly from `MetricCovDerivOrderBoundOn`.
- **j=0 term (order-0 HS)**: `‖metricDifferenceCcTensor gBase g₀ .toSection x‖ = √(riemannianFiberNormSq gBase 0 2 x (…))`; bound `riemannianFiberNormSq ≤ finrank²·(Λ−1)²` via `_eq_coord`/Parseval (`normSq0S_eq_coord`; ON frame) + my Discharger-1 op bound `Λ−1` per component ⟹ `≤ finrank·(Λ−1)`.  **Pins `c₀(n) = finrank ℝ E = n`.**

### Pinned constants
`B(Λ) = c₀(n)·(Λ−1) + 2Λ` with **`c₀(n) = n = Module.finrank ℝ E`** (order-0 HS = `n·(Λ−1)`;
orders 1,2 each `≤ Λ` from `MetricCovDerivOrderBoundOn (≤2) g₀ gBase Λ`, summed `= 2Λ`).

### LANDED this session (sorry-free, axiom-clean)
`metricDiff_iterCovGrad_sub` (public): RS linearity split of the envelope summand,
`iteratedCovGrad gBase 0 2 j (metricDifferenceCcTensor gBase g₀) = iteratedCovGrad … (metricCcTensor gBase g₀) − iteratedCovGrad … (metricCcTensor gBase gBase)` (via `iteratedCovGrad_sub`; the `metricDifferenceCcTensor = metricCcTensor g₀ − metricCcTensor gBase` reduction is `rfl`).  Design-independent first assembly step (needed whether the planner builds `normBridge` upstream or restates the S1 hypothesis in RS currency).  Import added: `…CovGrad.IteratedCovGradLinear`.

### STOP condition (this brick) — reached
Frontier `normBridge` is a genuine multi-session upstream structural tower (two
HEq-heavy halves).  Mission protocol: upstream bridge ⟹ stop-and-propose.  Assembly
`unifCurvatureSup_singleLink` and `2a-tel` remain blocked on `normBridge` + the j=0
Parseval HS bound (both upstream/reusable).  DECISION for planner: (i) build `normBridge`
upstream (est. 1–2 sessions), or (ii) restate S1's curvature-jet hypothesis directly in
the RS `iteratedCovGradJetSum` currency (avoids the bridge; `MetricArmCoeffJetTower`
already consumes that currency).

## Session 6 (2026-07-24, LANE C, Opus) — Discharger 1 LANDED; D2 frontier sharpened

### LANDED — Discharger 1 (`gFibreOpBound` from comparability), verified + axiom-clean
Three declarations in `UnifCurvatureJetBound.lean`:
- `clm_offdiag_le_of_diag` (private, REUSABLE): for a symmetric fibre form `D`
  with `|D u u| ≤ c·gBase(u,u)`, `|D v w| ≤ c·√(gBase(v,v))·√(gBase(w,w))`.
  Proof = polarization AM bound `½c(gBase(v,v)+gBase(w,w))` + unit-vector
  rescaling to the GM; degenerate slots via `gBase.pos`.  (Generic op-norm =
  diagonal-norm fact; kept private in the leaf — could get a public home in a
  metric/fibre-algebra layer if reused elsewhere.)
- `metricDiff_diag_le` (private): `|g₀(u,u)−gBase(u,u)| ≤ (Λ−1)·gBase(u,u)` from
  comparability (`Λ⁻¹+Λ−2 = (Λ−1)²/Λ ≥ 0`).
- `metricDiff_gFibreOpBound` (public, D1): `gFibreOpBound gBase (ccTensorBilinSymm
  gBase (metricDifferenceCcTensor gBase g₀)) (Λ−1)` under `hΛ : 1 ≤ Λ` +
  comparability.  NOTE: `Λ < 2` is NOT needed for D1 itself (the bound `Λ−1`
  holds for all Λ≥1); the `δ = Λ−1 < 1` gate is a CONSUMER (asset) requirement,
  added at assembly.  Axiom audit `[propext, Classical.choice, Quot.sound]`;
  `lake build` 9405 jobs EXIT=0.

### D2 frontier — SHARPENED (the hard bridge; NOT attempted this session)
Recon of the two covariant-derivative iterations shows they are **NOT obviously
definitionally parallel** (the coordinator's stop-condition):
- `iteratedCovGrad gBase 0 2 j T` iterates `covGrad gBase r s`
  (`SobolevEmbeddingCm.lean:94` → `CovGrad/Defs.lean:253`) on the `SmoothCcTensor`
  `T = metricCcTensor gBase h`.
- `metricCovDeriv h gBase j` (`PointedConvergence.lean:80`) iterates
  `metricCovDerivStep gBase` — which evaluates via `nabla0SFun` /
  `leviCivitaConnectionOfMetric gBase` (`metricCovDeriv_one_apply_section:105`) —
  on the `Tensor0SField` `metricTensorField h`.
So the bridge needs a PROVEN equality (or the norm-`≤` version — consumer only
needs norms) between `covGrad gBase` and the `nabla0SFun/leviCivitaConnectionOf
Metric gBase` step, PLUS `metricCcTensor gBase h .toSection ↔ metricTensorField h`.
Neither is `rfl`-obvious.  Additional missing pieces:
- `metricCovDeriv gBase gBase j = 0` for j≥1 (metric compatibility) — the existing
  `metricCovDeriv_zero_restrictOpen_apply` (`MetricDerivNormRestrict.lean:40`) is
  about restrictOpen, NOT self-zero; the self-zero must be built (iterate the
  first-order metric-compat `∇^{gBase}gBase = 0`).
- norm reconciliation `‖·.toSection x‖` ↔ `metricCovDerivNorm`.
- order-0 `(0,2)`-tensor HS norm of `g₀−gBase` from the op bound `Λ−1`.
This is a genuine multi-sub-lemma brick, likely its own session, and the
covGrad↔leviCivita-step alignment is the decisive risk — if it is a real
convention mismatch (slot order / connection), STOP and report per the
coordinator.  `B(Λ) = c₀(n)(Λ−1) + 2Λ` shape unchanged (c₀ from the order-0 HS
factor, still to pin).

### ASSEMBLY (`unifCurvatureSup_singleLink`) — blocked on D2 only
D1 done; tie done; need D2's envelope, then apply the difference asset (δ₀:=Λ−1,
needs `hΛ2 : Λ<2`) → `hdiff` → session-4 `unifCurvatureSup_singleLink_of_diff`.

## Session 5 (2026-07-24, LANE C, Opus) — P-construction recon + TIE API landed

### KEY RECON FINDING — the P-construction ALREADY EXISTS (reuse, don't rebuild)
- `metricCcTensor (g₀ g : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2`
  (`Analysis/Parabolic/RicciLinearization/RicciArmResidualCoefficientFields.lean:107`)
  realizes metric `g` as a `(0,2)` cc-tensor tagged over `g₀`; closed M ⟹ compact
  support is `HasCompactSupport.of_compactSpace`.
  KEY: `metricCcTensor_apply : ccTensorBilin g₀ (metricCcTensor g₀ g) x v w = g.inner x v w` (:150).
- `metricDifferenceCcTensor g₀ g₁ := metricCcTensor g₀ g₁ − metricCcTensor g₀ g₀`
  (:118), `SmoothCcTensor g₀ 0 2`; `metricDifferenceCcTensor_self = 0` (:121).
- `ccTensorBilin_sub`, `ccTensorBilinSymm_sub` PUBLIC
  (`MetricRealization/RealizedGramDiff.lean:101/110`).
- No import cycle: `RicciArmResidualCoefficientFields` (Analysis/Parabolic) doesn't
  import HCG; my leaf may import it.
So the P **object** + realization is done; the mission's "construct P" reduces to
proving the **tie identity** and the two dischargers.  Role: base = gBase,
`g₁ = g₀`, `P = metricDifferenceCcTensor gBase g₀`.

### Asset htie shape (ground truth, `PerturbedRiemannOpDifferenceBound.lean:95`)
`htie : ∀ x v w, g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm g₀ P x v w`.

### LANDED this session — TIE API (in `UnifCurvatureJetBound.lean`)
- `metricDiff_ccBilin : ccTensorBilin gBase (metricDifferenceCcTensor gBase g₀) x v w
   = g₀.inner x v w − gBase.inner x v w`  (via `ccTensorBilin_sub` + `metricCcTensor_apply`×2).
- `metricDiff_ccBilinSymm : ccTensorBilinSymm gBase (metricDifferenceCcTensor gBase g₀) x v w
   = g₀.inner x v w − gBase.inner x v w`  (symmetrization of a symmetric form; uses `g.symm`).
- `metricDiff_tie : g₀.inner x v w = gBase.inner x v w
   + ccTensorBilinSymm gBase (metricDifferenceCcTensor gBase g₀) x v w`  (asset htie shape, role base=gBase).
Import ADDED: `…RicciLinearization.RicciArmResidualCoefficientFields`.

### FRONTIER — the two dischargers (designed; next session, both new nontrivial lemmas)
**Discharger 1 — comparability ⟹ `gFibreOpBound` (Λ<2 gate).**
Target: `gFibreOpBound gBase (ccTensorBilinSymm gBase P) (Λ−1)`, i.e. (via the tie)
`|g₀(v,w) − gBase(v,w)| ≤ (Λ−1)·√(gBase(v,v))·√(gBase(w,w))`.  From diagonal
comparability `Λ⁻¹gBase(v,v) ≤ g₀(v,v) ≤ ΛgBase(v,v)`: diagonal
`|D(v,v)| ≤ (Λ−1)gBase(v,v)` (`|Λ⁻¹−1| = 1−Λ⁻¹ ≤ Λ−1` for Λ≥1).  Off-diagonal via
**homogeneity/unit-vector trick** (NOT plain polarization — that gives the AM bound
½c(Q(v)+Q(w)), too weak): scale `v'=v/√Q(v), w'=w/√Q(w)`, get `|D(v',w')| ≤ c` from
the AM bound at unit vectors, rescale to `|D(v,w)| ≤ c√(Q(v)Q(w))`; Q=gBase-quad;
`Q=0 ⟹ v=0` (posdef) handles the degenerate case.  NO existing lemma
(`gFibreOpBound` def = `PosDefPerturbation.lean:70`; no diagonal→offdiag producer).
State honestly with `hΛ2 : Λ < 2` (⟹ δ=Λ−1<1); telescoping links each satisfy it.
**Discharger 2 — jet envelope from `MetricCovDerivOrderBoundOn ≤2` (the HARD one).**
Target: `∀ x, ∑_{j<3} ‖(iteratedCovGrad gBase 0 2 j P).toSection x‖ ≤ B(Λ)`.
Structural bridge needed (NO existing lemma):
`iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h) = metricCovDeriv h gBase j`
— both iterate the SAME covariant differentiation: `iteratedCovGrad` iterates
`covGrad gBase` (`SobolevEmbeddingCm.lean:94`); `metricCovDeriv h gBase j`
(`PointedConvergence.lean:80`) iterates `totalNabla0S(LeviCivita gBase)` of
`metricTensorField h` (`Tensor/RSTensor/MetricCompatibility.lean:37`).  Sub-steps:
(a) base-case `metricCcTensor gBase h .toSection ↔ metricTensorField h`;
(b) step-op `covGrad gBase ↔ totalNabla0S(LeviCivita gBase)`;
(c) `metricCovDeriv gBase gBase j = 0` for `j≥1` (iterated metric compatibility);
(d) linearity on `P = metricCcTensor gBase g₀ − metricCcTensor gBase gBase`;
(e) norm reconciliation `‖·.toSection x‖` (RiemannianBundle fibre norm on `TensorRSSpace 0 (2+j)`)
   ↔ `metricCovDerivNorm j g₀ gBase x = √(normSq0S gBase x (j+2)(metricCovDeriv g₀ gBase j x))`;
(f) order-0 `‖P.toSection x‖`: `(0,2)`-tensor (HS) norm of `g₀−gBase` from the
   operator bound `Λ−1` (dimensional factor).
So j=1,2 reduce to `MetricCovDerivOrderBoundOn ≤2` directly (since ∇^{gBase}gBase=0);
j=0 from comparability.  **B(Λ) shape:** `B(Λ) = c₀(n)·(Λ−1) + 2Λ` — order-0
`c₀·(Λ−1)` (dimensional, from the op bound) + orders 1,2 each `≤ Λ`, summed.
(Refine `c₀(n)` and any norm-reconciliation constant on orders 1,2 when (e) lands.)

### ASSEMBLY (final corollary, after both dischargers)
`unifCurvatureSup_singleLink (gBase g₀ Λ) (hΛ : 1≤Λ) (hΛ2 : Λ<2)
  (hcomp) (hjets : MetricCovDerivOrderBoundOn univ 2 g₀ gBase Λ)` ⟹
`∃ F ≥ 0, ∀ x v w u, g₀(R(g₀)vwu,·) ≤ F²·g₀-quad`, by:
tie ⟹ htie; discharger 1 ⟹ the asset's `hδ`; discharger 2 ⟹ the asset's envelope;
apply `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope` (δ₀:=Λ−1)
to get `hdiff`; feed `hdiff` into the session-4 `unifCurvatureSup_singleLink_of_diff`.
F = Λ²·(Cd(Λ−1,B(Λ)) + √Kbase).

### Home decision
Tie API + dischargers live in `UnifCurvatureJetBound.lean` (mission-sanctioned;
consumer-side curvature-bound bridges).  If discharger 2's structural bridge
(a)/(b) turns out to belong upstream (a general `iteratedCovGrad(metricCcTensor)
= metricCovDeriv` fact, reusable beyond curvature), flag for an editable-set
extension.

## Session 4 (2026-07-24, LANE C, Opus) — STEP 0 + composition core landed

### STEP 0 — asset real-green PROBE (mandatory, per false-green lesson)
`lake build` of the three consumed asset modules
(`PerturbedRiemannOpDifferenceBound`, `CovDerivConnDiffQuadraticBound`,
`ChristoffelDifferenceKoszul`): "Build completed successfully (9273 jobs)",
EXIT=0, all REPLAYED real-green (warnings pre-existing in other files).  NOT
`lake env lean` false-greens.  Safe to consume.

### Ground-truth asset signatures (verified by direct read)
- ORDER-0 DIFFERENCE (`PerturbedRiemannOpDifferenceBound.lean:88`)
  `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope
   (g₀) {δ₀} (hδ₀ : δ₀<1) (B) (hB : 0≤B) : ∃ C ≥ 0, ∀ (g₁) (P : SmoothCcTensor g₀ 0 2)
   {δ} (hδ_le : δ ≤ max δ₀ 0) (hδ : gFibreOpBound g₀ (ccTensorBilinSymm g₀ P) δ)
   (htie : ∀ x v w, g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm g₀ P x v w) (x),
   (∑ j<3, ‖(iteratedCovGrad g₀ 0 2 j P).toSection x‖) ≤ B →
   ∀ v w u, g₀(R(g₁)−R(g₀), R(g₁)−R(g₀)) ≤ C²·g₀(v,v)·g₀(w,w)·g₀(u,u)`.
  KEY: the envelope uses the **asset-`g₀` connection**.  With role
  base=gBase (asset-`g₀` := gBase), it is `∇^{gBase,j}P` — direct
  `MetricCovDerivOrderBoundOn` content, so **Finding-D connection conversion is
  NOT needed** for the base=gBase assignment (corrects Finding D's worry).
- FIXED gBase CURVATURE (`UniformRiemannOperatorNormBound.lean:683`)
  `exists_uniform_riemannOp_LeviCivita_gNorm_bound (g) : ∃ Kbase ≥ 0,
   ∀ x v w u, g(R(g)vwu, R(g)vwu) ≤ Kbase·g(v,v)·g(w,w)·g(u,u)`.  (Squared-norm.)
- CONVEX COMBO (`Geometry/Metric/ConvexCombination.lean:140`)
  `SmoothRiemannianMetric.convexComb g₁ g₂ χ hχ hχ01`, `convexComb_inner :
   (g₁.convexComb g₂ χ …).inner x v w = χ x • g₁.inner x v w + (1−χ x) • g₂.inner x v w`.
  For telescoping take χ ≡ constant `t`.  NO comparability/jet lemmas yet.
- (N) comparability (inline, `ExtendViaUniqueness.lean:78`): diagonal
  `Λ⁻¹·gBase(v,v) ≤ g₀(v,v) ≤ Λ·gBase(v,v)` ∀ x v.  No named predicate.
- `MetricCovDerivOrderBoundOn K a h gRef C := ∀ x∈K, √(normSq0S gRef x (a+2)
   (metricCovDeriv h gRef a x)) ≤ C` (`AllTimesBounds.lean:661/691`)
  = `‖∇^{gRef,a}h‖_{gRef} ≤ C`.

### 2a-0 assembly SPINE (this session's math)
Role base=gBase, `g₁ = g₀`, `P = g₀−gBase`.  Chain, in gBase then g₀ currency:
1. difference asset ⟹ `gBase(R(g₀)−R(gBase),·) ≤ Cd²·gBase-quad`  (needs P/htie/fibre-op/envelope).
2. fixed asset @ gBase ⟹ `gBase(R(gBase),·) ≤ Kb·gBase-quad`.
3. g-norm triangle (`R(g₀) = (R(g₀)−R(gBase)) + R(gBase)`) + square ⟹
   `gBase(R(g₀),·) ≤ (Cd+√Kb)²·gBase-quad`.
4. comparability conversion ⟹ `g₀(R(g₀),·) ≤ Λ⁴(Cd+√Kb)²·g₀-quad`
   (one Λ on the output vector `g₀ ≤ Λ·gBase`, three on the inputs `gBase ≤ Λ·g₀`).
So **F = Λ²·(Cd + √Kb)** (norm form; squared bound uses F²).

### LANDED this session — `UnifCurvatureJetBound.lean` (composition core)
`unifCurvatureSup_singleLink_of_diff` (target-shaped, verified): takes the
difference bound (step 1's CONCLUSION) as hypothesis `hdiff` + `Λ`-comparability,
consumes the committed fixed-curvature asset (step 2), does steps 3–4, and
produces `∃ F ≥ 0, ∀ x v w u, g₀(R(g₀),·) ≤ F²·g₀(v,v)g₀(w,w)g₀(u,u)` with
`F = Λ²(Cd+√Kb)`.  Plus a private g-norm triangle helper `gAddNorm_le`.
This is the item-4-style abstraction: the genuinely-missing infrastructure
(discharging `hdiff`) is the named frontier; the composition + fixed asset +
conversion is fully proved.

### FRONTIER (remaining for full 2a-0, next sessions)
- **Discharge `hdiff`** (the crux): construct `P = g₀−gBase : SmoothCcTensor
  gBase 0 2` with `htie` (metric-difference-as-ccTensor — MISSING infra; `htie`
  is always a hypothesis in the codebase, never constructed); derive
  `gFibreOpBound gBase (ccTensorBilinSymm gBase P) (Λ−1)` from comparability
  (needs Λ<2 for δ<1); derive the envelope `∑_{j<3}‖∇^{gBase,j}P‖ ≤ B` from
  `MetricCovDerivOrderBoundOn ≤2 g₀ gBase Λ` (orders 1,2 direct; order 0 = ‖g₀−gBase‖
  from comparability).  Then apply the order-0 difference asset.
- **2a-tel** (Λ ≥ 2 full class): `g_t = convexComb g₀ gBase (const t)`; prove
  each link's convexComb comparability + jet inheritance (NEW lemmas on
  `convexComb`); compose ~2Λ(Λ+1) single-links by triangle.  Needs the
  discharge above per link.
- **2a-hi**: higher-order `∇^{g₀,a}R`, a ≤ b (order-generic; needs the
  higher-order curvature-difference extension the current asset lacks).

## Status
- 2026-07-24 (session 6, LANE C): **Discharger 1 LANDED** + verified + axiom-clean
  (`metricDiff_gFibreOpBound` + reusable `clm_offdiag_le_of_diag` + `metricDiff_diag_le`;
  `[propext, Classical.choice, Quot.sound]`; `lake build` 9405 jobs EXIT=0).
  Discharger 2 (envelope) NOT attempted — recon shows the `covGrad ↔
  leviCivita-step` bridge is not definitionally obvious + missing self-zero/norm
  pieces; genuine multi-sub-lemma brick (see session-6 block).  Assembly
  `unifCurvatureSup_singleLink` blocked on D2 only.
- 2026-07-24 (session 5, LANE C): P-construction recon done — `metricCcTensor` /
  `metricDifferenceCcTensor` ALREADY EXIST (reuse).  TIE API landed + verified +
  axiom-clean: `metricDiff_ccBilin`, `metricDiff_ccBilinSymm`, `metricDiff_tie`
  (all three `[propext, Classical.choice, Quot.sound]`; `lake build` 9405 jobs
  EXIT=0).  Frontier = the two dischargers (comparability→`gFibreOpBound` via the
  homogeneity trick; the order-`≤2` jet envelope via the `iteratedCovGrad ↔
  metricCovDeriv` structural bridge — the HARD one), then the assembled
  `unifCurvatureSup_singleLink`, then 2a-tel.  See session-5 block.
- 2026-07-24 (session 4, LANE C): STEP 0 asset probe PASSED (real-green);
  composition core `unifCurvatureSup_singleLink_of_diff` landed + verified +
  axiom-clean (see this file's session-4 block).  Frontier = discharge `hdiff`
  (P-construction crux) then 2a-tel/2a-hi.
- 2026-07-24 (session 3): (2a) recon COMPLETE, no Lean.  Finding A: (2a) is an
  assembly of existing jet-envelope curvature-difference machinery (de-risked).
  Finding B: that machinery is small-perturbation (`Λ<2`) only — full class needs
  telescoping.  Finding C: layering forces S1 to take the curvature bound
  abstractly (corrects recon §5).  Finding D: envelope-connection + order-budget
  bridges.  Stopped at the recon boundary pending planner ratification of the
  route (Findings B/C are scope-changing).  Recommended first brick = 2a-abs
  (abstract interface, landable in Analysis now).

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingDerivativesWindow_P6WA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingDerivatives2Window_P6WA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalCurvatureDerivativeBoundsWindow_P6WA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.ParabolicTerminalBallFlowWindow_P6WA

/-!
# hTPloc 逐层孪生 · 叶子层：HSIC:183 起点球版 + 直接窗口调用者（O-CH11-SLTLOCAL2-B G1，后缀 `_P6SL2`）

背景（state-O-CH11-SLTLOCAL "R-C11-19 Q4"）：TP 窗口引理
`exists_normalized_scalar_bound_of_chain_traces_window_P6WB`（P6WB:408）的五条导数消费路线全部终于
HSIC:183 `exists_backwardSurvivorIncomingFootprint_curvature_bound_window_P6WA` 的
reciprocal-Lipschitz 叶子（→ BTR:139 `inv_max_scalar_sub_incoming_terminal_le_on_time_window`），
且 HSIC 只在 footprint `K` 的 trace 点上用 `hbound`、
终端时刻 = `s`（= TP 的 `time i`）。本文件给坏点尺度局部合同（`hTPloc` 的 guard
`(time i − t)·max(q i, R(time i, z)) ≤ c i`）在叶子层的孪生：
* guard 统一形：`(s − t) * max q (Rt z) ≤ cg`，`Rt : (H.stage last).Carrier → ℝ` = 终端 scalar（TP 处
  `fun z => (A i).flow.scalar (time i) z`，与 `metricScalarAt (endpointTerminalLimitMetric).metric`
  同值）；
* HSIC:183 孪生：新前提 `hRt : ∀ x ∈ K, Rt x.val ≤ 2Q`（起点界，只在 `K` 上）+ `hcg : 2Q(s − c) ≤ cg`；
* 直接窗口调用者 HSID / TCDB / HSID2 / PTBF:110 / PTBF:225 的孪生：新前提
  `hRt : ∀ y ∈ K, Rt y.val ≤ metricScalarAt L.metric y` + 预算（`2θ ≤ cg`；HSID2 `2Aθ ≤ cg`；PTBF:110
  `2Q(s − c) ≤ cg`）。
证明模式（全部 PROVED，无 binder）：叶子窗口已是 `s − θ/Q′`（或给定 `c`），故取起点球
`U′ := U ∩ {Rt ≤ 2Q′}` 重调原引理（`K ⊆ U′` 由 `hRt` + `hscalar`），guard 由
`guard_le_of_start_bound_P6SL2`：`t ≥ c` ⇒ `(s − t)·max(q, Rt z) ≤ (s − c)·2Q′ ≤ cg`。原文件不改；上层
（TTC / TTC2 / Cone / Cone2 / Cone3，窗口 `a`、`Q(s − a) → ∞`）的孪生见 G2，在其叶子调用处付 `cg := c n`
（`c n → ∞` 故 eventually `≥ 2Aθ`）。consumer：文末 example（孪生 ⇒ 原引理，取 `Rt := 0`）。
生成器 `build-logs/scratch/O-CH11-SLTLOCAL2-B/gen1.py`（从 tracked 文本 assert 替换）。**不声称 J10 已去。**
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- guard 付法（`_P6SL2`）：`0 < q ≤ Q`、起点界 `Rz ≤ 2Q`、`c ≤ t`、`c ≤ s`、预算 `2Q(s − c) ≤ cg` ⇒
坏点尺度 guard `(s − t)·max(q, Rz) ≤ cg`。 -/
theorem guard_le_of_start_bound_P6SL2 {q Q Rz s c t cg : ℝ} (hq : 0 < q) (hqQ : q ≤ Q)
    (hRz : Rz ≤ 2 * Q) (hct : c ≤ t) (hcs : c ≤ s) (hcg : 2 * Q * (s - c) ≤ cg) :
    (s - t) * max q Rz ≤ cg := by
  have hM0 : 0 ≤ max q Rz := hq.le.trans (le_max_left _ _)
  have hM : max q Rz ≤ 2 * Q := max_le (by linarith) hRz
  calc (s - t) * max q Rz ≤ (s - c) * max q Rz :=
        mul_le_mul_of_nonneg_right (by linarith) hM0
    _ ≤ (s - c) * (2 * Q) := mul_le_mul_of_nonneg_left hM (by linarith)
    _ = 2 * Q * (s - c) := by ring
    _ ≤ cg := hcg

/-- 叶子窗口预算（`_P6SL2`）：窗口 `s − θ/Q`、起点界 `2·(A·Q)` ⇒ `2(AQ)·(θ/Q) = 2Aθ`。 -/
theorem window_budget_P6SL2 {s θ Q A cg : ℝ} (hQ : 0 < Q) (h : 2 * (A * θ) ≤ cg) :
    2 * (A * Q) * (s - (s - θ / Q)) ≤ cg := by
  have heq : 2 * (A * Q) * (s - (s - θ / Q)) = 2 * (A * θ) := by field_simp; ring
  rw [heq]
  exact h

/-- 叶子窗口预算（`_P6SL2`，`A = 1`）：`2Q·(θ/Q) = 2θ`。 -/
theorem window_budget_one_P6SL2 {s θ Q cg : ℝ} (hQ : 0 < Q) (h : 2 * θ ≤ cg) :
    2 * Q * (s - (s - θ / Q)) ≤ cg := by
  have heq : 2 * Q * (s - (s - θ / Q)) = 2 * θ := by field_simp; ring
  rw [heq]
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

/-- 局部实例（同 P6WA 文件的 private local instance；命名以便审计覆盖）。 -/
local instance sigmaCompactSpace_terminalRegularOpen_P6SL2 :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- 局部实例（同 P6WA 文件的 private local instance；命名以便审计覆盖）。 -/
local instance sigmaCompactSpace_footprint_P6SL2 (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

/-- **HSIC:183 起点球版（`_P6SL2`，PROVED）**。原引理
`ObservedHistory.exists_backwardSurvivorIncomingFootprint_curvature_bound_window_P6WA`
（`Local/HistorySurvivorIncomingCurvatureWindow_P6WA.lean:183`）→ 孪生：`hbound` 从 "整个 `U`、窗口 `c`" 形
改为多一句坏点尺度 guard `(s − t) · max q (Rt z) ≤ cg`（`s` = 终端时刻 = TP 的 `time i`，`Rt` = 终端 scalar，
TP 处取 `fun z => (A i).flow.scalar (time i) z`）。新前提只两条：起点界 `hRt : ∀ x ∈ K, Rt x.val ≤ 2Q`
（只在 footprint `K` 上）与预算 `hcg : 2Q(s − c) ≤ cg`。guard 付法：原证明只在 `x ∈ K` 的 trace 点上用
`hbound`，故取 `U′ := U ∩ {Rt ≤ 2Q}`（起点球）重调原引理；`t ≥ c` 时
`(s − t)·max(q, Rt z) ≤ (s − c)·2Q ≤ cg`（`q ≤ Q`）。结论逐字。 -/
theorem exists_backwardSurvivorIncomingFootprint_curvature_bound_window_loc_P6SL2
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen) (U : Set (H.stage last).Carrier)
    (hKU : ∀ x ∈ K, x.val ∈ U) {c : ℝ} {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (Rt : (H.stage last).Carrier → ℝ) {cg : ℝ}
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), c ≤ t →
      (s - t) * max q (Rt z) ≤ cg →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ x ∈ K, ∀ t ∈ Ioo (H.time last) s, c ≤ t → q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici c) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s ∩ Ici c) Phi)
    (hscalar : ∀ x ∈ K, metricScalarAt L.metric x ≤ 2 * Q)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val))
    (hRt : ∀ x ∈ K, Rt x.val ≤ 2 * Q) (hcg : 2 * Q * (s - c) ≤ cg)
    (hc : H.time first ≤ c) (hcs : c < s)
    (htime : 6 * C * (s - c) * Q ≤ 1) :
    range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first last hle G K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      gflow s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
          (RealTimeInterval.closed c s hcs.le)) ∧
      ∀ t ∈ Icc c s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
        normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
          (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 := by
  exact H.exists_backwardSurvivorIncomingFootprint_curvature_bound_window_P6WA first last hle G L
    hinit K (U ∩ {z | Rt z ≤ 2 * Q}) (fun x hx => ⟨hKU x hx, hRt x hx⟩) hq hqQ hPhi
    (fun j hf hl z hz A t ht hct => hbound j hf hl z hz.1 A t ht hct
      (guard_le_of_start_bound_P6SL2 hq hqQ hz.2 hct hcs.le hcg))
    hfinal hpinch hpinchFinal hscalar htrace hc hcs htime

/-- **HSID 起点球版（`_P6SL2`，PROVED）**。原引理
`ObservedHistory.curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace_window_P6WA`
（`Local/HistorySurvivorIncomingDerivativesWindow_P6WA.lean:49`，HSIC:183 的直接调用者）→ 孪生：`hbound`
多 guard `(s − t)·max q (Rt z) ≤ cg`；窗口已是叶子窗口 `s − θ/Q`，`K` = 终端球 `B̄_L(x, r/√Q)`。
guard 付法：`hRt : Rt ≤ metricScalarAt L.metric` 于 `K` 上 + `hscalar`（`R ≤ 2Q`）⇒
`U′ := U ∩ {Rt ≤ 2Q}` 含 `K`；
`(θ/Q)·2Q = 2θ ≤ cg`（预算 `hcg`）。结论逐字。 -/
theorem curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace_window_loc_P6SL2
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {r q Q θ : ℝ} {C : ℝ≥0}
    (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x (r / Real.sqrt Q)))
    (U : Set (H.stage last).Carrier)
    (hKU : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q), y.val ∈ U)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (Rt : (H.stage last).Carrier → ℝ) {cg : ℝ}
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), s - θ / Q ≤ t →
      (s - t) * max q (Rt z) ≤ cg →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t →
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (s - θ / Q)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow
      (Ico (H.time last) s ∩ Ici (s - θ / Q)) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hRt : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      Rt y.val ≤ metricScalarAt L.metric y) (hcg : 2 * θ ≤ cg)
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθ.le hQpos.le)
  exact H.curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace_window_P6WA first last hle G
    L hinit x hr hq hqQ hQ hθ hcompact (U ∩ {z | Rt z ≤ 2 * Q})
    (fun y hy => ⟨hKU y hy, (hRt y hy).trans (hscalar y hy)⟩) hPhi
    (fun j hf hl z hz A t ht hct => hbound j hf hl z hz.1 A t ht hct
      (guard_le_of_start_bound_P6SL2 hq hqQ hz.2 hct hcs (window_budget_one_P6SL2 hQpos hcg)))
    hfinal hpinch hpinchFinal hscalar htrace hc htime

/-- **TCDB 起点球版（`_P6SL2`，PROVED）**。原引理
`curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_window_P6WA`
（`Local/TerminalCurvatureDerivativeBoundsWindow_P6WA.lean:28`）→ 孪生：`hbound` 多 guard
`(s − t)·max q (Rt z) ≤ cg`；窗口 `s − θ/Q`，`K = B̄_L(x, (a + r)/√Q)`。guard 付法同 HSID
（`U′ := U ∩ {Rt ≤ 2Q}`、`2θ ≤ cg`）。结论逐字。 -/
theorem curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_window_loc_P6SL2
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {a r q Q θ : ℝ} {C : ℝ≥0}
    (ha : 0 ≤ a) (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)))
    (U : Set (H.stage last).Carrier)
    (hKU : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q), y.val ∈ U)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (Rt : (H.stage last).Carrier → ℝ) {cg : ℝ}
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), s - θ / Q ≤ t →
      (s - t) * max q (Rt z) ≤ cg →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t →
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (s - θ / Q)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow
      (Ico (H.time last) s ∩ Ici (s - θ / Q)) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hRt : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      Rt y.val ≤ metricScalarAt L.metric y) (hcg : 2 * θ ≤ cg)
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
    ∀ y ∈ riemannianClosedBallOf L.metric x (a / Real.sqrt Q),
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθ.le hQpos.le)
  exact H.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_window_P6WA
    first last hle G L hinit x ha hr hq hqQ hQ hθ hcompact (U ∩ {z | Rt z ≤ 2 * Q})
    (fun y hy => ⟨hKU y hy, (hRt y hy).trans (hscalar y hy)⟩) hPhi
    (fun j hf hl z hz A t ht hct => hbound j hf hl z hz.1 A t ht hct
      (guard_le_of_start_bound_P6SL2 hq hqQ hz.2 hct hcs (window_budget_one_P6SL2 hQpos hcg)))
    hfinal hpinch hpinchFinal hscalar htrace hc htime

/-- **PTBF:110 起点球版（`_P6SL2`，PROVED）**。原引理
`ObservedHistory.exists_parabolically_controlled_incoming_terminal_ball_window_P6WA`
（`Local/ParabolicTerminalBallFlowWindow_P6WA.lean:110`，κ 体积下界路线的叶子）→ 孪生：`hbound` 多 guard
`(s − t)·max q (Rt z) ≤ cg`；`K = B̄_L(x, r)`，窗口 `c`。guard 付法：`U′ := U ∩ {Rt ≤ 2Q}`
（`hRt` + `hscalar`），
预算 `2Q(s − c) ≤ cg`。结论逐字。 -/
theorem exists_parabolically_controlled_incoming_terminal_ball_window_loc_P6SL2
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x r))
    (U : Set (H.stage last).Carrier)
    (hKU : ∀ y ∈ riemannianClosedBallOf L.metric x r, y.val ∈ U)
    {c : ℝ} {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (Rt : (H.stage last).Carrier → ℝ) {cg : ℝ}
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), c ≤ t →
      (s - t) * max q (Rt z) ≤ cg →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x r, ∀ t ∈ Ioo (H.time last) s, c ≤ t →
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici c) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s ∩ Ici c) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x r,
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hRt : ∀ y ∈ riemannianClosedBallOf L.metric x r, Rt y.val ≤ metricScalarAt L.metric y)
    (hcg : 2 * Q * (s - c) ≤ cg)
    (hc : H.time first ≤ c) (hcs : c ≤ s)
    (htime : 6 * C * (s - c) * Q ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hwindow : ρ ^ 2 ≤ s - c)
    (hscale : ρ ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 ≤ 1) :
    let K := riemannianClosedBallOf L.metric x r
    ∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed c s hcs)),
      H.backwardSurvivorIncomingFootprintMap first last hle G K p = x ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∃ B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩,
        B.center = p ∧ B.radius = ρ ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p ρ ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x ρ ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x ρ) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p ρ) := by
  exact H.exists_parabolically_controlled_incoming_terminal_ball_window_P6WA first last hle G L
    hinit x hr hcompact (U ∩ {z | Rt z ≤ 2 * Q})
    (fun y hy => ⟨hKU y hy, (hRt y hy).trans (hscalar y hy)⟩) hq hqQ hPhi
    (fun j hf hl z hz A t ht hct => hbound j hf hl z hz.1 A t ht hct
      (guard_le_of_start_bound_P6SL2 hq hqQ hz.2 hct hcs hcg))
    hfinal hpinch hpinchFinal hscalar htrace hc hcs htime hρ hρr hwindow hscale

/-- **PTBF:225 起点球版（`_P6SL2`，PROVED）**。原引理
`ObservedHistory.exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_window_P6WA`
（`Local/ParabolicTerminalBallFlowWindow_P6WA.lean:225`；Cone:205 调用处）→ 孪生：`α` 同原引理（在历史之前取），
`hbound` 多 guard `(s − t)·max q (Rt z) ≤ cg`（`∀ Rt cg` 紧随 `q ≤ Q`），新前提 `Rt ≤ metricScalarAt` 于
`B̄_L(x, r)` 上 + `2θ ≤ cg`。guard 付法同 HSID。结论逐字。 -/
theorem exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_window_loc_P6SL2
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
      (x : G.terminalRegularOpen) {r q Q : ℝ} {C : ℝ≥0} (hQ : 1 ≤ Q),
    G.flow.base.metric (H.time last) = H.initialMetric last →
    0 < r → IsCompact (riemannianClosedBallOf L.metric x r) →
    ∀ U : Set (H.stage last).Carrier, (∀ y ∈ riemannianClosedBallOf L.metric x r, y.val ∈ U) →
    0 < q → q ≤ Q →
    ∀ (Rt : (H.stage last).Carrier → ℝ) (cg : ℝ),
    (∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), s - θ / Q ≤ t →
      (s - t) * max q (Rt z) ≤ cg →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t →
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (s - θ / Q)) Phi) →
    (Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s ∩ Ici (s - θ / Q)) Phi) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ 2 * Q) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r,
      Nonempty (BackwardPointTrace H first last hle y.val)) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, Rt y.val ≤ metricScalarAt L.metric y) →
    2 * θ ≤ cg →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    α / Real.sqrt Q < r →
    let K := riemannianClosedBallOf L.metric x r
    ∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed (s - θ / Q) s
          (sub_le_self s (div_nonneg hθ.le (zero_le_one.trans hQ))))),
      H.backwardSurvivorIncomingFootprintMap first last hle G K p = x ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∃ B : Perelman.FlowMetricBall S
          ⟨s, sub_le_self s (div_nonneg hθ.le (zero_le_one.trans hQ)), le_rfl⟩,
        B.center = p ∧ B.radius = α / Real.sqrt Q ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p (α / Real.sqrt Q) ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x (α / Real.sqrt Q) ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x (α / Real.sqrt Q)) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p (α / Real.sqrt Q)) := by
  obtain ⟨α, hα, hα1, hαθ, hchoice⟩ :=
    exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_window_P6WA hPhi hθ
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first last hle s G L x r q Q C hQ hinit hr hcompact U hKU hq hqQ Rt cg
    hbound hfinal hpinch hpinchFinal hscalar htrace hRt hcg hc htime hradius
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθ.le hQpos.le)
  exact hchoice H first last hle G L x hQ hinit hr hcompact (U ∩ {z | Rt z ≤ 2 * Q})
    (fun y hy => ⟨hKU y hy, (hRt y hy).trans (hscalar y hy)⟩) hq hqQ
    (fun j hf hl z hz A t ht hct => hbound j hf hl z hz.1 A t ht hct
      (guard_le_of_start_bound_P6SL2 hq hqQ hz.2 hct hcs (window_budget_one_P6SL2 hQpos hcg)))
    hfinal hpinch hpinchFinal hscalar htrace hc htime hradius

variable {E XH M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]

/-- **HSID2 起点球版（`_P6SL2`，PROVED；第二层 blow-up 叶子）**。原引理
`ObservedHistory.curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_window_P6WA`
（`Local/HistorySurvivorIncomingDerivatives2Window_P6WA.lean:49`）→ 孪生：`hbound` 多 guard
`(s − t)·max q (Rt z) ≤ cg`；窗口 `s − θ/Q`，起点界 `R ≤ 2·(A·Q)`（`Q` = 第二层基点尺度 `Q₂`）。guard 付法：
`U′ := U ∩ {Rt ≤ 2AQ}`（`hRt` + `hscalar`），`(θ/Q)·2AQ = 2Aθ ≤ cg`——深度绑在起点自身尺度 `1/Q`。结论逐字。 -/
theorem curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_window_loc_P6SL2
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    (Ψ : M → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {r q Q θ A : ℝ} {C : ℝ≥0}
    (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ A * Q) (hQ : 1 ≤ Q) (hA : 1 ≤ A) (hθ : 0 < θ)
    (hmetric : ∀ t ∈ Icc (-(θ / 2)) 0, S.base.metric t =
      localPullMetric (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow (s + t / Q))) Ψ hΨ)
    (z : M)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K (Ψ z)) (r / Real.sqrt Q)))
    (hball : riemannianBallOf L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K (Ψ z)) (r / Real.sqrt Q) ⊆
        interior K)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (U : Set (H.stage last).Carrier) (hKU : ∀ y ∈ K, y.val ∈ U)
    (Rt : (H.stage last).Carrier → ℝ) {cg : ℝ}
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), s - θ / Q ≤ t →
      (s - t) * max q (Rt z) ≤ cg →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y ∈ K,
      ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t →
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (s - θ / Q)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow
      (Ico (H.time last) s ∩ Ici (s - θ / Q)) Phi)
    (hscalar : ∀ y ∈ K,
      metricScalarAt L.metric y ≤ 2 * (A * Q))
    (htrace : ∀ y ∈ K,
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hRt : ∀ y ∈ K, Rt y.val ≤ metricScalarAt L.metric y) (hcg : 2 * (A * θ) ≤ cg)
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ * A ≤ 1) :
    let B := 4 * Real.sqrt 3 * A * (1 + Phi 4 + Phi 0)
    ∀ m : ℕ, ∀ t ∈ Icc (-(θ / 2)) 0, curvDerivNorm m (S.base.metric t) z ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθ.le hQpos.le)
  exact H.curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_window_P6WA first last
    hle G L hinit K gflow hslabs hlast Ψ hΨ S hr hq hqQ hQ hA hθ hmetric z hcompact hball hPhi
    (U ∩ {w | Rt w ≤ 2 * (A * Q)}) (fun y hy => ⟨hKU y hy, (hRt y hy).trans (hscalar y hy)⟩)
    (fun j hf hl w hw B t ht hct => hbound j hf hl w hw.1 B t ht hct
      (guard_le_of_start_bound_P6SL2 hq hqQ hw.2 hct hcs (window_budget_P6SL2 hQpos hcg)))
    hfinal hpinch hpinchFinal hscalar htrace hc htime

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u in
open ObservedHistory in
/-- consumer（sanity）：HSIC 孪生 ⇒ HSIC:183 原引理（取 `Rt := 0`、`cg := 2Q(s − c)`；guard 丢弃）——
孪生不弱于树内已证叶子。 -/
example : type_of%
    @ObservedHistory.exists_backwardSurvivorIncomingFootprint_curvature_bound_window_P6WA.{u} := by
  intro H first last hle s G L hinit K U hKU c q Q C hq hqQ Phi hPhi hbound hfinal hpinch
    hpinchFinal hscalar htrace hc hcs htime
  exact H.exists_backwardSurvivorIncomingFootprint_curvature_bound_window_loc_P6SL2 first last hle
    G L hinit K U hKU hq hqQ hPhi (fun _ => 0)
    (fun j hf hl z hz A t ht hct _ => hbound j hf hl z hz A t ht hct) hfinal hpinch hpinchFinal
    hscalar htrace (fun _ _ => by linarith) le_rfl hc hcs htime

universe u in
open ObservedHistory Classical in
/-- consumer（sanity）：HSID 孪生 ⇒ HSID 原引理（`Rt` 取终端 scalar 本身，`cg := 2θ`）。 -/
example : type_of%
    @curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace_window_P6WA.{u} := by
  intro H first last hle s G L hinit x r q Q θ C hr hq hqQ hQ hθ hcompact U hKU Phi hPhi hbound
    hfinal hpinch hpinchFinal hscalar htrace hc htime
  exact H.curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace_window_loc_P6SL2 first last
    hle G L hinit x hr hq hqQ hQ hθ hcompact U hKU hPhi
    (fun z => if h : z ∈ G.terminalRegularOpen then metricScalarAt L.metric ⟨z, h⟩ else 0)
    (fun j hf hl z hz A t ht hct _ => hbound j hf hl z hz A t ht hct) hfinal hpinch hpinchFinal
    hscalar htrace (fun y _ => le_of_eq (by simp [y.property])) le_rfl hc htime

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

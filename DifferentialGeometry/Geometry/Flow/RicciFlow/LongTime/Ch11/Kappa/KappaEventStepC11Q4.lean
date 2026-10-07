import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaNoEventWindowC11Q3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IncomingStageWeightedRestart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedEventWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleBirthStagePropagationPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventLocalWeightedTemporalSupportPortC11P

/-!
# κ 线跨 event 归纳的单步引擎（O-CH11-KAPPA3 G1，后缀 `_C11Q4`；R-C11-4 D-3）

固定种子 `(t, p, r)`、trace、极点 `x`、`1 ≤ A`、地板 `3/a₀`（`a₀ = windowBarrierA₀_C11Q2 P g`）、
`M = tracedPhysicalWeightedMinimum`，上界 `U(w) = 2rw·e^{C(A)w²/r² + 32w/r}`。不变量
`Inv(c) := ∀ w ∈ Ioc 0 c, M w ≤ ↑U(w)`（WithTop 形，有限性在不变量内，D-3 要求）。三类单步：
* **base**（`activeStage t` 起点早于 `t − c²`）：
  `distinct_pole_initial_minimum_receives_pole_stage_continuation`（DPWSP:859）；
* **birth**（`t` 恰为 event 时刻）：`distinct_pole_birth_minimum_receives_first_incoming_stage`
  （`DistinctPoleBirthStagePropagationPortC11P:135`）——树内已有，**不是**新缺口；
* **event**（`k = √(t − time i.succ) ∈ (0, c]`）：闭侧 (7) =
  `exists_closed_event_traced_weighted_minimum_of_preceding_stage_bound`（ClosedEvent:454，
  `D := E_A`、`upper := U`）⇒ `M k ≤ U(k)` 与接触点 `q`；
  离开 event (8) = `traced_weighted_minimum_restarts_on_incoming_stage_without_loss_at_closed_poles`
  （IncomingStageWeightedRestart:587）⇒ `Icc k c` 上 `Inv`；其输入 `S, O, z, hO, hz` 由
  **`EventLowSublevelContact_C11Q4`**（D-3 冻结的中间合同，达到最小值版）给出。

request 统一取
`exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests_at_closed_poles`
（EventLocal:567，closed-pole 版：hRequest + hWindow + 无 `hpole` 的 hSupport）的 `Classical.choose`，
`Rbirth = transitionEnd + 10`、`c' = max c 1`。窗口 event 的 request 形数据 = `EventNodeData_C11Q4`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory renaming
  exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests_at_closed_poles
    → closedPoleSupport_C11Q4,
  traced_weighted_minimum_restarts_on_incoming_stage_without_loss_at_closed_poles
    → closedPoleRestart_C11Q4,
  exists_distinct_pole_half_clock_support_with_event_local_cap_requests → halfClockSupport_C11Q4

namespace GC.LongTime.Ch11

universe u

/-! ## 0. request、常数、合同 -/

/-- κ 跨 event 的 request：EventLocal:567（closed-pole exclusion 版）的 `Classical.choose`，
`a₀ = windowBarrierA₀_C11Q2 P₀ g₀`、`c' = max c 1`、`Rbirth = transitionEnd + 10`。 -/
def kappaEventRequest_C11Q4 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (c : ℝ)
    (Cderiv : ℝ≥0) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ :=
  Classical.choose (closedPoleSupport_C11Q4.{u} (windowBarrierA₀_C11Q2 P₀ g₀) (max c 1)
    (StandardCap.transitionEnd + 10) Cderiv (windowBarrierA₀_spec_C11Q2 P₀ g₀).1
    (lt_of_lt_of_le one_pos (le_max_right c 1)) (le_add_of_nonneg_right (by norm_num)))

/-- event 低次水平集常数 `E_A = e^{C(A)/2 + 32/√2}`（`C(A) = cutoffBarrierConst_C11Q3 A`）。 -/
def eventLevelE_C11Q4 (A : ℝ) : ℝ :=
  Real.exp (cutoffBarrierConst_C11Q3 A / 2 + 32 / Real.sqrt 2)

/-- **窗口 event 的 node 数据**（request 形；R-C11-4 D-2 fine-cap 请求的 event 版）：半窗口
`t − r²/2 ≤ time i.succ` 内每个 event 的 request 输入 `(nodeA, nodeE, nodeR, nodeQ, nodeRho)`
满足 DPWSP / restart 同形条款（δ、neck、后续 delta、导数），外加 `nodeR ≤ r`、`r/√2 ≤ nodeE`、
`(E_A + 1) r ≤ nodeA`，以及请求精度上的 **uniform** presented static cap family。 -/
def EventNodeData_C11Q4 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Cderiv : ℝ≥0)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier) (r A : ℝ)
    (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ) : Prop :=
  ∀ i : Fin H.eventCount, i.succ ≤ H.activeStage t → t.val - r ^ 2 / 2 ≤ H.time i.succ →
    0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧
    r / Real.sqrt 2 ≤ nodeE i ∧ nodeR i ≤ r ∧
    H.isParabolicallyRmControlledBall t x (nodeR i) ∧
    parameters.delta (H.time i.succ) ≤
      (kappaEventRequest_C11Q4 P₀ g₀ parameters.recenterConstant Cderiv
        (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.2.2 ∧
    parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
    (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
      ∀ b, (records j).delta b ≤
        (kappaEventRequest_C11Q4 P₀ g₀ parameters.recenterConstant Cderiv
          (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.2.2) ∧
    (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
      ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
        nodeQ i < metricScalarAt (H.stageMetric j s) y →
        |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
          Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
    (∃ (Dcap εcap : ℝ) (ncap : ℕ)
      (S : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap parameters.fixed Dcap ncap εcap c),
      (kappaEventRequest_C11Q4 P₀ g₀ parameters.recenterConstant Cderiv
        (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.1 ≤ Dcap ∧
      (kappaEventRequest_C11Q4 P₀ g₀ parameters.recenterConstant Cderiv
        (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.2.1 ≤ ncap ∧
      εcap ≤ (kappaEventRequest_C11Q4 P₀ g₀ parameters.recenterConstant Cderiv
        (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).1 ∧
      (∀ c, (S c).hasCanonicalWindow) ∧
      ∀ c, (S c).neck.scale = ((records i).static c).neck.scale) ∧
    (eventLevelE_C11Q4 A + 1) * r ≤ nodeA i

/-- **EventLowSublevelContact**（R-C11-4 D-3 冻结的中间合同，达到最小值版）：对种子的每个 event
`i`（clock `k ∈ (0, r/√2]`，`t − k² = time i.succ`），post stage 的加权 cost 的 minimizer `q`，只要
`regularizedCost q = L ≤ (E_A − 1) r`（低次水平集），就有该 event 的 uniform presented static caps
（`εcap ≤ 1/2`、`Dcap > transitionEnd + 10`、canonical）与 old lifts `O`（种子 trace 过 event）、`z`
（`oldOutput z = q`），两者都在扩大 cap core `{‖y‖ ≤ transitionEnd + 10}` 之外。 -/
def EventLowSublevelContact_C11Q4 (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (a₀ : ℝ) (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p) : Prop :=
  ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t) (k : ℝ), 0 < k →
    k ^ 2 ≤ r ^ 2 / 2 → t.val - k ^ 2 = H.time i.succ →
    ∀ (hfPost : H.activeStage aSeed ≤ i.succ) (q : (H.stage i.succ).Carrier) (L : ℝ),
      (∀ y : (H.stage i.succ).Carrier,
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
            (seedTrace.point i.succ hfPost hl) q ≤
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
            (seedTrace.point i.succ hfPost hl) y) →
      H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x q = (L : WithTop ℝ) →
      L ≤ (eventLevelE_C11Q4 A - 1) * r →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      ∃ (Dcap εcap : ℝ) (ncap : ℕ)
        (S : ∀ c : (H.event i).RetainedBoundaryIndex,
          (H.event i).PresentedStaticCap parameters.fixed Dcap ncap εcap c),
        (∀ c, (S c).hasCanonicalWindow) ∧ εcap ≤ 1 / 2 ∧
        StandardCap.transitionEnd + 10 < Dcap ∧
        ∃ O z : (H.event i).old,
          O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
          (H.event i).oldOutput O = seedTrace.point i.succ hfPost hl ∧
          (H.event i).oldOutput z = q ∧
          (∀ c, (H.event i).oldOutput O ∉ (S c).window ''
            {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
          (∀ c, (H.event i).oldOutput z ∉ (S c).window ''
            {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})

/-! ## 1. 初等引理 -/

/-- `0 ≤ C(A)`（`0 ≤ A`）。 -/
theorem cutoffBarrierConst_nonneg_C11Q4 {A : ℝ} (hA : 0 ≤ A) : 0 ≤ cutoffBarrierConst_C11Q3 A := by
  unfold cutoffBarrierConst_C11Q3
  apply DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg
  nlinarith [sq_nonneg DifferentialGeometry.Analysis.CutoffProfile.derivBound]

/-- `k² ≤ r²/2` ⇒ 指数 `Ck²/r² + 32k/r ≤ C/2 + 32/√2`。 -/
theorem clock_exponent_le_C11Q4 {C r k : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hk : 0 ≤ k)
    (hhalf : k ^ 2 ≤ r ^ 2 / 2) :
    C * k ^ 2 / r ^ 2 + 32 * k / r ≤ C / 2 + 32 / Real.sqrt 2 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hkr : k / r ≤ 1 / Real.sqrt 2 := by
    apply (div_le_div_iff₀ hr hsqrt).mpr
    have hsq : (k * Real.sqrt 2) ^ 2 ≤ r ^ 2 := by
      rw [mul_pow, hsqrt2]
      linarith
    simpa only [one_mul] using (sq_le_sq₀ (mul_nonneg hk hsqrt.le) hr.le).mp hsq
  have hquad : C * k ^ 2 / r ^ 2 ≤ C / 2 := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hC
    nlinarith only [hh]
  have hlin : 32 * k / r ≤ 32 / Real.sqrt 2 := by
    simpa only [← mul_div_assoc, mul_one] using
      mul_le_mul_of_nonneg_left hkr (by norm_num : (0 : ℝ) ≤ 32)
  linarith

/-- `0 < c ≤ r/√2` ⇒ `c² ≤ r²/2`。 -/
theorem sq_le_half_of_le_C11Q4 {c r : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ r / Real.sqrt 2) :
    c ^ 2 ≤ r ^ 2 / 2 := by
  have h := pow_le_pow_left₀ hc0 hc 2
  rwa [div_pow, Real.sq_sqrt (by norm_num)] at h

/-- WithTop 形：`M ≠ ⊤` 且 `M.untopD 0 ≤ u` ⇒ `M ≤ ↑u`。 -/
theorem le_coe_of_untopD_le_C11Q4 {M : WithTop ℝ} {u : ℝ} (hM : M ≠ ⊤) (h : M.untopD 0 ≤ u) :
    M ≤ (u : WithTop ℝ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hM
  rw [← hm] at h ⊢
  rw [WithTop.untopD_coe] at h
  exact WithTop.coe_le_coe.mpr h

/-- 闭侧入口时钟：`t − k² = time i.succ`（`0 < k`）⇒ `∃ a ∈ (0, k)`，`t − a² < stageEndTime i.succ`。 -/
theorem exists_entry_clock_C11Q4 (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (i : Fin H.eventCount) {k : ℝ} (hk : 0 < k) (hevent : t.val - k ^ 2 = H.time i.succ) :
    ∃ a : ℝ, 0 < a ∧ a < k ∧ t.val - a ^ 2 < H.stageEndTime i.succ := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hcases : H.time i.succ < H.stageEndTime i.succ ∨ i.succ = Fin.last H.eventCount := by
    generalize i.succ = j
    cases j using Fin.lastCases with
    | last => exact Or.inr rfl
    | cast j =>
      left
      rw [H.stageEndTime_castSucc]
      exact H.time_strictMono j.castSucc_lt_succ
  have hend : t.val - k ^ 2 < H.stageEndTime i.succ := by
    rcases hcases with h | h
    · rw [hevent]
      exact h
    · rw [h, H.stageEndTime_last]
      have := t.2.2
      linarith
  have hmax : max (t.val - H.stageEndTime i.succ) 0 < k ^ 2 := max_lt (by linarith) hk2
  have hle1 := le_max_left (t.val - H.stageEndTime i.succ) 0
  have hle2 := le_max_right (t.val - H.stageEndTime i.succ) 0
  have hs0 : 0 < (max (t.val - H.stageEndTime i.succ) 0 + k ^ 2) / 2 := by linarith
  refine ⟨Real.sqrt ((max (t.val - H.stageEndTime i.succ) 0 + k ^ 2) / 2),
    Real.sqrt_pos.mpr hs0, ?_, ?_⟩
  · exact (Real.sqrt_lt' hk).mpr (by linarith)
  · rw [Real.sq_sqrt hs0.le]
    linarith

/-! ## 2. 三类单步 -/

/-- **base 步**（DPWSP:859）：`activeStage t` 的起点早于 `t − c²`（`0 < c ≤ r/√2`）⇒ `Inv(c)`。 -/
theorem tracedMin_le_of_stageStart_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : ObservedHistory.{u}) (identification : InitialIdentification P g H)
    (parameters : CutoffParameters) (records : ∀ j, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) {r A ϱ₀ : ℝ}
    (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val) (hseed : H.isParabolicallyRmControlledBall t p r)
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r))
    (htest : H.isParabolicallyRmControlledBall t x ϱ₀)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    {c : ℝ} (hc0 : 0 < c) (hc : c ≤ r / Real.sqrt 2)
    (hage : H.time (H.activeStage t) < t.val - c ^ 2) :
    ∀ w ∈ Ioc (0 : ℝ) c,
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
          (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ) := by
  have hr : 0 < r := hseed.1
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  have hinit := hspec.2.1 H identification
  have hc4 : 0 < parameters.recenterConstant :=
    lt_of_lt_of_le (by norm_num) parameters.recenterConstant_ge_four
  have hex := halfClockSupport_C11Q4.{u} (windowBarrierA₀_C11Q2 P g) parameters.recenterConstant
    StandardCap.transitionEnd 0 hspec.1 hc4 le_rfl
  obtain ⟨request, -, hSupport⟩ := hex
  have hDP := ObservedHistory.distinct_pole_initial_minimum_receives_pole_stage_continuation
    (windowBarrierA₀_C11Q2 P g) parameters.recenterConstant 0 hspec.1 request hSupport H
    parameters records le_rfl hinit.1 hinit.2 t p x r A hr hA hT hseed aSeed hSeedTime
    hSeedClock seedTrace ϱ₀ c hc0 (sq_le_half_of_le_C11Q4 hc0.le hc) hage htest hdist
  intro w hw
  have h1 := hDP.1 w hw
  dsimp only at h1
  obtain ⟨hne, -, hle⟩ := h1
  exact le_coe_of_untopD_le_C11Q4 hne hle

/-- **birth 步**（t 恰为 event 时刻，`DistinctPoleBirthStagePropagationPortC11P:135`）：
`activeStage t = i.succ`、`t = time i.succ`、`time i.castSucc < t − c²` ⇒ `Inv(c)`；pole event 的
request 数据与 uniform caps 取自 `EventNodeData_C11Q4`。 -/
theorem tracedMin_le_of_birth_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (Cderiv : ℝ≥0) (H : ObservedHistory.{u}) (identification : InitialIdentification P g H)
    (parameters : CutoffParameters) (records : ∀ j, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) {r A : ℝ}
    (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val) (hseed : H.isParabolicallyRmControlledBall t p r)
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r))
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    {nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ}
    (hnode : EventNodeData_C11Q4 P g Cderiv H parameters records t x r A
      nodeA nodeE nodeR nodeQ nodeRho)
    (i : Fin H.eventCount) (hactive : H.activeStage t = i.succ)
    (hbirth : t.val = H.time i.succ) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ r / Real.sqrt 2)
    (hage : H.time i.castSucc < t.val - c ^ 2) :
    ∀ w ∈ Ioc (0 : ℝ) c,
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
          (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ) := by
  have hr : 0 < r := hseed.1
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  have hinit := hspec.2.1 H identification
  have hex := closedPoleSupport_C11Q4.{u} (windowBarrierA₀_C11Q2 P g)
    (max parameters.recenterConstant 1) (StandardCap.transitionEnd + 10) Cderiv hspec.1
    (lt_of_lt_of_le one_pos (le_max_right _ 1)) (le_add_of_nonneg_right (by norm_num))
  have hreq := Classical.choose_spec hex
  obtain ⟨hRequest, hWindow, hSupport⟩ := hreq
  have hwin : t.val - r ^ 2 / 2 ≤ H.time i.succ := by
    rw [← hbirth]
    nlinarith [sq_nonneg r]
  have hN := hnode i hactive.symm.le hwin
  obtain ⟨hE, hR, hQ, hRho, hEge, hRle, hball, hdelta, hneck, -, -, hcaps, hfit⟩ := hN
  obtain ⟨Dcap, εcap, ncap, S, hDcap, hncap, hεcap, hcan, hscale⟩ := hcaps
  have hB := ObservedHistory.distinct_pole_birth_minimum_receives_first_incoming_stage
    (windowBarrierA₀_C11Q2 P g) (max parameters.recenterConstant 1) Cderiv hspec.1
    (kappaEventRequest_C11Q4 P g parameters.recenterConstant Cderiv) hRequest hWindow hSupport
    H parameters records (le_max_left _ _) hinit.1 hinit.2 t p x r A hr hA hT hseed hdist
    aSeed hSeedTime hSeedClock seedTrace i hactive hbirth c (nodeA i) (nodeE i) (nodeR i)
    (nodeQ i) (nodeRho i) hc0 (sq_le_half_of_le_C11Q4 hc0.le hc) hage hE hR hQ hRho
    (hc.trans hEge) hRle hball hfit hdelta hneck S hDcap hncap hεcap hcan hscale
  obtain ⟨_hfS, hB1⟩ := hB
  intro w hw
  have h1 := hB1.1 w hw
  dsimp only at h1
  obtain ⟨hne, -, hle⟩ := h1
  exact le_coe_of_untopD_le_C11Q4 hne hle

/-- **event 步**（R-C11-4 D-3 的 (7) + (8)）：event `i`，clock `k = √(t − time i.succ) ∈ (0, c]`，
`c ≤ r/√2`、`time i.castSucc < t − c²`；`(0, k)` 上 `Inv` 已知 ⇒ `Icc k c` 上 `Inv`。
闭侧 = ClosedEvent:454（`D := E_A`、`upper := U`）；`k < c` 时离开 event = restart (closed poles)，
`S, O, z` 由 `EventLowSublevelContact_C11Q4` 在闭侧接触点上给出，node 数据由 `EventNodeData_C11Q4`。 -/
theorem tracedMin_le_of_eventStep_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (Cderiv : ℝ≥0) (H : ObservedHistory.{u}) (identification : InitialIdentification P g H)
    (parameters : CutoffParameters) (records : ∀ j, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) {r A : ℝ}
    (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val) (hseed : H.isParabolicallyRmControlledBall t p r)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    {nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ}
    (hnode : EventNodeData_C11Q4 P g Cderiv H parameters records t x r A
      nodeA nodeE nodeR nodeQ nodeRho)
    (hcontact : EventLowSublevelContact_C11Q4 H parameters (windowBarrierA₀_C11Q2 P g) t p x r A
      aSeed hSeedTime seedTrace)
    (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t) {k c : ℝ} (hk : 0 < k)
    (hkc : k ≤ c) (hc : c ≤ r / Real.sqrt 2) (hevent : t.val - k ^ 2 = H.time i.succ)
    (hclockEnd : H.time i.castSucc < t.val - c ^ 2)
    (hbelow : ∀ w ∈ Ioo (0 : ℝ) k,
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
          (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ)) :
    ∀ w ∈ Icc k c,
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
          (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ) := by
  have hr : 0 < r := hseed.1
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  have hinit := hspec.2.1 H identification
  have hC : 0 ≤ cutoffBarrierConst_C11Q3 A := cutoffBarrierConst_nonneg_C11Q4 (by linarith)
  have hc2 : c ^ 2 ≤ r ^ 2 / 2 := sq_le_half_of_le_C11Q4 (hk.le.trans hkc) hc
  have hk2 : k ^ 2 ≤ r ^ 2 / 2 := (pow_le_pow_left₀ hk.le hkc 2).trans hc2
  obtain ⟨a, ha, hak, hentry⟩ := exists_entry_clock_C11Q4 H t i hk hevent
  have hbudget : 2 * r * k * Real.exp (cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 + 32 * k / r) ≤
      2 * r * k * eventLevelE_C11Q4 A :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (clock_exponent_le_C11Q4 hC hr hk.le hk2))
      (by positivity)
  have hCE := H.exists_closed_event_traced_weighted_minimum_of_preceding_stage_bound parameters
    records (windowBarrierA₀_C11Q2 P g) hspec.1 hinit.1 hinit.2 t p x r A (eventLevelE_C11Q4 A)
    a k hr ha hak hk2 hT aSeed hSeedTime hSeedClock seedTrace i hl hevent hentry
    (fun w => 2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r))
    (by fun_prop) hbudget (fun w hw => hbelow w ⟨ha.trans_le hw.1, hw.2⟩)
  dsimp only at hCE
  obtain ⟨hfPost, q, L, m, hMk, hWmin, hMinimum, hCost, hInside, -, -, hmUpper, -, hLbound, -⟩ :=
    hCE
  have hMkle : H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
      (3 / windowBarrierA₀_C11Q2 P g) r A k ≤
      ((2 * r * k * Real.exp (cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 + 32 * k / r) : ℝ) :
        WithTop ℝ) := by
    rw [hMk]
    exact WithTop.coe_le_coe.mpr hmUpper
  rcases eq_or_lt_of_le hkc with hkc' | hkc'
  · intro w hw
    have hwk : w = k := le_antisymm (hw.2.trans_eq hkc'.symm) hw.1
    rw [hwk]
    exact hMkle
  have hcon := hcontact i hl k hk hk2 hevent hfPost q L hMinimum hCost hLbound
  obtain ⟨hfSeed, Dcap, εcap, ncap, S, hcan, hε, hD, O, z, hOin, hOout, hzEnd, hO, hz⟩ := hcon
  have hpostMetric : H.stageMetric i.succ (t.val - k ^ 2) = (H.event i).outputMetric := by
    rw [hevent, H.stageMetric_initial]
    exact (H.event_output i).symm
  have hInsideEvent : riemannianEDistOf (H.event i).outputMetric
      ((H.event i).oldOutput O) ((H.event i).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) := by
    simpa only [hpostMetric, hOout, hzEnd] using hInside
  have hCostEvent : H.regularizedCost i.succ (H.activeStage t) hl t.val
      (3 / windowBarrierA₀_C11Q2 P g) 0 k x ((H.event i).oldOutput z) = (L : WithTop ℝ) := by
    rw [hzEnd]
    exact hCost
  have hContact : H.physicalWeightedCost i.succ (H.activeStage t) hl t.val
      (3 / windowBarrierA₀_C11Q2 P g) r A k x ((H.event i).oldOutput O)
      ((H.event i).oldOutput z) =
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
        (3 / windowBarrierA₀_C11Q2 P g) r A k := by
    rw [hOout, hzEnd]
    exact hWmin.trans hMk.symm
  have hNormalized : Real.exp (-cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 - 32 * k / r) *
      (H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
        (3 / windowBarrierA₀_C11Q2 P g) r A k).untopD 0 / k ≤ 2 * r := by
    rw [hMk, WithTop.untopD_coe]
    apply (div_le_iff₀ hk).mpr
    have hcancel : Real.exp (-cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 - 32 * k / r) *
        Real.exp (cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 + 32 * k / r) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 2
      ring
    have hmU : m ≤ 2 * r * k *
        Real.exp (cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 + 32 * k / r) := hmUpper
    have hmul := mul_le_mul_of_nonneg_left hmU
      (Real.exp_pos (-cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 - 32 * k / r)).le
    calc
      Real.exp (-cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 - 32 * k / r) * m ≤
          Real.exp (-cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 - 32 * k / r) *
            (2 * r * k * Real.exp (cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 + 32 * k / r)) :=
        hmul
      _ = 2 * r * k * (Real.exp (-cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 - 32 * k / r) *
            Real.exp (cutoffBarrierConst_C11Q3 A * k ^ 2 / r ^ 2 + 32 * k / r)) := by ring
      _ = 2 * r * k := by rw [hcancel, mul_one]
  have hwinOf (j : Fin H.eventCount) (hij : i.castSucc ≤ j.castSucc) :
      t.val - r ^ 2 / 2 ≤ H.time j.succ := by
    have hsucc : i.succ ≤ j.succ := by
      change i.val + 1 ≤ j.val + 1
      change i.val ≤ j.val at hij
      omega
    have hmono := H.time_strictMono.monotone hsucc
    linarith
  have hex := closedPoleSupport_C11Q4.{u} (windowBarrierA₀_C11Q2 P g)
    (max parameters.recenterConstant 1) (StandardCap.transitionEnd + 10) Cderiv hspec.1
    (lt_of_lt_of_le one_pos (le_max_right _ 1)) (le_add_of_nonneg_right (by norm_num))
  have hreq := Classical.choose_spec hex
  obtain ⟨-, -, hSupport⟩ := hreq
  have hR := closedPoleRestart_C11Q4 (windowBarrierA₀_C11Q2 P g)
    (max parameters.recenterConstant 1) Cderiv hspec.1
    (kappaEventRequest_C11Q4 P g parameters.recenterConstant Cderiv) hSupport H parameters
    records (le_max_left _ _) hinit.1 hinit.2 t p x r A hr hA hT hseed aSeed hSeedTime
    hSeedClock seedTrace k c hk hkc' hc2 i hfSeed hl hevent S hcan hε hD O z hOin hO hz L
    hInsideEvent hCostEvent hContact hclockEnd
  have hR' := hR nodeA nodeE nodeR nodeQ nodeRho
    (fun j hij hj => by
      obtain ⟨hE, hR0, hQ, hRho, hEge, -, hball, hdelta, hneck, hlater, hderiv, hcaps, -⟩ :=
        hnode j hj (hwinOf j hij)
      obtain ⟨Dcap', εcap', ncap', S', hD', hn', hε', hcan', hscale'⟩ := hcaps
      exact ⟨hE, hR0, hQ, hRho, hc.trans hEge, hball, hdelta, hneck, hlater, hderiv,
        fun b => ⟨Dcap', εcap', ncap', S' b, hD', hn', hε', hcan' b, hscale' b⟩⟩)
    (fun j hij hj => (hnode j hj (hwinOf j hij)).2.2.2.2.2.2.2.2.2.2.2.2) hNormalized
  intro w hw
  exact le_coe_of_untopD_le_C11Q4 (hR'.1 w hw).1 (hR'.2.2 w hw).2

end GC.LongTime.Ch11

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEventStepC11Q4

/-!
# κ 线跨 event 归纳（O-CH11-KAPPA3 G1，后缀 `_C11Q4`；R-C11-4 D-3）

对 stage 递减归纳 `Q(j) := ∀ c ∈ (0, r/√2], time j < t − c² → Inv(c)`
（`Inv(c) := ∀ w ∈ Ioc 0 c, M w ≤ ↑(2rw·e^{C(A)w²/r² + 32w/r})`）：
* `Q(activeStage t)` = base 步（DPWSP:859）；
* `Q(i.succ) → Q(i.castSucc)`：`time i.succ < t − c²` 直接继承；否则 event `i` 落在 `[t − c², t]`：
  `time i.succ = t` ⇒ birth 步（t 恰为 event 时刻，树内 `DistinctPoleBirthStagePropagation`）；
  `time i.succ < t` ⇒ `k = √(t − time i.succ) ∈ (0, c]`，`(0, k)` 由 `Q(i.succ)`，`[k, c]` 由 event 步
  （闭侧 + `EventLowSublevelContact_C11Q4` + restart）；
* 终止于 `activeStage aSeed`（`time ≤ t − r² < t − r²/2`）。
不重置时钟、不逐 event 损失乘法因子（D-3）。G1 主定理：
`tracedMin_le_of_eventContact_C11Q4`（逐种子）与 `weightedMinBoundEnd_of_event_C11Q4`
（`WeightedMinBoundEnd_C11Q3` 的全称形：无 event 种子走 KAPPA2 Q3-G1，有 event 种子走本归纳）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **跨 event 归纳（逐种子）**：`1 ≤ A`、种子 `(p, t, r)`、trace、极点 `x ∈ B(p, Ar)`（任一受控球
`ϱ₀`）、窗口 event 的 node 数据与 `EventLowSublevelContact_C11Q4` ⇒ `0 < w ≤ r/√2` 上
`M w ≤ 2rw·e^{C(A)w²/r² + 32w/r}`（有无 event、t 是否为 event 时刻都覆盖）。 -/
theorem tracedMin_le_of_eventContact_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (Cderiv : ℝ≥0) (H : ObservedHistory.{u}) (identification : InitialIdentification P g H)
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
    {nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ}
    (hnode : EventNodeData_C11Q4 P g Cderiv H parameters records t x r A
      nodeA nodeE nodeR nodeQ nodeRho)
    (hcontact : EventLowSublevelContact_C11Q4 H parameters (windowBarrierA₀_C11Q2 P g) t p x r A
      aSeed hSeedTime seedTrace) :
    ∀ w ∈ Ioc (0 : ℝ) (r / Real.sqrt 2),
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
          (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ) := by
  have hr : 0 < r := hseed.1
  have hmain : ∀ n : ℕ, ∀ j : Fin (H.eventCount + 1), j.val + n = (H.activeStage t).val →
      ∀ c : ℝ, 0 < c → c ≤ r / Real.sqrt 2 → H.time j < t.val - c ^ 2 →
      ∀ w ∈ Ioc (0 : ℝ) c,
        H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
            (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
          ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
            WithTop ℝ) := by
    intro n
    induction n with
    | zero =>
      intro j hj c hc0 hc hage
      have hjl : j = H.activeStage t := Fin.ext (by simpa using hj)
      subst hjl
      exact tracedMin_le_of_stageStart_C11Q4 H identification parameters records t p x hA hT
        hseed hdist htest aSeed hSeedTime hSeedClock seedTrace hc0 hc hage
    | succ n ih =>
      intro j hj c hc0 hc hage
      have hjlt : j.val < H.eventCount := by
        have := (H.activeStage t).isLt
        omega
      obtain ⟨i, rfl⟩ : ∃ i : Fin H.eventCount, j = i.castSucc := ⟨⟨j.val, hjlt⟩, Fin.ext rfl⟩
      change i.val + (n + 1) = (H.activeStage t).val at hj
      have hil : i.succ ≤ H.activeStage t := by
        change i.val + 1 ≤ (H.activeStage t).val
        omega
      have hIH := ih i.succ (by change i.val + 1 + n = (H.activeStage t).val; omega)
      rcases lt_or_ge (H.time i.succ) (t.val - c ^ 2) with hlt | hge
      · exact hIH c hc0 hc hlt
      have hsuccLe : H.time i.succ ≤ t.val :=
        (H.time_strictMono.monotone hil).trans (H.activeStage_time_le t)
      rcases eq_or_lt_of_le hsuccLe with hbirth | htlt
      · have hactive : H.activeStage t = i.succ := by
          refine le_antisymm ?_ hil
          by_contra hne
          have hlt' : i.succ < H.activeStage t := lt_of_not_ge hne
          have h1 := H.time_strictMono hlt'
          have h2 := H.activeStage_time_le t
          linarith
        exact tracedMin_le_of_birth_C11Q4 Cderiv H identification parameters records t p x hA hT
          hseed hdist aSeed hSeedTime hSeedClock seedTrace hnode i hactive hbirth.symm hc0 hc hage
      have hkpos : 0 < t.val - H.time i.succ := by linarith
      obtain ⟨k, hk, hksq⟩ : ∃ k : ℝ, 0 < k ∧ k ^ 2 = t.val - H.time i.succ :=
        ⟨Real.sqrt _, Real.sqrt_pos.mpr hkpos, Real.sq_sqrt hkpos.le⟩
      have hevent : t.val - k ^ 2 = H.time i.succ := by linarith
      have hkc : k ≤ c := (sq_le_sq₀ hk.le hc0.le).mp (by linarith)
      have hbelow : ∀ w ∈ Ioo (0 : ℝ) k,
          H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
              (3 / windowBarrierA₀_C11Q2 P g) r A w ≤
            ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) :
              ℝ) : WithTop ℝ) := by
        intro w hw
        have hw2 : w ^ 2 < k ^ 2 := pow_lt_pow_left₀ hw.2 hw.1.le two_ne_zero
        exact hIH w hw.1 (hw.2.le.trans (hkc.trans hc)) (by linarith) w ⟨hw.1, le_rfl⟩
      have hstep := tracedMin_le_of_eventStep_C11Q4 Cderiv H identification parameters records t
        p x hA hT hseed aSeed hSeedTime hSeedClock seedTrace hnode hcontact i hil hk hkc hc
        hevent hage hbelow
      intro w hw
      rcases lt_or_ge w k with hwk | hwk
      · exact hbelow w ⟨hw.1, hwk⟩
      · exact hstep w ⟨hwk, hw.2⟩
  have hlast : (H.activeStage aSeed).val ≤ (H.activeStage t).val := H.activeStage_mono hSeedTime
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hb2 : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have hseedTime := H.activeStage_time_le aSeed
  have hr2 : 0 < r ^ 2 := by positivity
  exact hmain ((H.activeStage t).val - (H.activeStage aSeed).val) (H.activeStage aSeed)
    (by omega) (r / Real.sqrt 2) (div_pos hr hs2) le_rfl (by rw [hb2]; linarith)

/-- **`WeightedMinBoundEnd_C11Q3` 的全称形（G1）**：records（同一 `params`）下，无 event 半窗口的
种子由 KAPPA2 Q3-G1（`weightedMinBoundEnd_of_noEvent_C11Q3`）给出；半窗口内有 event 的种子（`hEvent`）
由本归纳给出，显式输入 = 每个这样的种子（`A' = max A 1`）的 `EventNodeData_C11Q4` 与
`EventLowSublevelContact_C11Q4`。 -/
theorem weightedMinBoundEnd_of_event_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hcontact : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
          (H.activeStage_mono hbt) p,
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        EventLowSublevelContact_C11Q4 H params (windowBarrierA₀_C11Q2 P g) t p x r (max A 1) b
          hbt seedTrace) :
    WeightedMinBoundEnd_C11Q3 F δ α nr (fun A => cutoffBarrierConst_C11Q3 (max A 1)) := by
  refine weightedMinBoundEnd_of_noEvent_C11Q3 params records ?_
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf hev
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hA1 : 1 ≤ max A 1 := le_max_right _ _
  have hx' : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (max A 1 * r) :=
    lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0.le))
  have hN := hnode A hA n t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball hev
  obtain ⟨nodeA, nodeE, nodeR, nodeQ, nodeRho, hN'⟩ := hN
  have hC := hcontact A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball hev
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  have hbound := tracedMin_le_of_eventContact_C11Q4 Cderiv H (F.tower.initial n) params
    (records n) t p x hA1 hr (isParabolicallyRmControlledBall_of_seed_C11Q hsmall) hx' hball b hbt
    hb seedTrace hN' hC
  have h := weightedMinBound_of_traced_C11Q2 R (F.tower.initial n) (records n) hspec.1 hspec.2.1
    hBf hbt seedTrace hb x hr hbound (r / Real.sqrt 2) ⟨div_pos hr0 hs2, le_rfl⟩
  rw [cutoffMin_halfClock_eq_C11Q3 R hr0 A (max A 1) hbt seedTrace x]
  exact h

/-- **consumer（G1）**：node 数据 + contact + K3（`Λ ≥ E + 1`）⇒ K4
（`BoundedReducedLengthNearSeed_C11Q`，经 Q3-G1 的端点形 K4）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr Λ : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hcontact : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
          (H.activeStage_mono hbt) p,
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        EventLowSublevelContact_C11Q4 H params (windowBarrierA₀_C11Q2 P g) t p x r (max A 1) b
          hbt seedTrace)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A →
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A ≤ Λ A) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr
      (weightedMinLengthConst_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) :=
  boundedReducedLength_of_weightedMinBoundEnd_C11Q3
    (weightedMinBoundEnd_of_event_C11Q4 params records Cderiv hnode hcontact) hK3 hΛ

end GC.LongTime.Ch11

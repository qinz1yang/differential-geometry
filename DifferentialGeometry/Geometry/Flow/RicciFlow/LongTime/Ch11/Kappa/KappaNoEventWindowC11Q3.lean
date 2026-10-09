import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEndToEndC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedStagePropagation

/-!
# WeightedMinBound 的无 event 窗口版实例（O-CH11-KAPPA2 续窗 G1，后缀 `_C11Q3`）

树内（FIX11 G7 / FIX12 G3 落地）：
* `exists_distinct_pole_half_clock_support_with_event_local_cap_requests`
  （`Action/EventLocalWeightedTemporalSupportPortC11P:934`）给 `request` 与 half-clock 支撑 `hSupport`；
* `distinct_pole_initial_minimum_receives_pole_stage_continuation`
  （`Action/DistinctPoleWeightedStagePropagation:859`）：`hSupport` + **无 event 半窗口**
  `hage : time(activeStage t) < t − b²` + `1 ≤ A` ⇒ `0 < w ≤ b` 上 astra 的
  `tracedPhysicalWeightedMinimum ≤ 2rw·e^{C w²/r² + 32w/r}`（`C = SingularBarrier.bound(2A + …)`）。

本文件：
* `cutoffMin_le_of_noEventWindow_C11Q3`：逐种子把上式经 `weightedMinBound_of_traced_C11Q2` 换成本链的
  `cutoffMin_C11Q`（任一真实地板 `Bf`），`b = r/√2`；
* **端点形** `WeightedMinBoundEnd_C11Q3`：K4 只用 `v₁ = r/√2` 一点，而该点 cutoff 的
  `shift = A(1 − 2v₁²/r²) = 0` 与 `A` 无关（`cutoffMin_halfClock_eq_C11Q3`），所以 `A < 1` 的种子借
  `A' = 1` 处理，`C(A) = cutoffBarrierConst_C11Q3 (max A 1)`；
* `boundedReducedLength_of_weightedMinBoundEnd_C11Q3`：端点形 + K3 ⇒ K4（`WeightedMinBound_C11Q2 ⇒` 端点形）；
* `weightedMinBoundEnd_of_noEvent_C11Q3`：native records 下，**无 event 半窗口的种子由树内定理给出**，
  有 event 的种子是唯一剩余前提 `hEvent`（G2 跨 event 归纳的目标）。
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

/-- astra 的 weighted 常数 `C(A) = SingularBarrier.bound(2A + 160·derivBound² + 3/40)`。 -/
def cutoffBarrierConst_C11Q3 (A : ℝ) : ℝ :=
  DifferentialGeometry.Analysis.SingularBarrier.bound
    (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)

/-! ## 1. 逐种子：无 event 半窗口 ⇒ 积分形上界 -/

/-- **无 event 半窗口的 WeightedMinBound（逐种子）**：`1 ≤ A`、种子 `(p, t, r)`、trace、基点
`x ∈ B(p, Ar)`（受控球 `ϱ₀`）、真实地板 `Bf`，且 `activeStage t` 起点早于 `t − r²/2` ⇒
`0 < w ≤ r/√2` 上 `cutoffMin ≤ 2rw·e^{C(A)w²/r² + 32w/r}`。 -/
theorem cutoffMin_le_of_noEventWindow_C11Q3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (identification : InitialIdentification P g R.toHistory)
    {params : CutoffParameters} (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf)
    (t : Icc (0 : ℝ) R.toHistory.horizon) (p x : (R.toHistory.stageAt t).Carrier) {r A : ℝ}
    (hA : 1 ≤ A) (hT : 2 * r ^ 2 < (t : ℝ)) (hseed : hasSmallParabolicCurvature R.toHistory t p r)
    {b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) (hb : (b : ℝ) = (t : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (hx : x ∈ riemannianBallOf (R.toHistory.stageMetric (R.toHistory.activeStage t) t) p (A * r))
    {ϱ₀ : ℝ} (hball : R.toHistory.isParabolicallyRmControlledBall t x ϱ₀)
    (hage : R.toHistory.time (R.toHistory.activeStage t) < (t : ℝ) - r ^ 2 / 2) :
    ∀ w ∈ Ioc 0 (r / Real.sqrt 2),
      cutoffMin_C11Q R Bf r A hbt seedTrace x w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ) := by
  have hr : 0 < r := hseed.1
  obtain ⟨a₀, ha₀, hinit⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  have hstart := hinit R.toHistory identification
  have hc : 0 < params.recenterConstant :=
    lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four
  obtain ⟨request, -, hSupport⟩ :=
    ObservedHistory.exists_distinct_pole_half_clock_support_with_event_local_cap_requests.{u}
      a₀ params.recenterConstant StandardCap.transitionEnd 0 ha₀ hc le_rfl
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hb2 : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have hDP := ObservedHistory.distinct_pole_initial_minimum_receives_pole_stage_continuation
    a₀ params.recenterConstant 0 ha₀ request hSupport R.toHistory params records le_rfl
    hstart.1 hstart.2 t p x r A hr hA hT (isParabolicallyRmControlledBall_of_seed_C11Q hseed)
    b hbt hb seedTrace ϱ₀ (r / Real.sqrt 2) (div_pos hr hs2) hb2.le (by rw [hb2]; exact hage)
    hball hx
  have hbound : ∀ w ∈ Ioc (0 : ℝ) (r / Real.sqrt 2),
      R.toHistory.tracedPhysicalWeightedMinimum b t hbt p x seedTrace (3 / a₀) r A w ≤
        ((2 * r * w * Real.exp (cutoffBarrierConst_C11Q3 A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) :
          WithTop ℝ) := by
    intro w hw
    have h1 := hDP.1 w hw
    dsimp only at h1
    obtain ⟨hne, -, hle⟩ := h1
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hm] at hle ⊢
    rw [WithTop.untopD_coe] at hle
    exact WithTop.coe_le_coe.mpr hle
  exact weightedMinBound_of_traced_C11Q2 R identification records ha₀ hinit hBf hbt seedTrace hb
    x hT hbound

/-! ## 2. 端点形：`v₁ = r/√2` 处 cutoff 与 `A` 无关 -/

/-- 半时钟终点 `v₁ = r/√2` 处 `1 − 2v₁²/r² = 0`。 -/
theorem halfClock_shift_zero_C11Q3 {r : ℝ} (hr : 0 < r) :
    1 - 2 * (r / Real.sqrt 2) ^ 2 / r ^ 2 = 0 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  field_simp
  ring

/-- **`v₁ = r/√2` 处 cutoff 最小值与 `A` 无关**（截断区 `d < r/10`、权 `φ(d/r)`）。 -/
theorem cutoffMin_halfClock_eq_C11Q3 (R : RetainedCoreHistory.{u}) {Bf r : ℝ} (hr : 0 < r)
    (A A' : ℝ) {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t)
    {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) :
    cutoffMin_C11Q R Bf r A hbt seedTrace x (r / Real.sqrt 2) =
      cutoffMin_C11Q R Bf r A' hbt seedTrace x (r / Real.sqrt 2) := by
  have h0 := halfClock_shift_zero_C11Q3 hr
  unfold cutoffMin_C11Q cutoffValue_C11Q ObservedHistory.physicalWeightedCost
  simp only [h0, mul_zero]

/-- **WeightedMinBound 端点形**（K4 实际消费的形）：同 `WeightedMinBound_C11Q2` 的绑定，只在
`w = r/√2`。 -/
def WeightedMinBoundEnd_C11Q3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (C : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
      cutoffMin_C11Q R Bf r A hbt seedTrace x (r / Real.sqrt 2) ≤
        ((2 * r * (r / Real.sqrt 2) *
          Real.exp (C A * (r / Real.sqrt 2) ^ 2 / r ^ 2 + 32 * (r / Real.sqrt 2) / r) : ℝ) :
          WithTop ℝ)

/-- 积分形 ⇒ 端点形。 -/
theorem WeightedMinBound_C11Q2.toEnd {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C) : WeightedMinBoundEnd_C11Q3 F δ α nr C := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  exact hW A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf
    (r / Real.sqrt 2) ⟨div_pos hr0 hs2, le_rfl⟩

/-- **K4 ⇐ 端点形 + K3**（与 `boundedReducedLength_of_weightedMinBound_C11Q2` 同一终点论证，只用
`v₁ = r/√2`）。 -/
theorem boundedReducedLength_of_weightedMinBoundEnd_C11Q3 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {nr C Λ : ℝ → ℝ} (hW : WeightedMinBoundEnd_C11Q3 F δ α nr C)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf s₁ hbs₁
    hs₁t hs₁
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  set v₁ : ℝ := r / Real.sqrt 2 with hv₁
  have hv₁pos : 0 < v₁ := div_pos hr0 hs2
  have hv₁mem : v₁ ∈ Ioc 0 (r / Real.sqrt 2) := ⟨hv₁pos, le_rfl⟩
  have hv₁sq : v₁ ^ 2 = r ^ 2 / 2 := by
    rw [hv₁, div_pow, Real.sq_sqrt (by norm_num)]
  obtain ⟨-, hval, hsq, -, hslice⟩ := halfClock_slice_facts_C11Q2 R hr hb hv₁mem
  set E : ℝ := Real.exp (C A / 2 + 32 / Real.sqrt 2) with hE
  have hexp : C A * v₁ ^ 2 / r ^ 2 + 32 * v₁ / r = C A / 2 + 32 / Real.sqrt 2 := by
    rw [hv₁sq, hv₁]
    field_simp
  have hM := hW A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
  rw [← hv₁, hexp] at hM
  have hK3' := hK3 A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
    v₁ hv₁mem
  have hΛA : E + 1 ≤ Λ A := hΛ A hA
  have hEpos : 0 < E := Real.exp_pos _
  have h2rv : 0 < 2 * r * v₁ := by positivity
  have hlt : cutoffMin_C11Q R Bf r A hbt seedTrace x v₁ <
      ((Λ A * (2 * r * v₁) : ℝ) : WithTop ℝ) :=
    lt_of_le_of_lt hM (WithTop.coe_lt_coe.mpr (by nlinarith))
  obtain ⟨q, hq⟩ := hK3'.2 hlt
  have hfin : cutoffMin_C11Q R Bf r A hbt seedTrace x v₁ ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hM
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hmle : m ≤ 2 * r * v₁ * E := by
    rw [← hm] at hM
    exact WithTop.coe_le_coe.mp hM
  obtain ⟨hreg, L, hL, hX⟩ :=
    cutoffValue_spec_C11Q R hbt seedTrace x hr0 hslice q (hq.trans hm.symm)
  have hLb : L ≤ (E - 1) * r := by
    have hmax : max m 0 ≤ 2 * r * v₁ * E := max_le hmle (by positivity)
    have h2v : 0 < 2 * v₁ := by positivity
    have h1 : 2 * v₁ * L ≤ 2 * v₁ * ((E - 1) * r) := by nlinarith
    exact le_of_mul_le_mul_left h1 h2v
  have hcostL : sliceCost_C11Q R Bf t (clockSlice_C11Q R t v₁) x q = L := by
    unfold sliceCost_C11Q
    rw [dite_eq_left (H.activeStage_mono hslice.2), hsq]
    exact hL
  have hregq : IsRegularMinimizerEndpoint_C11Q R Bf t (clockSlice_C11Q R t v₁) x q :=
    hK3'.1 q (by rw [hcostL]; exact WithTop.coe_le_coe.mpr (by nlinarith))
  have hs₁eq : clockSlice_C11Q R t v₁ = s₁ := Subtype.ext (by rw [hval, hs₁, hv₁sq])
  subst hs₁eq
  refine ⟨q, ?_, hregq, ?_⟩
  · change riemannianEDistOf _ _ q < ENNReal.ofReal (r / 10)
    have hrad : r * (A * (1 - 2 * v₁ ^ 2 / r ^ 2) + 1 / 10) = r / 10 := by
      rw [hv₁sq]
      field_simp
      ring
    rw [hrad, ← hval] at hreg
    exact hreg
  · rw [hcostL, hsq]
    refine WithTop.coe_le_coe.mpr ?_
    have hconst : 2 * weightedMinLengthConst_C11Q2 C A * v₁ = (E - 1) * r := by
      rw [weightedMinLengthConst_C11Q2, hv₁, ← hE]
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    rw [hconst]
    exact hLb

/-! ## 3. 无 event 种子由树内定理供给；有 event 种子是唯一剩余前提 -/

/-- **端点形的 producer（无 event 半窗口部分已证）**：records（同一 `params`）下，
`C(A) = cutoffBarrierConst_C11Q3 (max A 1)`；`activeStage t` 起点早于 `t − r²/2` 的种子由
`cutoffMin_le_of_noEventWindow_C11Q3`（`A < 1` 借 `A' = 1`）给出，其余种子（半窗口内有 event）由
`hEvent` 给出。 -/
theorem weightedMinBoundEnd_of_noEvent_C11Q3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hEvent : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
          (H.activeStage_mono hbt) p,
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
          cutoffMin_C11Q R Bf r A hbt seedTrace x (r / Real.sqrt 2) ≤
            ((2 * r * (r / Real.sqrt 2) * Real.exp
              (cutoffBarrierConst_C11Q3 (max A 1) * (r / Real.sqrt 2) ^ 2 / r ^ 2 +
                32 * (r / Real.sqrt 2) / r) : ℝ) : WithTop ℝ)) :
    WeightedMinBoundEnd_C11Q3 F δ α nr (fun A => cutoffBarrierConst_C11Q3 (max A 1)) := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf
  rcases lt_or_ge (H.time (H.activeStage t)) ((t : ℝ) - r ^ 2 / 2) with hage | hev
  · have hr0 : 0 < r := hsmall.1
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hA1 : 1 ≤ max A 1 := le_max_right _ _
    have hx' : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (max A 1 * r) := by
      change riemannianEDistOf _ p x < ENNReal.ofReal (max A 1 * r)
      exact hx.trans_le (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0.le))
    have h := cutoffMin_le_of_noEventWindow_C11Q3 R (F.tower.initial n) (records n) hBf t p x hA1
      hr hsmall hbt hb seedTrace hx' hball hage (r / Real.sqrt 2) ⟨div_pos hr0 hs2, le_rfl⟩
    rw [cutoffMin_halfClock_eq_C11Q3 R hr0 A (max A 1) hbt seedTrace x]
    exact h
  · exact hEvent A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf hev

/-- **consumer（续窗 G1）**：无 event 种子已证 + 有 event 种子的剩余前提 `hEvent` + K3（`Λ ≥ E + 1`）
⇒ K4；并与 `boundedReducedLength_of_weightedMinBound_C11Q2` 同一结论（积分形经 `.toEnd`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr Λ : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hEvent : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
          (H.activeStage_mono hbt) p,
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
          cutoffMin_C11Q R Bf r A hbt seedTrace x (r / Real.sqrt 2) ≤
            ((2 * r * (r / Real.sqrt 2) * Real.exp
              (cutoffBarrierConst_C11Q3 (max A 1) * (r / Real.sqrt 2) ^ 2 / r ^ 2 +
                32 * (r / Real.sqrt 2) / r) : ℝ) : WithTop ℝ))
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A →
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A ≤ Λ A) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr
      (weightedMinLengthConst_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) :=
  boundedReducedLength_of_weightedMinBoundEnd_C11Q3
    (weightedMinBoundEnd_of_noEvent_C11Q3 params records hEvent) hK3 hΛ

/-- 型对齐：积分形 `WeightedMinBound_C11Q2` 经 `.toEnd` 与 G2 的 K4 同结论。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C Λ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C) (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) :=
  boundedReducedLength_of_weightedMinBoundEnd_C11Q3 hW.toEnd hK3 hΛ

end GC.LongTime.Ch11

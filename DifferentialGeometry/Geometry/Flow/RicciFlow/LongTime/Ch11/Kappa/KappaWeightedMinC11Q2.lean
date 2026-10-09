import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBarrierWindowC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedMinimumPortC11P

/-!
# K1 / K2 对接合同：astra weighted-minimum 链的积分形（O-CH11-KAPPA2 G2，后缀 `_C11Q2`）

astra 的 weighted-minimum 链（donor `…/Action/{PhysicalWeightedTemporalSupport,
DistinctPoleWeightedTemporalSupport:177, ClosedEventWeightedMinimum:415}` → orphan
`HalfClockActionEndpoint:17` 的前提 `hbound`）给的是**积分形**：
`tracedPhysicalWeightedMinimum … (3/a₀) r A w ≤ 2rw·exp(C w²/r² + 32w/r)`（`0 < w ≤ r/√2`，
`C = SingularBarrier.bound(2A + 160·CutoffProfile.derivBound² + 3/40)`）。合同 K2
（`LocalizedLCutoffInequality_C11Q`）是**导数形**（`N` 连续 + 右上支撑导数 `≤ ε`），积分形推不出
导数形；而 K2 在强链里只用来产 K4。故本组：
* `WeightedMinBound_C11Q2 F δ α nr C`：积分形的显式前提，按本链对象（`cutoffMin_C11Q`，任一真实地板
  `Bf`）陈述；`weightedMinBound_of_traced_C11Q2`：astra 的原形（`tracedPhysicalWeightedMinimum`，地板
  `3/a₀`）⇒ 本形（逐种子；实际定理落地后直接喂这里）。
* **K4 ⇐ WeightedMinBound + K3**（`boundedReducedLength_of_weightedMinBound_C11Q2`，跳过 K2；照
  donor `HalfClockActionEndpoint` 的终点论证 + K3 的 regular 化）：`v₁ = r/√2` 处 `M(v₁) ≤ 2rv₁E`
  （`E = e^{C/2 + 32/√2}`），K3 子句 2 取可达点 `q`，截断区（`shift = 0`）⇒ `q ∈ B(O₁, r/10)`，
  `φ ≥ 1` ⇒ `𝓛(q) ≤ (E − 1)r`，K3 子句 1 ⇒ regular；`C₄ = (E − 1)/√2`，屏障要求 `Λ ≥ E + 1`。
* 新强链 `localKappa_of_weightedMinBound_C11Q2`：WeightedMinBound + K3 + K5a ⇒
  `LocalKappaWideSupply_C11Q`（**不再要 K1、K2**）；与 G1 窗口 K3 合成
  `localKappa_of_weightedMinBound_window_C11Q2`。
* K1：(a) 拼接在树内只有 event 处的 DP（`regularizedCost_dynamic_programming_at_event`），一般中间时刻
  的三角不等式无树内引理；(b) producer = donor `exists_physical_cost_upper_support_of_attained_action`
  （`AttainedPhysicalSupport:28`，03:3x 未落地，另要 `ContMDiffAt` 端点 C¹、可积性、`T ∈ Ioc`）。新强链
  不经 K1，K1 只剩 K5a 合同的形式输入（URE producer 不用它）。
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

/-! ## 1. 积分形前提 -/

/-- **WeightedMinBound**（astra weighted-minimum 链的结论形，显式前提）：在 accuracy 下、每个种子
`(p, t, r)`、种子 trace、基点 `x ∈ B_t(p, Ar)`（受控测试球 `ϱ₀ ≥ nr(t)/100`）与真实地板 `Bf`，半时钟
`0 < w ≤ r/√2` 上 cutoff 最小值 `M(w) ≤ 2rw·exp(C(A) w²/r² + 32w/r)`。 -/
def WeightedMinBound_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    ∀ w ∈ Ioc 0 (r / Real.sqrt 2),
      cutoffMin_C11Q R Bf r A hbt seedTrace x w ≤
        ((2 * r * w * Real.exp (C A * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) : WithTop ℝ)

/-! ## 2. 与 astra 原形对齐（`tracedPhysicalWeightedMinimum`，地板 `3/a₀`） -/

/-- 切片相等时加权极小相等（依赖类型里的切片换元）。 -/
theorem sInf_physicalWeightedCost_congr_slice_C11Q2 (H : ObservedHistory.{u})
    {t b : Icc (0 : ℝ) H.horizon} (hbt : b ≤ t) {p : (H.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p)
    (x : (H.stageAt t).Carrier) (B r A w : ℝ) {s s' : Icc (0 : ℝ) H.horizon} (hss : s = s')
    (h₁ : b ≤ s) (h₂ : s ≤ t) (h₁' : b ≤ s') (h₂' : s' ≤ t) :
    sInf (Set.range (H.physicalWeightedCost (H.activeStage s) (H.activeStage t)
      (H.activeStage_mono h₂) t B r A w x
      (seedTrace.point (H.activeStage s) (H.activeStage_mono h₁) (H.activeStage_mono h₂)))) =
    sInf (Set.range (H.physicalWeightedCost (H.activeStage s') (H.activeStage t)
      (H.activeStage_mono h₂') t B r A w x
      (seedTrace.point (H.activeStage s') (H.activeStage_mono h₁') (H.activeStage_mono h₂'))))
    := by
  subst hss
  rfl

/-- 地板换算：两真实地板下的加权 cutoff 值相等。 -/
theorem physicalWeightedCost_eq_of_floor_C11Q2 {H : ObservedHistory.{u}} {b : ℝ}
    (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.stageMetric j t) x)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T : ℝ) {B C : ℝ}
    (hB : b ≤ B) (hC : b ≤ C) (r A v : ℝ) (p : (H.stage last).Carrier)
    (O q : (H.stage first).Carrier) :
    H.physicalWeightedCost first last hle T B r A v p O q =
      H.physicalWeightedCost first last hle T C r A v p O q := by
  unfold ObservedHistory.physicalWeightedCost
  rw [ObservedHistory.regularizedCost_eq_of_scalar_lower_bound_le hfloor first last hle T hB hC
    0 v p q]

/-- **对齐**：半时钟 `0 < w`、`w² ≤ r²/2`、`2r² < t` 时，本链的 cutoff 最小值（地板 `Bf`）等于 astra 的
`tracedPhysicalWeightedMinimum`（地板 `3/a₀`，`a₀` 来自初始数据的 Hamilton–Ivey 区域）。 -/
theorem cutoffMin_eq_traced_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (identification : InitialIdentification P g R.toHistory)
    {params : CutoffParameters} (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hinit : ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf) {r A : ℝ}
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (hb : (b : ℝ) = (t : ℝ) - r ^ 2)
    (x : (R.toHistory.stageAt t).Carrier) {w : ℝ} (hT : 2 * r ^ 2 < (t : ℝ))
    (hw : w ∈ Ioc 0 (r / Real.sqrt 2)) :
    cutoffMin_C11Q R Bf r A hbt seedTrace x w =
      R.toHistory.tracedPhysicalWeightedMinimum b t hbt p x seedTrace (3 / a₀) r A w := by
  obtain ⟨hw2, hval, -, -, hslice⟩ := halfClock_slice_facts_C11Q2 R hT hb hw
  have hstart := hinit R.toHistory identification
  have hfloor := scalarFloor_min_C11Q2 R ha₀ hBf records hstart.1 hstart.2
  have htime : (b : ℝ) ≤ (t : ℝ) - w ^ 2 := by rw [hb]; nlinarith
  have hfun : cutoffValue_C11Q R Bf r A hbt seedTrace x w =
      R.toHistory.physicalWeightedCost (R.toHistory.activeStage (clockSlice_C11Q R t w))
        (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hslice.2) t Bf r A w x
        (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t w))
          (R.toHistory.activeStage_mono hslice.1) (R.toHistory.activeStage_mono hslice.2)) := by
    funext q
    unfold cutoffValue_C11Q
    rw [dite_eq_left hslice]
  unfold cutoffMin_C11Q ObservedHistory.tracedPhysicalWeightedMinimum
  rw [hfun, dite_eq_left htime]
  dsimp only
  have hfloorEq : R.toHistory.physicalWeightedCost (R.toHistory.activeStage (clockSlice_C11Q R t w))
        (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hslice.2) t Bf r A w x
        (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t w))
          (R.toHistory.activeStage_mono hslice.1) (R.toHistory.activeStage_mono hslice.2)) =
      R.toHistory.physicalWeightedCost (R.toHistory.activeStage (clockSlice_C11Q R t w))
        (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hslice.2) t (3 / a₀) r A w x
        (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t w))
          (R.toHistory.activeStage_mono hslice.1) (R.toHistory.activeStage_mono hslice.2)) := by
    funext q
    exact physicalWeightedCost_eq_of_floor_C11Q2 hfloor _ _ _ _ (min_le_left _ _)
      (min_le_right _ _) r A w x _ q
  rw [hfloorEq]
  exact sInf_physicalWeightedCost_congr_slice_C11Q2 R.toHistory hbt seedTrace x (3 / a₀) r A w
    (Subtype.ext hval) hslice.1 hslice.2 htime (sub_le_self (t : ℝ) (sq_nonneg w))

/-- **astra 原形 ⇒ 本形**（逐种子）：astra 的 `hbound`（`tracedPhysicalWeightedMinimum`，地板 `3/a₀`）
在任一真实地板 `Bf` 下给本链 `M(w)` 的同一上界。实际定理落地后经此喂 `WeightedMinBound_C11Q2`。 -/
theorem weightedMinBound_of_traced_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (identification : InitialIdentification P g R.toHistory)
    {params : CutoffParameters} (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hinit : ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf) {r A Cw : ℝ}
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (hb : (b : ℝ) = (t : ℝ) - r ^ 2)
    (x : (R.toHistory.stageAt t).Carrier) (hT : 2 * r ^ 2 < (t : ℝ))
    (hbound : ∀ w ∈ Ioc (0 : ℝ) (r / Real.sqrt 2),
      R.toHistory.tracedPhysicalWeightedMinimum b t hbt p x seedTrace (3 / a₀) r A w ≤
        ((2 * r * w * Real.exp (Cw * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) : WithTop ℝ)) :
    ∀ w ∈ Ioc 0 (r / Real.sqrt 2),
      cutoffMin_C11Q R Bf r A hbt seedTrace x w ≤
        ((2 * r * w * Real.exp (Cw * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) : WithTop ℝ) := by
  intro w hw
  rw [cutoffMin_eq_traced_C11Q2 R identification records ha₀ hinit hBf hbt seedTrace hb x hT hw]
  exact hbound w hw

/-! ## 3. K4 ⇐ WeightedMinBound + K3（跳过 K2） -/

/-- WeightedMinBound 下 K3 需要的屏障高度 `Λ_A = e^{C(A)/2 + 32/√2} + 1`。 -/
def weightedMinLevel_C11Q2 (C : ℝ → ℝ) (A : ℝ) : ℝ :=
  Real.exp (C A / 2 + 32 / Real.sqrt 2) + 1

theorem weightedMinLevel_pos_C11Q2 (C : ℝ → ℝ) (A : ℝ) : 0 < weightedMinLevel_C11Q2 C A := by
  unfold weightedMinLevel_C11Q2
  positivity

/-- K4 常数（WeightedMinBound 形）：`C₄(A) = (e^{C(A)/2 + 32/√2} − 1)/√2`（donor `HalfClockActionEndpoint`
的 `L ≤ (D − 1) r`，`D = e^{C/2+32/√2} + 1`，换成 reduced length `l = 𝓛/(2v₁)`）。 -/
def weightedMinLengthConst_C11Q2 (C : ℝ → ℝ) (A : ℝ) : ℝ :=
  (Real.exp (C A / 2 + 32 / Real.sqrt 2) - 1) / Real.sqrt 2

/-- **K4 ⇐ WeightedMinBound + K3**（跳过导数形 K2）。 -/
theorem boundedReducedLength_of_weightedMinBound_C11Q2 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {nr C Λ : ℝ → ℝ} (hW : WeightedMinBound_C11Q2 F δ α nr C)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf s₁ hbs₁
    hs₁t hs₁
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
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
    v₁ hv₁mem
  rw [hexp] at hM
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

/-! ## 4. 新强链（不经 K1 / K2） -/

/-- **新强链**：WeightedMinBound（积分形）+ K3（`Λ ≥ e^{C/2+32/√2} + 1`）+ K5a ⇒
`LocalKappaWideSupply_C11Q`（K0 / K4 / K5 / K6 已证；**不要 K1、K2**）。 -/
theorem localKappa_of_weightedMinBound_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C Λ C₅ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C) (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A)
    (hK5a : SeedPatchLowAction_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) C₅) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappaWide_of_seedReducedVolume_C11Q
    (seedReducedVolumeLower_of_patch_C11Q seedPatchTransport_C11Q
      (boundedReducedLength_of_weightedMinBound_C11Q2 hW hK3 hΛ) hK5a)

/-- **新强链 + G1 窗口 K3**（`Λ := weightedMinLevel_C11Q2 C`，取等号）：剩余前提 = WeightedMinBound、K5a、
K3 的显式数据与尺度前提 `KappaWindowScale_C11Q2`（在该 `Λ` 处）。 -/
theorem localKappa_of_weightedMinBound_window_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C C₅ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C)
    (hK5a : SeedPatchLowAction_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) C₅)
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hcanon : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s) (hnr : ∀ t, 0 < t → 0 < nr t)
    (qcan ρbar : ℝ → ℝ) (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
    (hneck : ∀ t s, 0 < t → t / 2 ≤ s → s ≤ t → params.neckRadius s ≤ ρbar t)
    (Ctime : ℝ≥0)
    (hderiv : ∀ n, ∀ (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (j : Fin ((F.tower.history n).toHistory.eventCount + 1))
      (y : ((F.tower.history n).toHistory.stage j).Carrier),
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j →
      ∀ s ∈ Ioo ((F.tower.history n).toHistory.time j)
        ((F.tower.history n).toHistory.stageEndTime j), s < t.val →
        qcan t < metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt ((F.tower.history n).toHistory.stageMetric j z) y)
              (Iic s) s| ≤
            Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hscale : KappaWindowScale_C11Q2 P g params α nr (weightedMinLevel_C11Q2 C) qcan ρbar
      Ctime) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappa_of_weightedMinBound_C11Q2 hW
    (surgeryActionBarrier_of_window_C11Q2 params records hcanon hδ
      (fun A _ => weightedMinLevel_pos_C11Q2 C A) hnr qcan ρbar hqcan hρbar hneck Ctime hderiv
      hscale)
    (fun _ _ => le_rfl) hK5a

/-- **consumer（G2）**：新强链 ⇒ P6B `hKappaLocal`（`L = 1`，同一 `nr`），与 G1 强链同一终点。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C Λ C₅ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C) (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A)
    (hK5a : SeedPatchLowAction_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) C₅) :
    LocalKappaSupply_P6B F δ α nr :=
  (localKappa_of_weightedMinBound_C11Q2 hW hK3 hΛ hK5a).toP6B

end GC.LongTime.Ch11

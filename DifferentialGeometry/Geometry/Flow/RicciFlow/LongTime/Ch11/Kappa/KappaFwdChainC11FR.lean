import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleC11Q4b

/-!
# κ 链的前向种子尺度变体（O-CH11-FRESH G1a，后缀 `_C11FR`）

`KappaSeedScaleC11Q4b` 的种子尺度前提 `nr t / 100 ≤ r` 唯一的实质消费是 EventNodeData 的
`nodeR ≤ r`（`KappaFineNodesC11Q6` 的 `rad(blk+1)/100 ≤ r`，A 类：event 块半径 ≤ 种子尺度），
而块子句给 `rad(m+1) ≤ nr T` 对任意 `T ∈ [τ, 2τ]`；半窗 `τ ≥ t − r²/2` ⇒ `[t, 2t − r²] ⊂ [τ, 2τ]`。
故种子尺度换成**前向形** `∃ T, t ≤ T ≤ 2t − r², nr T / 100 ≤ r`（`T = t` 退回原形，严格更弱）：
* 合同 `WeightedMinBoundEndFwd_C11FR` / `BoundedReducedLengthFwd_C11FR` / `SeedReducedVolumeFwd_C11FR`
  = Q4b 三合同逐字，只换种子尺度一行；测试尺度 `nr t / 100 ≤ ϱ₀` 不变；
* K4 ⇐ 端点形 + K3、K5 ⇐ K4 + block、端点形 ⇐ records + node 数据：Q4b 证明体逐字
  （种子尺度只原样转交）；
* `seedReducedVolumeScaled_of_fwd_C11FR`：前向 K5 ⇒ Q4b 尺度 K5（`T := t`），供 P6B `hloc`。
设计：`docs/geometrization/chapter8/design-C11-fresh-20261007.md` §1–§2。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
  (eventLowSublevelContact_of_nodeData_C11Q4)

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 前向种子尺度合同 -/

/-- **端点形 WeightedMinBound（前向种子尺度）**：`WeightedMinBoundEnd_C11Q3` 逐字，种子尺度换成前向形
`∃ T ∈ [t, 2t − r²], nr T/100 ≤ r`。 -/
def WeightedMinBoundEndFwd_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (C : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    (∃ T : ℝ, (t : ℝ) ≤ T ∧ T ≤ 2 * (t : ℝ) - r ^ 2 ∧ nr T / 100 ≤ r) →
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

/-- **K4（前向种子尺度）**：`BoundedReducedLengthNearSeed_C11Q` 逐字，种子尺度换成
前向形 `∃ T ∈ [t, 2t − r²], nr T/100 ≤ r`。 -/
def BoundedReducedLengthFwd_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (C₄ : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    (∃ T : ℝ, (t : ℝ) ≤ T ∧ T ≤ 2 * (t : ℝ) - r ^ 2 ∧ nr T / 100 ≤ r) →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ (s₁ : Icc (0 : ℝ) H.horizon) (hbs₁ : b ≤ s₁) (hs₁t : s₁ ≤ t),
      (s₁ : ℝ) = (t : ℝ) - r ^ 2 / 2 →
      ∃ q ∈ riemannianBallOf (H.stageMetric (H.activeStage s₁) s₁)
          (seedTrace.point (H.activeStage s₁) (H.activeStage_mono hbs₁)
            (H.activeStage_mono hs₁t)) (r / 10),
        IsLowActionEndpoint_C11Q R Bf t s₁ x (C₄ A) q

/-- **K5（前向种子尺度）**：`SeedReducedVolumeLower_C11Q` 逐字，种子尺度换成
前向形 `∃ T ∈ [t, 2t − r²], nr T/100 ≤ r`。 -/
def SeedReducedVolumeFwd_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (v : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → 0 < v A ∧ ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    (∃ T : ℝ, (t : ℝ) ≤ T ∧ T ≤ 2 * (t : ℝ) - r ^ 2 ∧ nr T / 100 ≤ r) →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
      ENNReal.ofReal (v A) ≤ redVolTau_C11Q (F.tower.history n) t x (3 / 4 * r ^ 2)

/-! ## 2. 链：端点形 ⇒ K4 ⇒ K5；端点形的生产 -/

/-- **K4 ⇐ 端点形 + K3（前向种子尺度）**：`boundedReducedLength_of_weightedMinBoundEnd_C11Q3` 的证明逐字。 -/
theorem boundedReducedLengthFwd_of_end_C11FR {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {nr C Λ : ℝ → ℝ} (hW : WeightedMinBoundEndFwd_C11FR F δ α nr C)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A) :
    BoundedReducedLengthFwd_C11FR F δ α nr (weightedMinLengthConst_C11Q2 C) := by
  intro A hA n R H t p r hr hacc hsmall hvol hscale b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf s₁
    hbs₁ hs₁t hs₁
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
  have hM := hW A hA n t p r hr hacc hsmall hvol hscale b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
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

/-- **K5 ⇐ K4 + block（前向种子尺度）**：`seedReducedVolumeLower_of_block_C11Q2` 的证明逐字。 -/
theorem seedReducedVolumeFwd_of_block_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₄ D κ : ℝ → ℝ}
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hK4 : BoundedReducedLengthFwd_C11FR F δ α nr C₄)
    (hB : SeedRegularBlock_C11Q2 F δ α nr C₄ D κ) :
    SeedReducedVolumeFwd_C11FR F δ α nr (seedBlockVolumeConst_C11Q2 D κ) := by
  intro A hA
  refine ⟨by unfold seedBlockVolumeConst_C11Q2; have := hκ A hA; positivity, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ϱ₀ hϱ₀ hball₀
  have hr0 : 0 < r := hsmall.1
  obtain ⟨b, hbt, hb, htraces⟩ := hsmall.2
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr0
  obtain ⟨seedTrace, -⟩ := htraces p hp
  obtain ⟨Bf, -, hfl⟩ := (F.tower.history n).exists_stageMetric_scalar_lower_bound
  have hBf : ScalarFloor_C11Q (F.tower.history n) Bf := hfl
  set w : ℝ := Real.sqrt (3 / 4) * r with hwdef
  have hs34 : 0 < Real.sqrt (3 / 4) := Real.sqrt_pos.2 (by norm_num)
  have hw : 0 < w := mul_pos hs34 hr0
  have hw2 : w ^ 2 = 3 / 4 * r ^ 2 := by
    rw [hwdef, mul_pow, Real.sq_sqrt (by norm_num)]
  have ht0 : (0 : ℝ) ≤ (t : ℝ) - w ^ 2 := by rw [hw2]; nlinarith
  have hsval : (clockSlice_C11Q (F.tower.history n) t w : ℝ) = (t : ℝ) - w ^ 2 :=
    clockSlice_val_C11Q (F.tower.history n) t ht0
  have hst : clockSlice_C11Q (F.tower.history n) t w ≤ t := by
    change (clockSlice_C11Q (F.tower.history n) t w : ℝ) ≤ (t : ℝ)
    rw [hsval]
    nlinarith [sq_nonneg w]
  let s₁ : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - r ^ 2 / 2, ⟨by nlinarith, by have := t.2.2; nlinarith [sq_nonneg r]⟩⟩
  have hbs₁ : b ≤ s₁ := by
    change (b : ℝ) ≤ (t : ℝ) - r ^ 2 / 2
    rw [hb]
    nlinarith
  have hs₁t : s₁ ≤ t := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ)
    nlinarith [sq_nonneg r]
  have hq₁ := hK4 A hA n t p r hr hacc hsmall hvol hscale b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf
    hBf s₁ hbs₁ hs₁t rfl
  obtain ⟨U, hU, hvolU, hlow⟩ := hB A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀
    hϱ₀ hball₀ Bf hBf s₁ hbs₁ hs₁t rfl hq₁
  have hsq : Real.sqrt ((t : ℝ) - (clockSlice_C11Q (F.tower.history n) t w : ℝ)) = w := by
    rw [hsval, show (t : ℝ) - ((t : ℝ) - w ^ 2) = w ^ 2 by ring, Real.sqrt_sq hw.le]
  have hblock : ∀ q ∈ U,
      q ∈ H.regularMinimizerEndpoints (H.activeStage (clockSlice_C11Q (F.tower.history n) t w))
        (H.activeStage t) (H.activeStage_mono hst) t Bf w x ∧
      H.regularizedCost (H.activeStage (clockSlice_C11Q (F.tower.history n) t w))
        (H.activeStage t) (H.activeStage_mono hst) t Bf 0 w x q ≤
          ((2 * D A * w : ℝ) : WithTop ℝ) := by
    intro q hq
    obtain ⟨⟨hle', hmem⟩, hcost⟩ := hlow q hq
    unfold sliceCost_C11Q at hcost
    rw [dite_eq_left (H.activeStage_mono hst)] at hcost
    rw [hsq] at hmem hcost
    exact ⟨hmem, hcost⟩
  have hfinal := redVolume_ge_of_lowActionPatch_C11Q (F.tower.history n) hBf t x hw
    (H.activeStage_mono hst) U hU hvolU hblock
  unfold redVolTau_C11Q seedBlockVolumeConst_C11Q2
  rw [show 3 / 4 * r ^ 2 = w ^ 2 from hw2.symm, Real.sqrt_sq hw.le]
  exact hfinal

/-- **`WeightedMinBoundEndFwd_C11FR` ⇐ records + 前向尺度种子的 event node 数据**：无 event 半窗口种子由
`cutoffMin_le_of_noEventWindow_C11Q3`（DPWSP:859），有 event 种子由 G2 contact + G1 跨 event 归纳；
`A' = max A 1`（`v₁ = r/√2` 处 cutoff 与 `A` 无关）。 -/
theorem weightedMinBoundEndFwd_of_nodeData_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∃ T : ℝ, (t : ℝ) ≤ T ∧ T ≤ 2 * (t : ℝ) - r ^ 2 ∧ nr T / 100 ≤ r) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho) :
    WeightedMinBoundEndFwd_C11FR F δ α nr (fun A => cutoffBarrierConst_C11Q3 (max A 1)) := by
  intro A hA n R H t p r hr hacc hsmall hvol hscale b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hA1 : 1 ≤ max A 1 := le_max_right _ _
  have hx' : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (max A 1 * r) := by
    change riemannianEDistOf _ p x < ENNReal.ofReal (max A 1 * r)
    exact hx.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0.le))
  rw [cutoffMin_halfClock_eq_C11Q3 R hr0 A (max A 1) hbt seedTrace x]
  rcases lt_or_ge (H.time (H.activeStage t)) ((t : ℝ) - r ^ 2 / 2) with hage | hev
  · exact cutoffMin_le_of_noEventWindow_C11Q3 R (F.tower.initial n) (records n) hBf t p x hA1
      hr hsmall hbt hb seedTrace hx' hball hage (r / Real.sqrt 2) ⟨div_pos hr0 hs2, le_rfl⟩
  have hN := hnode A hA n t p r hr hacc hsmall hvol hscale x hx ϱ₀ hϱ₀ hball hev
  obtain ⟨nodeA, nodeE, nodeR, nodeQ, nodeRho, hN'⟩ := hN
  have hseedBall := isParabolicallyRmControlledBall_of_seed_C11Q hsmall
  have hcon := eventLowSublevelContact_of_nodeData_C11Q4 Cderiv H (F.tower.initial n) params
    (records n) t p x hA1 hseedBall b hbt hb seedTrace
    (seedTrace_isRmControlled_C11Q4 hsmall hbt hb seedTrace) hN'
  have hbound := tracedMin_le_of_eventContact_C11Q4 Cderiv H (F.tower.initial n) params
    (records n) t p x hA1 hr hseedBall hx' hball b hbt hb seedTrace hN' hcon
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  exact weightedMinBound_of_traced_C11Q2 R (F.tower.initial n) (records n) hspec.1 hspec.2.1
    hBf hbt seedTrace hb x hr hbound (r / Real.sqrt 2) ⟨div_pos hr0 hs2, le_rfl⟩

/-! ## 3. 前向 ⇒ 原尺度形（P6B `hloc` 用） -/

/-- **前向 K5 ⇒ Q4b 尺度 K5**：原种子尺度 `nr t/100 ≤ r` 取 `T := t`（`2r² < t` ⇒ `t ≤ 2t − r²`）。 -/
theorem seedReducedVolumeScaled_of_fwd_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeFwd_C11FR F δ α nr v) :
    SeedReducedVolumeScaled_C11Q4 F δ α nr v := by
  intro A hA
  obtain ⟨hv, h5⟩ := hK5 A hA
  refine ⟨hv, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ϱ₀ hϱ₀ hball
  exact h5 n t p r hr hacc hsmall hvol ⟨t, le_rfl, by nlinarith [sq_nonneg r], hscale⟩ x hx ϱ₀
    hϱ₀ hball

/-- **consumer**：前向链 K4 ⇒ K5 ⇒ P6B `LocalKappaSupply_P6B`（经尺度形）。 -/
theorem localKappaP6B_of_fwdChain_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₄ D κ : ℝ → ℝ}
    (hκ : ∀ A, 0 < A → 0 < κ A) (hK4 : BoundedReducedLengthFwd_C11FR F δ α nr C₄)
    (hB : SeedRegularBlock_C11Q2 F δ α nr C₄ D κ) :
    LocalKappaSupply_P6B F δ α nr :=
  localKappaP6B_of_reducedVolumeScaled_C11Q4
    (seedReducedVolumeScaled_of_fwd_C11FR (seedReducedVolumeFwd_of_block_C11FR hκ hK4 hB))

end GC.LongTime.Ch11

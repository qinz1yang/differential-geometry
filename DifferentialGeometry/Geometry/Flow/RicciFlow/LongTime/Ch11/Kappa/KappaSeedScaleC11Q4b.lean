import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaConsumerC11Q4

/-!
# κ 链的种子尺度变体（O-CH11-KAPPA3 G6，后缀 `_C11Q4`；FINEPACK G0 R-a，lead 方案 (a)）

`EventNodeData_C11Q4` 的 `nodeR ≤ r` 不能放宽：树内
`exists_old_seed_and_endpoint_outside_retained_cap_windows`（EventWindowEndpointPair:22，给 `hO`）
与 birth 定理都要 `rTerm ≤ r`（种子极点 `p` 在 `rTerm` 尺度受控）。
astra 靠种子尺度 `neckRadius t / 100 ≤ r` 保证。故把 event node 数据只对 **`nr t / 100 ≤ r` 的种子**要求
（`nodeR := nr(block)/100` 与种子无关，可由 block chooser 预先支配），并沿 κ 链加同一种子尺度前提：
* 合同 `WeightedMinBoundEndScaled_C11Q4` / `BoundedReducedLengthScaled_C11Q4` /
  `SeedReducedVolumeScaled_C11Q4` = `WeightedMinBoundEnd_C11Q3` / K4 / K5 逐字 + `nr t / 100 ≤ r`；
* K4 ⇐ 端点形 + K3、K5 ⇐ K4 + block 的证明逐字（多传 `hscale`）；
* **P6B（`L = 1`）⇐ K5（尺度形）+ K6**：`LocalKappaAt_P6B` 的测试尺度 `nr t/100 ≤ ρ' ≤ r` 本身推出
  `nr t/100 ≤ r`，故 `r < nr/100` 的种子空真。**注意**：`L > 1` 的 wide 形（SMALLVOL 的 seed shift 用
  `L = 100(A+1)`）对小种子不空真，本变体**不**给 `LocalKappaWideSupply_C11Q`；端到端 PRE841 只用 P6B 形。
* `weightedMinBoundEndScaled_of_nodeData_C11Q4`：无 event 种子同 Q3-G1，有 event 种子同 G1 + G2；
* 端到端 `nonempty_pre841Data_of_native_nodesScaled_C11Q4`：`nonempty_pre841Data_of_native_nodes_C11Q4`
  的 binder 逐字，只在 `hnode` 里加 `N.params.neckRadius t / 100 ≤ r`（严格弱前提；consumer 型对齐）。
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

/-! ## 1. 种子尺度合同 -/

/-- **端点形 WeightedMinBound（种子尺度）**：`WeightedMinBoundEnd_C11Q3` 逐字，种子另加
`nr t/100 ≤ r`。 -/
def WeightedMinBoundEndScaled_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (C : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    nr t / 100 ≤ r →
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

/-- **K4（种子尺度）**：`BoundedReducedLengthNearSeed_C11Q` 逐字，种子另加 `nr t/100 ≤ r`。 -/
def BoundedReducedLengthScaled_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (C₄ : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    nr t / 100 ≤ r →
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

/-- **K5（种子尺度）**：`SeedReducedVolumeLower_C11Q` 逐字，种子另加 `nr t/100 ≤ r`。 -/
def SeedReducedVolumeScaled_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (v : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → 0 < v A ∧ ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    nr t / 100 ≤ r →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
      ENNReal.ofReal (v A) ≤ redVolTau_C11Q (F.tower.history n) t x (3 / 4 * r ^ 2)

/-! ## 2. 链：端点形 ⇒ K4 ⇒ K5 ⇒ P6B -/

/-- **K4 ⇐ 端点形 + K3（种子尺度）**：`boundedReducedLength_of_weightedMinBoundEnd_C11Q3` 的证明逐字。 -/
theorem boundedReducedLengthScaled_of_end_C11Q4 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {nr C Λ : ℝ → ℝ} (hW : WeightedMinBoundEndScaled_C11Q4 F δ α nr C)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A) :
    BoundedReducedLengthScaled_C11Q4 F δ α nr (weightedMinLengthConst_C11Q2 C) := by
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

/-- **K5 ⇐ K4 + block（种子尺度）**：`seedReducedVolumeLower_of_block_C11Q2` 的证明逐字。 -/
theorem seedReducedVolumeScaled_of_block_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₄ D κ : ℝ → ℝ}
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hK4 : BoundedReducedLengthScaled_C11Q4 F δ α nr C₄)
    (hB : SeedRegularBlock_C11Q2 F δ α nr C₄ D κ) :
    SeedReducedVolumeScaled_C11Q4 F δ α nr (seedBlockVolumeConst_C11Q2 D κ) := by
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

/-- **P6B `hKappaLocal`（`L = 1`）⇐ K5（种子尺度）+ K6**：`localKappaWide_of_reducedVolume_C11Q` 在
`L = 1` 的证明；测试尺度 `nr t/100 ≤ ρ' ≤ r` 给出种子尺度前提。 -/
theorem localKappaP6B_of_reducedVolumeScaled_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeScaled_C11Q4 F δ α nr v)
    :
    LocalKappaSupply_P6B F δ α nr := by
  intro A hA
  obtain ⟨hvA, h5⟩ := hK5 A hA
  obtain ⟨σ, C, hσ, hC, h6⟩ := controlledBallVolumeFromReducedVolume_holds_C11Q.{u} (3 / 4)
    (by norm_num) (v A / 2) (half_pos hvA)
  refine ⟨v A / 2 / C, div_pos (half_pos hvA) hC, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ρ' hlow hup hball
  have hρ : 0 < ρ' := hball.1
  have hr0 : 0 < r := hsmall.1
  obtain ⟨hupper, hdepth⟩ := h6 (F.tower.history n) t x ρ' r hρ hup hball
  have hlowV := h5 n t p r hr hacc hsmall hvol (hlow.trans hup) x hx ρ' hlow hball
  have hτ : 0 < σ * ρ' ^ 2 := by positivity
  have hmono : redVolTau_C11Q (F.tower.history n) t x (3 / 4 * r ^ 2) ≤
      redVolTau_C11Q (F.tower.history n) t x (σ * ρ' ^ 2) := by
    unfold redVolTau_C11Q
    refine historyReducedVolumeMonotone_holds (F.tower.history n) _ x t _ _
      ((F.tower.history n).toHistory.activeStage_mem t) (Real.sqrt_pos.2 hτ)
      (Real.sqrt_le_sqrt hdepth) ?_
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hchain := (hlowV.trans hmono).trans hupper
  set V := ballVolume (H.stageMetric (H.activeStage t) t) x ρ' with hV
  have hsplit : ENNReal.ofReal (v A) =
      ENNReal.ofReal (v A / 2) + ENNReal.ofReal (v A / 2) := by
    rw [← ENNReal.ofReal_add (half_pos hvA).le (half_pos hvA).le]
    congr 1
    ring
  rw [hsplit] at hchain
  have hhalf : ENNReal.ofReal (v A / 2) ≤ ENNReal.ofReal (C / ρ' ^ 3) * V :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have hρ3 : 0 < ρ' ^ 3 := pow_pos hρ 3
  have hreal : v A / 2 / C * ρ' ^ 3 = v A / 2 * (ρ' ^ 3 / C) := by
    field_simp
  have hone : C / ρ' ^ 3 * (ρ' ^ 3 / C) = 1 := by
    field_simp
  calc
    ENNReal.ofReal (v A / 2 / C * ρ' ^ 3) =
        ENNReal.ofReal (v A / 2) * ENNReal.ofReal (ρ' ^ 3 / C) := by
      rw [hreal, ENNReal.ofReal_mul (half_pos hvA).le]
    _ ≤ ENNReal.ofReal (C / ρ' ^ 3) * V * ENNReal.ofReal (ρ' ^ 3 / C) :=
      mul_le_mul_left hhalf _
    _ = V := by
      rw [mul_comm (ENNReal.ofReal (C / ρ' ^ 3)) V, mul_assoc,
        ← ENNReal.ofReal_mul (div_pos hC hρ3).le, hone, ENNReal.ofReal_one, mul_one]

/-! ## 3. 端点形（种子尺度）的生产 -/

/-- **`WeightedMinBoundEndScaled_C11Q4` ⇐ records + 尺度种子的 event node 数据**：无 event 半窗口种子由
`cutoffMin_le_of_noEventWindow_C11Q3`（DPWSP:859），有 event 种子由 G2 contact + G1 跨 event 归纳；
`A' = max A 1`（`v₁ = r/√2` 处 cutoff 与 `A` 无关）。 -/
theorem weightedMinBoundEndScaled_of_nodeData_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        nr t / 100 ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho) :
    WeightedMinBoundEndScaled_C11Q4 F δ α nr (fun A => cutoffBarrierConst_C11Q3 (max A 1)) := by
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

/-! ## 4. 端到端（种子尺度 node 数据） -/

/-- **端到端 ⇒ `Pre841Data_C11K`（种子尺度 node 数据）**：`nonempty_pre841Data_of_native_nodes_C11Q4` 的
binder 逐字，只在 `hnode` 里加 `N.params.neckRadius t / 100 ≤ r`（event node 数据只对尺度种子要求，
`nodeR := nr(block)/100` 与种子无关）。κ 段走 P6B（`L = 1`）尺度链。 -/
theorem nonempty_pre841Data_of_native_nodesScaled_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        N.params.neckRadius t / 100 ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hure : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α
      (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  have hK3 := surgeryActionBarrier_of_native_fineCap_C11Q5 N hact hδ
    (fun A _ => weightedMinLevel_pos_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A) hfine
  have hK4 := boundedReducedLengthScaled_of_end_C11Q4
    (weightedMinBoundEndScaled_of_nodeData_C11Q4 N.params N.records Cderiv hnode) hK3
    (fun _ _ => le_rfl)
  have hK5 := seedReducedVolumeScaled_of_block_C11Q4 (fun A _ => ureBlockKappa_pos_C11Q3 A) hK4
    (seedRegularBlock_of_URE_C11Q4 N.params N.records Cderiv hure)
  have hloc : LocalKappaSupply_P6B F δ α N.params.neckRadius :=
    localKappaP6B_of_reducedVolumeScaled_C11Q4 hK5
  obtain ⟨κ₁, hκ₁, hW₁⟩ :=
    localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  have hW0 := localKappaWindow_zero_of_window_and_small_C11V hW₁ hsmallScale
  exact ⟨pre841Data_of_window_C11K (lt_min hκ₁ hκ') hW0 ind (N.comp ind) t p r hlate htime hsmall
    hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist⟩

/-- **consumer（G6，型对齐）**：`nonempty_pre841Data_of_native_nodes_C11Q4` 的 binder 逐字（无尺度前提的
`hnode`）⇒ 经尺度版得出（尺度版的 `hnode` 严格更弱）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hure : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α
      (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  refine nonempty_pre841Data_of_native_nodesScaled_C11Q4 N Cderiv ?_ hure hδ hact hfine hacc hA hκ'
    hsmallScale ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii
    hwin hdist
  intro A' hA' n R' H' t' p' r' hr' hacc' hsmall' hvol' _ x' hx' ϱ₀ hϱ₀ hball' hev'
  exact hnode A' hA' n t' p' r' hr' hacc' hsmall' hvol' x' hx' ϱ₀ hϱ₀ hball' hev'

end GC.LongTime.Ch11

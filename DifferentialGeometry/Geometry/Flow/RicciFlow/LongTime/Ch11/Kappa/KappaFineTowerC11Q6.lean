import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineNodesC11Q6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaPre841ThreeFineCapC11KD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepOfAstraC11W5
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRawCapsPortC11P

/-!
# R1 接线：策略 tower ⇒ raw caps ⇒ 块数据 ⇒ PRE841（O-CH11-FINEPACK G2b，后缀 `_C11Q6`）

把 G2 的块数据接口（`hev / hdomK3 / hdomE / hdomU / hnr1 / hrad` + native 数据 `N`）从树内生产者造出来：

1. `budgetChoice_dominating_C11Q6`：块 `j` 在 lookahead（`rNext`）之后选请求
   `req = join(k3BlockConsts j rNext, k3BlockConsts (j−1) X.radius, eventBlockRequest j rNext,
   ureBlockRequest j rNext)`，`accuracyCap ≤ min(1/(j+2), δ(b_j)/4, 各 δ)`——满足 `RequestReady_C11W`
   并支配四个 chooser（"nr 先定、再定请求"= C11W 量词序；无 tracked 改动）。
2. `exists_blockData_C11Q6`：`exists_blockSteps_of_astra_C11W5`（producer-closed）+
   `exists_inv_base_C11W` + G1 `tower_of_blockSteps_policy_C11Q6` ⇒ tower `TW`；
   `TW.toChain.exists_surgery_with_retained_raw_caps`
   （W = retention choice）⇒ `(F, q, records)` 与 block / m-i 子句 ⇒ `hev`（A-guard 经 G1
   `diagonalLargerBallAccuracy_eq_C11Q6`）、`hdom*`（策略 + `fine_{radius,order,accuracy}` +
   `accuracy_le_cap`）、
   `hnr1`（astra `hRadiusZero` 同证）；`N := nativeDataOfSupplies_C11KD`（KDATA，S11 由
   `timeDerivativeSupply_of_astra_C12X`）。
3. **`exists_pre841Data_of_retention_C11Q6`**：`∀ P g, ∃ F N`，PRE841 种子数据 + `hsmallScale` ⇒
   `Pre841Data_C11K`。κ 线不再有 `hW / hB / hact / hfine / hacc / hnode / hure` 前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory renaming
  exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests_at_closed_poles
    → closedPoleSupport_C11Q6,
  exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests
    → ureSupport_C11Q6

namespace GC.LongTime.Ch11

universe u

/-! ## 1. chooser 正性 -/

/-- event node chooser 在正输入处为正（EventLocal:567 的 request 子句）。 -/
theorem kappaEventRequest_pos_C11Q6 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (c : ℝ)
    (Cderiv : ℝ≥0) {Aact E rT qD ρ : ℝ} (hE : 0 ≤ E) (hr : 0 < rT) (hq : 0 < qD)
    (hρ : 0 < ρ) :
    0 < (kappaEventRequest_C11Q4 P₀ g₀ c Cderiv Aact E rT qD ρ).1 ∧
      0 < (kappaEventRequest_C11Q4 P₀ g₀ c Cderiv Aact E rT qD ρ).2.1 ∧
      0 < (kappaEventRequest_C11Q4 P₀ g₀ c Cderiv Aact E rT qD ρ).2.2.2 := by
  have h := (Classical.choose_spec (closedPoleSupport_C11Q6.{u} (windowBarrierA₀_C11Q2 P₀ g₀)
    (max c 1) (StandardCap.transitionEnd + 10) Cderiv (windowBarrierA₀_spec_C11Q2 P₀ g₀).1
    (lt_of_lt_of_le one_pos (le_max_right c 1)) (le_add_of_nonneg_right (by norm_num)))).1
    Aact E rT qD ρ hE hr hq hρ
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2⟩

/-- URE chooser 在正输入处为正（EventLocal:748 的 request 子句；`c > 0` 支）。 -/
theorem ureRequest_pos_C11Q6 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) {c : ℝ}
    (hc : 0 < c) (Cderiv : ℝ≥0) {Aact E rT qD ρ : ℝ} (hE : 0 ≤ E) (hr : 0 < rT)
    (hq : 0 < qD) (hρ : 0 < ρ) :
    0 < (ureRequest_C11Q3 P₀ g₀ c Cderiv Aact E rT qD ρ).1 ∧
      0 < (ureRequest_C11Q3 P₀ g₀ c Cderiv Aact E rT qD ρ).2.1 ∧
      0 < (ureRequest_C11Q3 P₀ g₀ c Cderiv Aact E rT qD ρ).2.2.2 := by
  unfold ureRequest_C11Q3
  rw [dite_eq_left hc]
  have h := (Classical.choose_spec (ureSupport_C11Q6.{u} (windowBarrierA₀_C11Q2 P₀ g₀) c
    StandardCap.transitionEnd Cderiv (windowBarrierA₀_spec_C11Q2 P₀ g₀).1 hc le_rfl)).1
    Aact E rT qD ρ hE hr hq hρ
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2⟩

/-- 块 K3 常数为正且 `R₀ > transitionEnd`。 -/
theorem k3BlockConsts_pos_C11Q6 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) {Λrec : ℝ}
    (hΛ : 0 < Λrec) (Ctime : ℝ≥0) (m : ℕ) {rad : ℝ} (hr : 0 < rad) :
    0 < (k3BlockConsts_C11Q6 P₀ g₀ Λrec Ctime m rad).1 ∧
      0 < (k3BlockConsts_C11Q6 P₀ g₀ Λrec Ctime m rad).2.1 ∧
      StandardCap.transitionEnd < (k3BlockConsts_C11Q6 P₀ g₀ Λrec Ctime m rad).2.2.1 := by
  have h := fineBarrierConsts_spec_C11Q5 P₀ g₀ (E := Real.sqrt ((3 : ℝ) ^ m))
    (A := weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))
      (12 * (3 : ℝ) ^ m) * Real.sqrt ((3 : ℝ) ^ m)) (r₀ := rad / 100) (qcan := (rad ^ 2)⁻¹)
    (Λ := Λrec) (ρ := 1) Ctime (Real.sqrt_nonneg _) (div_pos hr (by norm_num))
    (inv_pos.mpr (pow_pos hr 2)) hΛ one_pos
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## 2. 块请求策略 -/

/-- **块请求策略**：lookahead 给出 `rNext > 0` 后，join 四个 chooser 得到满足 `RequestReady_C11W` 的请求，
它支配本块 K3 / event / URE chooser（输入 `rNext`）与上一块 K3 chooser（输入 `X.radius`）。 -/
theorem budgetChoice_dominating_C11Q6 (P : OrientedThreeStage.{u}) (g : P.Metric) {Λrec : ℝ}
    (hΛ : 0 < Λrec) (Cderiv : ℝ≥0) {pBase : CutoffParameters} {C : ClosedBirthConstants}
    (j : ℕ) (X : BlockState_C11W pBase C P g j) {rNext : ℝ} (hrNext : 0 < rNext) :
    ∃ req : BlockRequest_C11W, RequestReady_C11W X req ∧
      ((k3BlockConsts_C11Q6 P g Λrec Cderiv j rNext).2.2.1 ≤ req.Dcut ∧
        (k3BlockConsts_C11Q6 P g Λrec Cderiv j rNext).2.2.2 ≤ req.mcut ∧
        req.epsCut ≤ (k3BlockConsts_C11Q6 P g Λrec Cderiv j rNext).2.1 ∧
        req.accuracyCap ≤
          (k3BlockConsts_C11Q6 P g Λrec Cderiv j rNext).1) ∧
      ((k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).2.2.1 ≤ req.Dcut ∧
        (k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).2.2.2 ≤ req.mcut ∧
        req.epsCut ≤ (k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).2.1 ∧
        req.accuracyCap ≤
          (k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).1) ∧
      ((eventBlockRequest_C11Q6 P g Λrec Cderiv j rNext).2.1 ≤ req.Dcut ∧
        (eventBlockRequest_C11Q6 P g Λrec Cderiv j rNext).2.2.1 ≤ req.mcut ∧
        req.epsCut ≤ (eventBlockRequest_C11Q6 P g Λrec Cderiv j rNext).1 ∧
        req.accuracyCap ≤
          (eventBlockRequest_C11Q6 P g Λrec Cderiv j rNext).2.2.2) ∧
      ((ureBlockRequest_C11Q6 P g Λrec Cderiv j rNext).2.1 ≤ req.Dcut ∧
        (ureBlockRequest_C11Q6 P g Λrec Cderiv j rNext).2.2.1 ≤ req.mcut ∧
        req.epsCut ≤ (ureBlockRequest_C11Q6 P g Λrec Cderiv j rNext).1 ∧
        req.accuracyCap ≤
          (ureBlockRequest_C11Q6 P g Λrec Cderiv j rNext).2.2.2) := by
  have hc₁ := k3BlockConsts_pos_C11Q6 P g hΛ Cderiv j hrNext
  have hc₂ := k3BlockConsts_pos_C11Q6 P g hΛ Cderiv (j - 1) X.radius_pos
  have he := kappaEventRequest_pos_C11Q6 P g Λrec Cderiv
    (Aact := (eventLevelE_C11Q4 (12 * (3 : ℝ) ^ j) + 1) * Real.sqrt ((3 : ℝ) ^ j))
    (Real.sqrt_nonneg ((3 : ℝ) ^ j)) (div_pos hrNext (by norm_num : (0 : ℝ) < 100))
    (inv_pos.mpr (pow_pos hrNext 2)) one_pos
  have hu := ureRequest_pos_C11Q6 P g hΛ Cderiv
    (Aact := ureBlockD_C11Q3 (12 * (3 : ℝ) ^ j) * Real.sqrt ((3 : ℝ) ^ j))
    (Real.sqrt_nonneg ((3 : ℝ) ^ j)) (div_pos hrNext (by norm_num : (0 : ℝ) < 100))
    (inv_pos.mpr (pow_pos hrNext 2)) one_pos
  have hδ : 0 < X.parameters.delta (preparedSpatialHorizon j) :=
    X.parameters.delta_pos _ (blockActivation_mem_C11W j).1
  have hj2 : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
  set c₁ := k3BlockConsts_C11Q6 P g Λrec Cderiv j rNext with hc₁def
  set c₂ := k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius with hc₂def
  set e := eventBlockRequest_C11Q6 P g Λrec Cderiv j rNext with hedef
  set v := ureBlockRequest_C11Q6 P g Λrec Cderiv j rNext with hvdef
  refine ⟨⟨min (min c₁.2.1 c₂.2.1) (min e.1 v.1), max (max c₁.2.2.1 c₂.2.2.1) (max e.2.1 v.2.1),
    max (max c₁.2.2.2 c₂.2.2.2) (max e.2.2.1 v.2.2.1),
    min (min (1 / ((j : ℝ) + 2)) (X.parameters.delta (preparedSpatialHorizon j) / 4))
      (min (min c₁.1 c₂.1) (min e.2.2.2 v.2.2.2))⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact lt_min (lt_min hj2 (by positivity)) (lt_min (lt_min hc₁.1 hc₂.1) (lt_min he.2.2 hu.2.2))
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact lt_min (lt_min hc₁.2.1 hc₂.2.1) (lt_min he.1 hu.1)
  · exact lt_of_lt_of_le (StandardCap.transitionEnd_pos.trans hc₁.2.2)
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-! ## 3. 块数据 -/

/-- **块数据存在**：`∀ P g`，策略 tower 的 raw caps 输出给出 G2 端到端的全部块数据前提与 native 数据。 -/
theorem exists_blockData_C11Q6 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
      (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ),
      (∀ m, 0 < rad m) ∧ (∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1) ∧
      (∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z)) ∧
      (∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) ∧
      (∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) ∧
      (∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) := by
  have hsteps := exists_blockSteps_of_astra_C11W5.{u} 1 1 one_pos one_pos 1 one_pos
  obtain ⟨Cdist, -, Γ, -, hΓ⟩ := hsteps
  have hPg := hΓ P g
  obtain ⟨pBase, prepared, hbase, hdist, hres, hstep⟩ := hPg
  have hinv := exists_inv_base_C11W Cdist 1 1 1 one_pos prepared hbase hdist hres
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ := hinv
  have hΛ : 0 < pBase.recenterConstant :=
    lt_of_lt_of_le (by norm_num) pBase.recenterConstant_ge_four
  have htower := tower_of_blockSteps_policy_C11Q6
    (fun j X ℓ req =>
      ((k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.1 ≤ req.Dcut ∧
        (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.2 ≤ req.mcut ∧
        req.epsCut ≤ (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.1 ∧
        req.accuracyCap ≤
          (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).1) ∧
      ((k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).2.2.1 ≤ req.Dcut ∧
        (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).2.2.2 ≤ req.mcut ∧
        req.epsCut ≤ (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).2.1 ∧
        req.accuracyCap ≤
          (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).1) ∧
      ((eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.1 ≤ req.Dcut ∧
        (eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.1 ≤ req.mcut ∧
        req.epsCut ≤ (eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).1 ∧
        req.accuracyCap ≤
          (eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.2) ∧
      ((ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.1 ≤ req.Dcut ∧
        (ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.1 ≤ req.mcut ∧
        req.epsCut ≤ (ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).1 ∧
        req.accuracyCap ≤
          (ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.2))
    (fun j X _ ℓ hℓ => budgetChoice_dominating_C11Q6 P g hΛ Γ.Ctime j X hℓ.rNext_pos)
    hstep X₀ hX₀ hhist hrad₀
  obtain ⟨TW, -, hQ⟩ := htower
  let W : ∀ n, PreparedSpatialStepRetention (TW.toChain.state n) (TW.toChain.state (n + 1))
      (TW.toChain.accuracy n) (1 / ((n : ℝ) + 2)) (TW.request n).epsCut (TW.request n).Dcut
      (TW.request n).mcut := fun n => Classical.choice (TW.extension n).retention
  have hraw := TW.toChain.exists_surgery_with_retained_raw_caps (fun n => (TW.inv n).distance)
    (fun n => (TW.request n).epsCut) (fun n => (TW.request n).Dcut)
    (fun n => (TW.request n).mcut) W (fun n => (TW.extension n).shift_eq)
    (fun n => (TW.extension n).offset_eq) (fun n => TW.toChain_accuracy_le_quarter n)
    (windowBarrierA₀_C11Q2 P g) (windowBarrierA₀_spec_C11Q2 P g).2.1
  obtain ⟨F, q, κ, records, hbig⟩ := hraw
  obtain ⟨⟨hW1, hdiag, -, -, hmi, -⟩, hblock⟩ := hbig
  obtain ⟨hTower, -, hStatic, -, -, hδanti, hρanti, hpref, -, hcan, hwin, -, -, hδlim, hrecent⟩ :=
    hW1
  have hP2 := timeDerivativeSupply_of_astra_C12X TW.toChain (fun n => (TW.request n).epsCut)
    (fun n => (TW.request n).Dcut) (fun n => (TW.request n).mcut) W
    (fun n => (TW.extension n).shift_eq) (fun n => (TW.extension n).offset_eq) F hTower q hρanti
    (fun v hv => (hdiag v hv).2)
  let N := nativeDataOfSupplies_C11KD F q records Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ)
    Γ.Ctime hρanti hδanti hδlim (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) hwin
    hcan hP2 hrecent
  have hrc : N.params.recenterConstant = pBase.recenterConstant := hStatic.2.2.2.2
  refine ⟨F, N, fun m => (TW.block m).radius, fun m => (W m).fineParameters.modelRadius,
    fun m => (W m).fineParameters.modelAccuracy, fun m => TW.accuracy m,
    fun m => (W m).fineParameters.modelOrder, fun m => (TW.block m).radius_pos, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro s hs
    have h0 : q.neckRadius 0 ≤ 1 := by
      calc q.neckRadius 0 = (TW.toChain.observation 0).parameters.neckRadius 0 :=
            (hpref 0 0 ⟨le_rfl, by norm_num⟩).2.1
        _ = (TW.toChain.state 1).parameters.neckRadius 0 := rfl
        _ = (TW.toChain.state 0).parameters.neckRadius 0 :=
            ((TW.toChain.successor 0).parameters_past 0
              (by norm_num [preparedSpatialHorizon])).2.1
        _ = (TW.toChain.state 0).radius :=
            (TW.toChain.state 0).radius_after 0 (by norm_num [preparedSpatialHorizon])
        _ ≤ 1 := TW.toChain.initial_radius_le
    exact (hρanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs).trans h0
  · intro n j
    have hb := hblock n j
    obtain ⟨m, -, i, -, -, -, htime, hIoc, -, hδ, -, -, -, hrawc⟩ := hb
    have htime' : (F.tower.history n).toHistory.time j.succ =
        (TW.toChain.state (m + 1)).native.time i.succ + (TW.toChain.state (m + 1)).shift := htime
    have hmi' := hmi m i
    obtain ⟨-, -, -, hnrT, hAg, -⟩ := hmi'
    refine ⟨m, hIoc.1, hIoc.2, hδ.le, ?_, ?_, ?_⟩
    · intro T hT
      rw [htime'] at hT
      exact hnrT T hT
    · intro A hA hlt
      rw [htime'] at hlt
      refine hAg A hA ?_
      rw [diagonalLargerBallAccuracy_eq_C11Q6 TW.toChain q (fun t ht => (hdiag t ht).1)]
      exact hlt
    · intro b'
      have hr := hrawc b'
      obtain ⟨b, raw, -, hcanr, -, -, -, -, -, -, -, -, -, -, -, -, hsc, hcap, -⟩ := hr
      exact ⟨raw, hcanr, hsc, hcap⟩
  · intro m
    have hrN : (TW.block (m + 1)).radius = (TW.lookahead m).rNext := (TW.extension m).radius_eq
    have hcap0 : TW.accuracy m ≤ (TW.request m).accuracyCap := (TW.extension m).accuracy_le_cap
    have hcap1 : TW.accuracy (m + 1) ≤ (TW.request (m + 1)).accuracyCap :=
      (TW.extension (m + 1)).accuracy_le_cap
    have hQm := hQ m
    have hQm1 := hQ (m + 1)
    obtain ⟨⟨a1, a2, a3, a4⟩, -, -, -⟩ := hQm
    obtain ⟨-, ⟨b1, b2, b3, b4⟩, -, -⟩ := hQm1
    beta_reduce
    rw [hrc, hrN]
    rw [hrN] at b1 b2 b3 b4
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4, b1.trans (W (m + 1)).fine_radius, b2.trans (W (m + 1)).fine_order,
      (W (m + 1)).fine_accuracy.trans b3, hcap1.trans b4⟩
  · intro m
    have hrN : (TW.block (m + 1)).radius = (TW.lookahead m).rNext := (TW.extension m).radius_eq
    have hcap0 : TW.accuracy m ≤ (TW.request m).accuracyCap := (TW.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, ⟨a1, a2, a3, a4⟩, -⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩
  · intro m
    have hrN : (TW.block (m + 1)).radius = (TW.lookahead m).rNext := (TW.extension m).radius_eq
    have hcap0 : TW.accuracy m ≤ (TW.request m).accuracyCap := (TW.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, -, ⟨a1, a2, a3, a4⟩⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩

/-! ## 4. 端到端 -/

/-- **κ 线端到端（R1，∀ P g）**：存在塔 `F` 与 native 数据 `N`，使 PRE841 种子数据 + `hsmallScale` ⇒
`Pre841Data_C11K`。 -/
theorem exists_pre841Data_of_retention_C11Q6 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)),
      ∀ {A κ' : ℝ}, 0 < A → 0 < κ' →
      (∃ T : ℝ, 0 < T ∧
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
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (A * r n)) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU⟩ :=
    exists_blockData_C11Q6 P g
  refine ⟨F, N, ?_⟩
  intro A κ' hA hκ' hsmallScale ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s
    hst y R hR hradii hwin hdist
  exact nonempty_pre841Data_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
    hA hκ' hsmallScale ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR
    hradii hwin hdist

/-- **consumer**：块数据的 `hnr1` 给出 native 数据 `N.params.neckRadius 0 ≤ 1`（与 astra `hRadiusZero` 同值）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)),
      N.params.neckRadius 0 ≤ 1 := by
  obtain ⟨F, N, -, -, -, -, -, -, hnr1, -⟩ := exists_blockData_C11Q6 P g
  exact ⟨F, N, hnr1 0 le_rfl⟩

end GC.LongTime.Ch11

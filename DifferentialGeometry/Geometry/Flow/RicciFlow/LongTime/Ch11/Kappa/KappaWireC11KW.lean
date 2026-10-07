import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineTowerC11Q6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEndToEndC11Q4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEventContactC11Q4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV3C11GT3

set_option autoImplicit false

/-!
# hK 端到端接线（S-CH11-KWIRE G2，后缀 `_C11KW`；INTEGRATION-ONLY / PROVISIONAL）

v3 顶层 `a12EnhancedFull_of_gaps_v3_C11GT3` 的 `hK`（budget 形，结论是 **未缩放**
`LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius`）由树内产物接线：

* ADP-3 `LocalKappaWideSupply_C11Q.congr_C11KW`：`δ`、`α`、`nr` 只在非负轴上被读，非负轴上相等即可换；
  ADP-2 `LocalKappaWideSupply_C11Q.of_tower_eq_C11KW`：该供给只经 `F.tower` 依赖 `F`。
* ADP-1 `blockData_of_certifiedTower_C11KW`：`exists_blockData_C11Q6`（FINEPACK）证明体在 `htower` 之后的部分，
  `hQ := hcert`（`BudgetCertificate_C11GT2` 的四块就是 `hQ m` 的四个 conjunct），对 **任意带预算证书的
  `BlockTower_C11W`** 给出 raw caps 的 `F'`（`F'.tower = T.toChain.tower`）、native 数据 `N`、块数据。
* `localKappaWide_of_blocks_C11KW`：块数据 ⇒ K3（`surgeryActionBarrier_of_blocks_C11Q6`）+ 缩放 event node +
  URE node（`nodes_of_retention_C11Q6`），再加 **OPEN-1** 的小种子 event node 数据 ⇒ 未缩放 `hnode` ⇒
  `localKappa_of_weightedMinBoundEnd_block_C11Q4` ⇒ `LocalKappaWideSupply_C11Q`。
* `hK_of_producers_C11KW`：v3 `hK` 槽逐字；唯一剩余 binder = `hsmallNode`（OPEN-1，逐字）。

**OPEN-1**（`r < N.params.neckRadius t / 100` 的种子的 `EventNodeData_C11Q4`）不是 selection 定理能给的：
`EventNodeData` 要 `0 < nodeR i ≤ r`，而块 cap 只支配 `nodeR = rad (m+1)/100` 一处，chooser 无单调性
（FINEPACK R-a）。lead 13:4x 裁定 (b)：hK 换 seedScale 形（G3）。
-/

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. ADP-3 / ADP-2：congruence 与 tower transport -/

/-- **ADP-3**：`LocalKappaWideSupply_C11Q` 只在非负轴上读 `δ`（`s ∈ [t/2, t]`）、`α`（同点）、`nr`（`t ≥ 0`），
非负轴上逐点相等即可整体换。 -/
theorem LocalKappaWideSupply_C11Q.congr_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ δ' : ℝ → ℝ} {α α' : ℝ → ℝ → ℝ} {nr nr' : ℝ → ℝ}
    (hδ : ∀ s, 0 ≤ s → δ s = δ' s) (hα : ∀ A s, 0 ≤ s → α A s = α' A s)
    (hnr : ∀ t, 0 ≤ t → nr t = nr' t) (h : LocalKappaWideSupply_C11Q F δ α nr) :
    LocalKappaWideSupply_C11Q F δ' α' nr' := by
  intro A L hA hL
  obtain ⟨κ, hκ, hW⟩ := h A L hA hL
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ρ' hlow hup hball
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  refine hW n t p r hr (fun s hs => ?_) hsmall hvol x hx ρ' ?_ hup hball
  · have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [hδ s hs0, hα A s hs0]
    exact hacc s hs
  · rw [hnr t ht0]
    exact hlow

/-- `RawSurgery` 的另一个字段 `event_control` 是 `Prop`，所以 tower 相等即 `F = F'`（证明无关）。 -/
theorem rawSurgery_eq_of_tower_eq_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F F' : GC.Interface.RawSurgery P g} (h : F.tower = F'.tower) : F = F' := by
  cases F
  cases F'
  cases h
  rfl

/-- **ADP-2**：`LocalKappaWideSupply_C11Q F …` 只经 `F.tower` 依赖 `F`。 -/
theorem LocalKappaWideSupply_C11Q.of_tower_eq_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F F' : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (h : F'.tower = F.tower) (hW : LocalKappaWideSupply_C11Q F' δ α nr) :
    LocalKappaWideSupply_C11Q F δ α nr := by
  obtain rfl := rawSurgery_eq_of_tower_eq_C11KW h.symm
  exact hW

/-! ## 2. ADP-1：certified tower ⇒ 块数据 -/

/-- **ADP-1（certified tower ⇒ 块数据）**：`exists_blockData_C11Q6` 的 `htower` 之后部分，tower 取给定的
带预算证书的 `T`（`hQ := hcert`）。输出的 `F` 满足 `F.tower = T.toChain.tower`，`N.params` 的 `delta`、
`neckRadius` 在非负轴上等于 `chainDiagonal_C11A T.toChain`；块数据部分逐字同 `exists_blockData_C11Q6`。 -/
theorem blockData_of_certifiedTower_C11KW {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j)) :
    ∃ (F : GC.Interface.RawSurgery P g) (_ : F.tower = T.toChain.tower)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
      (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ),
      (∀ t : ℝ, 0 ≤ t → N.params.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        N.params.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
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
  have hQ := hcert
  let W : ∀ n, PreparedSpatialStepRetention (T.toChain.state n) (T.toChain.state (n + 1))
      (T.toChain.accuracy n) (1 / ((n : ℝ) + 2)) (T.request n).epsCut (T.request n).Dcut
      (T.request n).mcut := fun n => Classical.choice (T.extension n).retention
  have hraw := T.toChain.exists_surgery_with_retained_raw_caps (fun n => (T.inv n).distance)
    (fun n => (T.request n).epsCut) (fun n => (T.request n).Dcut)
    (fun n => (T.request n).mcut) W (fun n => (T.extension n).shift_eq)
    (fun n => (T.extension n).offset_eq) (fun n => T.toChain_accuracy_le_quarter n)
    (windowBarrierA₀_C11Q2 P g) (windowBarrierA₀_spec_C11Q2 P g).2.1
  obtain ⟨F, q, κ, records, hbig⟩ := hraw
  obtain ⟨⟨hW1, hdiag, -, -, hmi, -⟩, hblock⟩ := hbig
  obtain ⟨hTower, -, hStatic, -, -, hδanti, hρanti, hpref, -, hcan, hwin, -, -, hδlim, hrecent⟩ :=
    hW1
  have hP2 := timeDerivativeSupply_of_astra_C12X T.toChain (fun n => (T.request n).epsCut)
    (fun n => (T.request n).Dcut) (fun n => (T.request n).mcut) W
    (fun n => (T.extension n).shift_eq) (fun n => (T.extension n).offset_eq) F hTower q hρanti
    (fun v hv => (hdiag v hv).2)
  let N := nativeDataOfSupplies_C11KD F q records Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ)
    Γ.Ctime hρanti hδanti hδlim (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) hwin
    hcan hP2 hrecent
  have hrc : N.params.recenterConstant = pB.recenterConstant := hStatic.2.2.2.2
  have hdiagN : ∀ t : ℝ, 0 ≤ t → N.params.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      N.params.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t := hdiag
  refine ⟨F, hTower, N, fun m => (T.block m).radius, fun m => (W m).fineParameters.modelRadius,
    fun m => (W m).fineParameters.modelAccuracy, fun m => T.accuracy m,
    fun m => (W m).fineParameters.modelOrder, hdiagN, fun m => (T.block m).radius_pos, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro s hs
    have h0 : q.neckRadius 0 ≤ 1 := by
      calc q.neckRadius 0 = (T.toChain.observation 0).parameters.neckRadius 0 :=
            (hpref 0 0 ⟨le_rfl, by norm_num⟩).2.1
        _ = (T.toChain.state 1).parameters.neckRadius 0 := rfl
        _ = (T.toChain.state 0).parameters.neckRadius 0 :=
            ((T.toChain.successor 0).parameters_past 0
              (by norm_num [preparedSpatialHorizon])).2.1
        _ = (T.toChain.state 0).radius :=
            (T.toChain.state 0).radius_after 0 (by norm_num [preparedSpatialHorizon])
        _ ≤ 1 := T.toChain.initial_radius_le
    exact (hρanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs).trans h0
  · intro n j
    have hb := hblock n j
    obtain ⟨m, -, i, -, -, -, htime, hIoc, -, hδ, -, -, -, hrawc⟩ := hb
    have htime' : (F.tower.history n).toHistory.time j.succ =
        (T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift := htime
    have hmi' := hmi m i
    obtain ⟨-, -, -, hnrT, hAg, -⟩ := hmi'
    refine ⟨m, hIoc.1, hIoc.2, hδ.le, ?_, ?_, ?_⟩
    · intro T hT
      rw [htime'] at hT
      exact hnrT T hT
    · intro A hA hlt
      rw [htime'] at hlt
      refine hAg A hA ?_
      rw [diagonalLargerBallAccuracy_eq_C11Q6 T.toChain q (fun t ht => (hdiag t ht).1)]
      exact hlt
    · intro b'
      have hr := hrawc b'
      obtain ⟨b, raw, -, hcanr, -, -, -, -, -, -, -, -, -, -, -, -, hsc, hcap, -⟩ := hr
      exact ⟨raw, hcanr, hsc, hcap⟩
  · intro m
    have hrN : (T.block (m + 1)).radius = (T.lookahead m).rNext := (T.extension m).radius_eq
    have hcap0 : T.accuracy m ≤ (T.request m).accuracyCap := (T.extension m).accuracy_le_cap
    have hcap1 : T.accuracy (m + 1) ≤ (T.request (m + 1)).accuracyCap :=
      (T.extension (m + 1)).accuracy_le_cap
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
    have hrN : (T.block (m + 1)).radius = (T.lookahead m).rNext := (T.extension m).radius_eq
    have hcap0 : T.accuracy m ≤ (T.request m).accuracyCap := (T.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, ⟨a1, a2, a3, a4⟩, -⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩
  · intro m
    have hrN : (T.block (m + 1)).radius = (T.lookahead m).rNext := (T.extension m).radius_eq
    have hcap0 : T.accuracy m ≤ (T.request m).accuracyCap := (T.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, -, ⟨a1, a2, a3, a4⟩⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩

/-! ## 3. 组装：块数据 + OPEN-1 ⇒ 未缩放 wide supply -/

/-- **块数据 + 小种子 event node（OPEN-1）⇒ `LocalKappaWideSupply_C11Q`**（未缩放）。K3、缩放 event node、
URE node 来自 `nodes_of_retention_C11Q6`；未缩放 `hnode` = 缩放形（`nr t/100 ≤ r`）与 `hnodeSmall`
（`r < nr t/100`）按种子分情形。 -/
theorem localKappaWide_of_blocks_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
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
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdomK3 : ∀ m : ℕ,
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
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hnodeSmall :
    (∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < N.params.neckRadius t / 100 →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)) :
    LocalKappaWideSupply_C11Q F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius := by
  obtain ⟨hK3, hnodeSc, hure⟩ := nodes_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3
    hdomE hdomU
  refine localKappa_of_weightedMinBoundEnd_block_C11Q4 ?_ hK3 (fun _ _ => le_rfl)
    (seedRegularBlock_of_URE_C11Q4 N.params N.records N.Ctime hure)
    (fun A _ => ureBlockKappa_pos_C11Q3 A)
  refine weightedMinBoundEnd_of_nodeData_C11Q4 N.params N.records N.Ctime ?_
  intro A hA n R H t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball hevt
  by_cases hsc : N.params.neckRadius t / 100 ≤ r
  · exact hnodeSc A hA n t p r hr hacc hsmall hvol hsc x hx ϱ₀ hϱ₀ hball hevt
  · exact hnodeSmall A hA n t p r hr hacc hsmall hvol (not_le.1 hsc) x hx ϱ₀ hϱ₀ hball hevt

/-! ## 4. `hK_of_producers_C11KW`：v3 `hK` 槽 -/

/-- **`hK` 的 producer（v3 `hK` 槽逐字）**，唯一剩余 binder `hsmallNode` = **OPEN-1**（小种子 event node 数据，
对一切块数据 `N rad Df εf cap mf`）。`εκ := 1`（本路线不消费 `pB.modelAccuracy`、`hguard`、`hrad`、`hord`）。 -/
theorem hK_of_producers_C11KW (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hsmallNode : ∀ {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ), (∀ m, 0 < rad m) →
    (∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1) →
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
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z)) →
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
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) →
    (∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) →
    (∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) →
    (∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < N.params.neckRadius t / 100 →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)) :
    ∃ εκ : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εκ Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      (∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
        q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
          diagonalAccuracy_C11S q.delta A
            ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
        A < 12 * (3 : ℝ) ^ m) →
      pB.modelAccuracy ≤ εκ Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius := by
  refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
  intro pB Γ Cdist εReserve T hcert F q hTower hq _hguard _hacc _hrad _hord
  obtain ⟨F', hF', N, rad, Df, εf, cap, mf, hdiagN, hrad, hnr1, hev, hdomK3, hdomE, hdomU⟩ :=
    blockData_of_certifiedTower_C11KW T hcert
  have hwide := localKappaWide_of_blocks_C11KW N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
    (hsmallNode N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU)
  refine LocalKappaWideSupply_C11Q.of_tower_eq_C11KW (hF'.trans hTower.symm) ?_
  refine hwide.congr_C11KW (fun s hs => ?_) (fun A s hs => ?_) (fun t ht => ?_)
  · exact (hdiagN s hs).1.trans (hq s hs).1.symm
  · have hm : 0 ≤ max 0 (A / 4) := le_max_left _ _
    change 2 * N.params.delta (max 0 (A / 4)) = 2 * q.delta (max 0 (A / 4))
    rw [(hdiagN _ hm).1.trans (hq _ hm).1.symm]
  · exact (hdiagN t ht).2.trans (hq t ht).2.symm

/-- consumer：喂 v3 顶层的 `hK` 槽（`hspine hP6b hfull` 三个 binder 逐字保留，只多 OPEN-1）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hsmallNode : ∀ {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ), (∀ m, 0 < rad m) →
    (∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1) →
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
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z)) →
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
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) →
    (∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) →
    (∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) →
    (∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < N.params.neckRadius t / 100 →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho))
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A → (∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (max Γ.C1s Γ.Cbirth)
          (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (max Γ.C1s Γ.Cbirth)
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))))
    (hfull : ∃ εfull : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εfull Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εfull Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
        ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
        ∃ W : SpatialCanonicalWitness s.metric Γ.epsilon (max Γ.C1s Γ.Cbirth)
            (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart Γ.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ)
              (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
              (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
                G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
              s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G Γ.epsilon x
                s.time) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v3_C11GT3 P g (hK_of_producers_C11KW P g hsmallNode) hspine hP6b hfull

end GC.LongTime.Ch11

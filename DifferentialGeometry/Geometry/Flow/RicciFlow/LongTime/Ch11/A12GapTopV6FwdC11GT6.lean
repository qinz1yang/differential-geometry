import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6C11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2EFwdC11FR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P5LNominalSupplyP6NI

set_option autoImplicit false

/-!
# A12′ 顶层 v6（R-C11-9 修正形）：`hspine′` 的种子 guard = `nr(t) ≤ r`，forward wide 由同一 certified tower 的
块数据生产（O-CH11-GAPTOP6 G2′，后缀 `_C11GT6`）

R-C11-9 处置（`out/dispositions-R-C11-9-kappa-fresh-v5.md`）D-6 / D-10：**撤回 v5 文件头**（`A12GapTopV5C11KW`）
"坏点序列 `r/nr → ∞` 只用种子限制 window"的说明——v5 `hspine` 的 `hw` guard 是旧
`∀ w ∈ [t − r²/2, t], nr w ≤ r`，ratio ⇏ 旧 guard（审稿数值反例 `a_k = 5/6·3^k`、`c_k = 2^{−2^k}`、
`r_k = √(c_{k−1} c_k)`）。lead 裁定 (B)：v6 的 `hspine′.hw` guard 改为 **`q.neckRadius t ≤ r`**（由 ceiling +
`hradii` 免费），forward wide 从**同一 certified tower 的块数据**重新生产（不把 `hKseed` 结果重解释为
forward wide）。本文件（G1 `A12GapTopV6C11GT6` 不改）：

* `LocalKappaWideFwdSupply_C11FR.congr_C11GT6`：前向 wide 只在非负轴读 `δ α nr`；
* **`localKappaWideFwd_of_certifiedTower_C11GT6`**（same-tower，D-4）：budget tower `T` 的块数据
  （KWIRE ADP-1 `blockData_of_certifiedTower_C11KW`）⇒ FRESH 前向 K5
  （`seedReducedVolumeFwd_of_retention_C11FR`）⇒ 前向 wide，
  搬到**任一**实现 `T` 的 `F q`（`rawSurgery_eq_of_tower_eq_C11KW` + diagonal 识别）；
* **`pre841Data_of_certifiedTower_fwd_C11GT6`**（same-tower 集成，D-4）：对实际 tower 取块数据，再调 generic
  `nonempty_pre841Data_of_retention_fwd_C11FR`——结论 = `exists_pre841Data_of_retention_fwd_C11FR`
  第三合取逐字，
  但 `F` 是给定的（不是另一个 `∃ F`）；
* `s8_of_smallVolFwd_C11GT6`：S8 wire 的前向版（P6B window 仍由尺度 wide 给，`hsmall` 由**前向** wide +
  `hsmallSeedFwd_of_wideFwdSupply_C11FR`，glue `localKappaWindow_zero_of_window_and_smallFwd_C11FR`，
  前向 guard `nr(4w/3) ≤ r` 由 `nr t ≤ r` + antitone 推出）；GAP-2 常数 = `epsilon0_C11FR`（D-3：与
  `epsilon0_C11V5` 无比较，故 reserve 取含它的正最小值后再选 `pBase` 与 tower）；
* **`SameConstructionRetentionSupplyPlus_C11GT6`**（SCRS⁺，合同 Prop 的 G2′ 修订）= G1 SCRS 六组 + 前向 wide +
  band 阈值 `qcanSup_P6WR`（P6WR A6）+ NOMID reparam late records；
  `sameConstructionRetentionSupplyPlus_of_tower_C11GT6`（G2 producer：W0 证书 + ModelSmallness ⇒ SCRS⁺，
  全部 producer-closed）；`scrs_of_plus_C11GT6`；
* **`a12EnhancedFull_of_gaps_v6fwd_C11GT6`**（lead 14:4x：G2′ 交付后即**冻结的顶层合同**）：binder
  `hspine″ hP6b′`；`hP6b′` = G1 schema，前提 SCRS → SCRS⁺；方向记录 `hspineNrt_of_hspineOld_C11GT6`
  （旧 guard `hspine′` ⇒ `hspine″`：适用性义务消失）、`hP6bPlus_of_hP6b_C11GT6`（G1 `hP6b′` ⇒ 冻结形）。
-/

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 前向 wide：congruence 与 same-tower producer -/

/-- 前向 wide 只在非负轴上读 `δ`（`s ∈ [t/2, t]`）、`α`、`nr`（`t` 与前向时刻 `T ≥ t ≥ 0`）。 -/
theorem LocalKappaWideFwdSupply_C11FR.congr_C11GT6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ δ' : ℝ → ℝ} {α α' : ℝ → ℝ → ℝ} {nr nr' : ℝ → ℝ}
    (h : LocalKappaWideFwdSupply_C11FR F δ α nr)
    (hδ : ∀ s, 0 ≤ s → δ s = δ' s) (hα : ∀ A s, 0 ≤ s → α A s = α' A s)
    (hnr : ∀ t, 0 ≤ t → nr t = nr' t) :
    LocalKappaWideFwdSupply_C11FR F δ' α' nr' := by
  intro A L hA hL
  obtain ⟨κ, hκ, hW⟩ := h A L hA hL
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ρ' hlow hup hball
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  obtain ⟨T, hT1, hT2, hT3⟩ := hscale
  refine hW n t p r hr (fun s hs => ?_) hsmall hvol ⟨T, hT1, hT2, ?_⟩ x hx ρ' ?_ hup hball
  · have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [hδ s hs0, hα A s hs0]
    exact hacc s hs
  · rw [hnr T (ht0.trans hT1)]
    exact hT3
  · rw [hnr t ht0]
    exact hlow

/-- **same-tower forward wide**（R-C11-9 D-4 / D-6(B)）：budget tower `T` 的块数据 ⇒ 前向 wide，在任一实现 `T`
的 `F q` 上（`F.tower = T.toChain.tower`、`q` = chain diagonal）。 -/
theorem localKappaWideFwd_of_certifiedTower_C11GT6 {pB : CutoffParameters}
    {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    {εReserve : ℝ} (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) :
    LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius := by
  obtain ⟨F', hF', N, rad, Df, εf, cap, mf, hdiagN, hrad, hnr1, hev, hdomK3, hdomE, hdomU⟩ :=
    blockData_of_certifiedTower_C11KW T hcert
  obtain rfl : F' = F := rawSurgery_eq_of_tower_eq_C11KW (hF'.trans hF.symm)
  obtain ⟨v, hK5⟩ :=
    seedReducedVolumeFwd_of_retention_C11FR N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  refine (localKappaWideFwd_of_reducedVolumeFwd_C11FR hK5).congr_C11GT6 (fun s hs => ?_)
    (fun A s _ => ?_) (fun t ht => ?_)
  · exact (hdiagN s hs).1.trans (hq s hs).1.symm
  · have hm : 0 ≤ max 0 (A / 4) := le_max_left _ _
    change 2 * N.params.delta (max 0 (A / 4)) = 2 * q.delta (max 0 (A / 4))
    rw [(hdiagN _ hm).1.trans (hq _ hm).1.symm]
  · exact (hdiagN t ht).2.trans (hq t ht).2.symm

/-! ## 2. SCRS⁺（R-C11-8 D-4 字段 + R-C11-9：前向 wide、band 阈值、NOMID reparam） -/

/-- **`SameConstructionRetentionSupplyPlus_C11GT6 T`**（lead 登记合同 Prop 的 G2′ 修订；v6 冻结形的
`hP6b′` 前提）：G1 `SameConstructionRetentionSupply_C11GT6` 的六组字段（同一 `F₀ q₀ κ records`）再加
(7) **前向 wide**（R-C11-9 D-6(B)，同一 certified tower 的块数据）；(8) **band 导数阈值**
`EventSlabsDerivative Γ.Ctime (qcanSup_P6WR T.toChain horizon_n) last`（P6WR A6）；
(9) **NOMID reparam**：late linked records 是**同一** `records` 的 reparameterization
（`lateLinkedRecordsSupplyNom_of_outer_P6NI`
结论，R-C11-8 D-8）。全部为 astra 构造独立产出；不含 CanonicalLateCore / S15 / hspine / S8 / S16。 -/
def SameConstructionRetentionSupplyPlus_C11GT6 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve) : Prop :=
  ∃ (F₀ : GC.Interface.RawSurgery P g) (q₀ : CutoffParameters) (κ : ℝ → ℝ)
    (records : CutoffRecords_C11S F₀ q₀),
    (F₀.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q₀.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q₀.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      (q₀.fixed = pB.fixed ∧ q₀.modelRadius = pB.modelRadius ∧
        q₀.modelOrder = pB.modelOrder ∧ q₀.modelAccuracy = pB.modelAccuracy ∧
        q₀.recenterConstant = pB.recenterConstant)) ∧
    ((∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F₀.tower.history n).NoncollapsedBefore (κ t) Γ.epsilon t) ∧
    LocalKappaWideScaledSupply_C11Q4b F₀ q₀.delta (diagonalAccuracy_C11S q₀.delta)
      q₀.neckRadius ∧
    (AntitoneOn q₀.delta (Ici 0) ∧ AntitoneOn q₀.neckRadius (Ici 0) ∧
      Tendsto q₀.delta atTop (𝓝 0)) ∧
    ((∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧ RecentCutoffSupply_C11S records ∧
      LinkedWindowsSupply_C11E records ∧ LateLinkedRecordsSupply_C11E F₀ q₀) ∧
    HistoryCanonicalSupply_C11S F₀ q₀.neckRadius Γ.epsilon (max Γ.C1s Γ.Cbirth)
      (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) ∧
    TimeDerivativeSupply_C11E F₀ q₀.neckRadius Γ.Ctime ∧
    LocalKappaWideFwdSupply_C11FR F₀ q₀.delta (diagonalAccuracy_C11S q₀.delta) q₀.neckRadius ∧
    (∀ n, (F₀.tower.history n).EventSlabsDerivative Γ.Ctime
      (qcanSup_P6WR T.toChain (F₀.tower.history n).horizon)
      (Fin.last (F₀.tower.history n).eventCount)) ∧
    ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      p.delta = q₀.delta ∧ p.neckRadius = q₀.neckRadius ∧
      p.fixed = q₀.fixed ∧ p.recenterConstant = q₀.recenterConstant ∧
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F₀.tower.history n).eventCount,
          T₀ ≤ (F₀.tower.history n).time i.succ →
          GeometricCutoffRecord (F₀.tower.history n).toHistory i p,
        (∀ i hi b, linkedCanonicalWindow_C11E ((records' i hi).static b)) ∧
        ∀ i hi, (records' i hi).nominalRadius = (records n i).nominalRadius ∧
          (records' i hi).delta = (records n i).delta ∧
          (records' i hi).order = (records n i).order ∧
          (∀ α, HEq ((records' i hi).neck α) ((records n i).neck α)) ∧
          (∀ b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale) ∧
          ∀ (b) (z : ThreeBall),
            ((records' i hi).static b).inclusion (((records' i hi).static b).witness.cap z) =
              ((records n i).static b).inclusion (((records n i).static b).witness.cap z)

/-- SCRS⁺ ⇒ G1 的 SCRS（丢掉 (7)(8)(9)）。 -/
theorem scrs_of_plus_C11GT6 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (h : SameConstructionRetentionSupplyPlus_C11GT6 T) :
    SameConstructionRetentionSupply_C11GT6 T := by
  obtain ⟨F₀, q₀, κ, records, h1, h2, h3, h4, h5, h6, h7, -, -, -⟩ := h
  exact ⟨F₀, q₀, κ, records, h1, h2, h3, h4, h5, h6, h7⟩

/-- **SCRS⁺ producer**（G2：同一 budget tower 上全部 producer-closed）：W0 证书（预算 ∧ 共尾）+ ModelSmallness
⇒ `SameConstructionRetentionSupplyPlus_C11GT6 T`。来源：astra
`exists_surgery_with_retained_raw_caps`（retention 取
`T.extension`）、KWIRE `hKseed_of_producers_C11KW`、同 tower 前向 wide（ADP-1 + FRESH）、S11、S10 wire、S14、
P6WR A6 `eventSlabsDerivative_qcanSup_P6WR`、NOMID `lateLinkedRecordsSupplyNom_of_outer_P6NI`。 -/
theorem sameConstructionRetentionSupplyPlus_of_tower_C11GT6 (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    ∃ εS : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εS Γ) ∧
    ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
      (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j) ∧ RequestCofinal_C11W4 j (T.request j)) →
      pB.modelAccuracy ≤ εS Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      SameConstructionRetentionSupplyPlus_C11GT6 T := by
  obtain ⟨εκ, hεκ, hKp⟩ := hKseed_of_producers_C11KW P g
  refine ⟨εκ, hεκ, ?_⟩
  intro pB Γ Cdist εReserve T hQ haccκ hradB hordB
  obtain ⟨a₀, hctrl⟩ := exists_initialControl_C11GT P g
  have hS : ∀ n, (T.toChain.state n).DistanceData Cdist := fun n => (T.inv n).distance
  obtain ⟨W⟩ : Nonempty (∀ m, PreparedSpatialStepRetention (T.toChain.state m)
      (T.toChain.state (m + 1)) (T.toChain.accuracy m) (1 / ((m : ℝ) + 2))
      (T.request m).epsCut (T.request m).Dcut (T.request m).mcut) :=
    ⟨fun m => Classical.choice (T.extension m).retention⟩
  have hshift : ∀ m, (T.toChain.state (m + 1)).shift =
      (T.toChain.state m).history.time (Fin.last (T.toChain.state m).history.eventCount) :=
    fun m => (T.extension m).shift_eq
  have hoffset : ∀ m, (T.toChain.state (m + 1)).offset = (T.toChain.state m).history.eventCount :=
    fun m => (T.extension m).offset_eq
  obtain ⟨F, q, κ, records, hOld, hRaw⟩ := T.toChain.exists_surgery_with_retained_raw_caps hS
    (fun m => (T.request m).epsCut) (fun m => (T.request m).Dcut) (fun m => (T.request m).mcut)
    W hshift hoffset (fun n => T.toChain_accuracy_le_quarter n) a₀ hctrl
  obtain ⟨⟨hTower, -, ⟨hfixed, hradq, hordq, haccq, hrc⟩, hκ, hκanti, hδanti, hρanti, hpref,
    hrecHEq, hcan, hwin, hnc, -, hδlim, hrecent⟩, hdiag, -, -, hmi, -⟩ := hOld
  have hlinkS : LinkedWindowsSupply_C11E records :=
    (hlinkfine_of_chain_C11GT3 T.toChain).hlinkS10 F q records hTower
      ⟨hfixed, hradq, hordq, haccq, hrc⟩ (fun n i j hij => hrecHEq n i j hij)
  have hguard : ∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
      q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
        diagonalAccuracy_C11S q.delta A
          ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
      A < 12 * (3 : ℝ) ^ m := by
    intro m i A hA hlt
    obtain ⟨-, -, -, -, hAg, -⟩ := hmi m i
    exact lt_of_accuracyGuard_C11Q6 T.toChain q (fun t ht => (hdiag t ht).1) hA hAg hlt
  have hwide : LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta)
      q.neckRadius :=
    hKp Cdist _ T (fun j => (hQ j).1) F q hTower hdiag hguard haccκ hradB hordB
  have hwideF : LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta)
      q.neckRadius :=
    localKappaWideFwd_of_certifiedTower_C11GT6 T (fun j => (hQ j).1) F q hTower hdiag
  have hTD := timeDerivativeSupply_of_astra_C12X T.toChain _ _ _ W hshift hoffset F hTower q
    hρanti (diagonal_neckRadius_of_prefix_C12X T.toChain q (fun n t ht => (hpref n t ht).2.1))
  have hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder := by
    intro D ζ m hζ
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
      (tower_fine_request_eventually_C11W4 T (fun j => (hQ j).2) hζ D m)
    refine ⟨k₀, fun k hk => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hk₀ k hk (W k)
    exact ⟨h2, h1, h3⟩
  have hlate := lateLinkedRecordsSupply_of_outer_C12X T.toChain W F q records hfixed hrc hmi hRaw
    hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hnom := lateLinkedRecordsSupplyNom_of_outer_P6NI T.toChain W F q records hfixed hrc hmi
    hRaw hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hSCRS : SameConstructionRetentionSupplyPlus_C11GT6 T :=
    ⟨F, q, κ, records, ⟨hTower, hdiag, hfixed, hradq, hordq, haccq, hrc⟩, ⟨hκ, hκanti, hnc⟩,
      hwide, ⟨hδanti, hρanti, hδlim⟩, ⟨hwin, hrecent, hlinkS, hlate⟩, hcan, hTD, hwideF,
      fun n => eventSlabsDerivative_qcanSup_P6WR T.toChain _ _ _ W hshift hoffset F hTower n,
      hnom⟩
  exact hSCRS

/-- **same-tower Pre841 集成**（R-C11-9 D-4）：对实际 budget tower `T` 取块数据（ADP-1）再调 generic
`nonempty_pre841Data_of_retention_fwd_C11FR`；结论 = `exists_pre841Data_of_retention_fwd_C11FR` 的第三合取
逐字，但 `F` 是**给定的**实现 `T` 的 surgery（不是另一个 `∃ F`），`N.params` 是 chain diagonal。 -/
theorem pre841Data_of_certifiedTower_fwd_C11GT6 {pB : CutoffParameters}
    {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    {εReserve : ℝ} (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower) :
    ∃ N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory),
      (∀ t : ℝ, 0 ≤ t → N.params.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        N.params.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P →
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
      (∀ᶠ n in atTop, N.params.neckRadius (t n) ≤ r n) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F', hF', N, rad, Df, εf, cap, mf, hdiagN, hrad, hnr1, hev, hdomK3, hdomE, hdomU⟩ :=
    blockData_of_certifiedTower_C11KW T hcert
  obtain rfl : F' = F := rawSurgery_eq_of_tower_eq_C11KW (hF'.trans hF.symm)
  refine ⟨N, hdiagN, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hratio
  exact nonempty_pre841Data_of_retention_fwd_C11FR N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE
    hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hratio

/-! ## 2. S8 wire（前向版，`nr(t) ≤ r` guard） -/

/-- **S8 wire 前向版**：尺度 wide（P6B window）+ **前向** wide（`hsmall`，GAP-2 常数 `epsilon0_C11FR`）+ glue ⇒
`nr(t) ≤ r` guard 的 window（前向 guard `nr(4w/3) ≤ r` 由 `nr t ≤ r`、`2r² < t` 与 antitone 推出）⇒ `hspine`
⇒ S8。 -/
theorem s8_of_smallVolFwd_C11GT6 (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {pBase q : CutoffParameters},
      CollarWindowSupply_C11E.{u} pBase → ModelConstraintsSupply_C11E pBase εProf_C11E.{u} →
      q.fixed = pBase.fixed → q.modelRadius = pBase.modelRadius →
      q.modelOrder = pBase.modelOrder → q.modelAccuracy = pBase.modelAccuracy →
      pBase.modelAccuracy ≤ epsilon0_C11FR ε C1 C2 P →
      ∀ records : CutoffRecords_C11S F q, LinkedWindowsSupply_C11E records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      (∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) →
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) := by
  intro g F pBase q hP3 hprof hfixed hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon hwideS
    hwideF hspine A hA
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hP3q : CollarWindowSupply_C11E.{u} q := by
    refine ⟨?_, ?_⟩
    · exact collarAdmitsAllOrders_congr_C11KW _ _ _ _ (by rw [hfixed]) hP3.1
    · rw [hrad]
      exact hP3.2
  have hprofq : ModelConstraintsSupply_C11E q εProf_C11E.{u} := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hacc]
      exact hprof.1
    · rw [hord]
      exact hprof.2.1
    · rw [hrad]
      exact hprof.2.2
  have hq : q.modelAccuracy ≤ epsilon0_C11FR ε C1 C2 P := by
    rw [hacc]
    exact hacc₀
  have hS7 := largerBallAccuracySupply_diagonal_C11S q hδanti
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B hS7 (localKappaP6B_of_wideScaled_C11KW hwideS)) A hA0
  obtain ⟨κ', hκ', hsmall⟩ := (hsmallSeedFwd_of_wideFwdSupply_C11FR.{u} ε C1 C2 P).choose_spec.2
    hA0 hP3q hprofq hq records (hwin_of_linkedWindows_C11V3 hlink) hδanti hρanti hcanon hwideF
  obtain ⟨T, hT, hK⟩ := localKappaWindow_zero_of_window_and_smallFwd_C11FR hW₁ hsmall
  refine hspine A hA ⟨min κ₁ κ', lt_min hκ₁ hκ', T, hT, ?_⟩
  intro n H t p r hTt hr hcurv hvol hnt aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ0 hρr
    hball
  refine hK n t p r hTt hr hcurv hvol (fun w hw1 _ => ?_) aSeed haT hclock seedTrace v hav hvt hv
    x hx ρ' hρ0 hρr hball
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have hle : (t : ℝ) ≤ 4 * w / 3 := by linarith
  exact (hρanti (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr (ht0.trans hle)) hle).trans hnt

/-! ## 3. v6（R-C11-9 修正形）顶层 -/

/-- **A12′ v6（R-C11-9 修正形）引擎，ceiling 泛型**：binder `hspine″ hP6b′`；`hspine″` 的 `hw` guard =
`q.neckRadius t ≤ r`，`hP6b′` 的前提为 SCRS⁺；`hKseed`、`hfull`、SCRS、**同一 tower 的前向 wide** 在证明体内供给。 -/
theorem a12EnhancedFull_of_gaps_v6fwd_gen_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
          (C2P6_C11GT6.{u} X2 Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨Cdist, Γ, hmake⟩ := hpbase_of_provider_C11GT3 P g
  obtain ⟨εκ, hεκ, hKp⟩ := hKseed_of_producers_C11KW P g
  obtain ⟨εsp, hεsp, hspinep⟩ := hspine
  obtain ⟨εP6, hεP6, hP6p⟩ := hP6b
  obtain ⟨εfull, hεfull, hfullp⟩ := hfull_ceiling_C11SC P g
  have hε₀ := epsilon0_pos_C11FR.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
    (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) P
  have hεR : 0 < min εProf_C11E.{u} (min (εK_threshold_C11GT2 εκ εsp εP6 εfull Γ)
      (epsilon0_C11FR.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) P)) :=
    lt_min εProf_pos_C11E (lt_min (εK_threshold_pos_C11GT2 hεκ hεsp hεP6 hεfull Γ) hε₀)
  obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR
  obtain ⟨hacc, hradB, hordB⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  have haccProf : pB.modelAccuracy ≤ εProf_C11E.{u} := hacc.trans (min_le_left _ _)
  have haccT : pB.modelAccuracy ≤ εK_threshold_C11GT2 εκ εsp εP6 εfull Γ :=
    hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨haccκ, haccsp, haccP6, haccfull⟩ := εK_threshold_le_C11GT2 εκ εsp εP6 εfull Γ haccT
  have hacc₀ : pB.modelAccuracy ≤ epsilon0_C11FR.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
      (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) P :=
    hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP3 : CollarWindowSupply_C11E.{u} pB := ⟨hcollar, hradB⟩
  have hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u} := by
    refine ⟨haccProf, hordB, ?_⟩
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E at hradB
    linarith
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ := exists_inv_base_C11W Cdist 1 (capWindowRadius_C11E + 1) _
    one_pos prepared hbase hdist hres
  have hΛ : 0 < pB.recenterConstant := lt_of_lt_of_le (by norm_num) pB.recenterConstant_ge_four
  obtain ⟨T, hQ⟩ := exists_budget_tower_C11GT2 hΛ Γ.Ctime (1 / 8646) (by norm_num) hstep X₀ hX₀
    hhist hrad₀
  obtain ⟨a₀, hctrl⟩ := exists_initialControl_C11GT P g
  have hS : ∀ n, (T.toChain.state n).DistanceData Cdist := fun n => (T.inv n).distance
  obtain ⟨W⟩ : Nonempty (∀ m, PreparedSpatialStepRetention (T.toChain.state m)
      (T.toChain.state (m + 1)) (T.toChain.accuracy m) (1 / ((m : ℝ) + 2))
      (T.request m).epsCut (T.request m).Dcut (T.request m).mcut) :=
    ⟨fun m => Classical.choice (T.extension m).retention⟩
  have hshift : ∀ m, (T.toChain.state (m + 1)).shift =
      (T.toChain.state m).history.time (Fin.last (T.toChain.state m).history.eventCount) :=
    fun m => (T.extension m).shift_eq
  have hoffset : ∀ m, (T.toChain.state (m + 1)).offset = (T.toChain.state m).history.eventCount :=
    fun m => (T.extension m).offset_eq
  obtain ⟨F, q, κ, records, hOld, hRaw⟩ := T.toChain.exists_surgery_with_retained_raw_caps hS
    (fun m => (T.request m).epsCut) (fun m => (T.request m).Dcut) (fun m => (T.request m).mcut)
    W hshift hoffset (fun n => T.toChain_accuracy_le_quarter n) a₀ hctrl
  obtain ⟨⟨hTower, -, ⟨hfixed, hradq, hordq, haccq, hrc⟩, hκ, hκanti, hδanti, hρanti, hpref,
    hrecHEq, hcan, hwin, hnc, -, hδlim, hrecent⟩, hdiag, -, -, hmi, -⟩ := hOld
  have hconst := canonicalConstantsSupply_mono_C11RD
    (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) (oldC1_le_C1P6_C11GT6.{u} X1 Γ)
    (oldC2_le_C2P6_C11GT6.{u} X2 Γ)
  have hdelta : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t :=
    fun t ht => (hdiag t ht).1
  have hlinkS : LinkedWindowsSupply_C11E records :=
    (hlinkfine_of_chain_C11GT3 T.toChain).hlinkS10 F q records hTower
      ⟨hfixed, hradq, hordq, haccq, hrc⟩ (fun n i j hij => hrecHEq n i j hij)
  have hguard : ∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
      q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
        diagonalAccuracy_C11S q.delta A
          ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
      A < 12 * (3 : ℝ) ^ m := by
    intro m i A hA hlt
    obtain ⟨-, -, -, -, hAg, -⟩ := hmi m i
    exact lt_of_accuracyGuard_C11Q6 T.toChain q (fun t ht => (hdiag t ht).1) hA hAg hlt
  have hwide : LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta)
      q.neckRadius :=
    hKp Cdist _ T (fun j => (hQ j).1) F q hTower hdiag hguard haccκ hradB hordB
  have hwideF : LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta)
      q.neckRadius :=
    localKappaWideFwd_of_certifiedTower_C11GT6 T (fun j => (hQ j).1) F q hTower hdiag
  have hTD := timeDerivativeSupply_of_astra_C12X T.toChain _ _ _ W hshift hoffset F hTower q
    hρanti (diagonal_neckRadius_of_prefix_C12X T.toChain q (fun n t ht => (hpref n t ht).2.1))
  have hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder := by
    intro D ζ m hζ
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
      (tower_fine_request_eventually_C11W4 T (fun j => (hQ j).2.1) hζ D m)
    refine ⟨k₀, fun k hk => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hk₀ k hk (W k)
    exact ⟨h2, h1, h3⟩
  have hlate := lateLinkedRecordsSupply_of_outer_C12X T.toChain W F q records hfixed hrc hmi hRaw
    hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hnom := lateLinkedRecordsSupplyNom_of_outer_P6NI T.toChain W F q records hfixed hrc hmi
    hRaw hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hSCRS : SameConstructionRetentionSupplyPlus_C11GT6 T :=
    ⟨F, q, κ, records, ⟨hTower, hdiag, hfixed, hradq, hordq, haccq, hrc⟩, ⟨hκ, hκanti, hnc⟩,
      hwide, ⟨hδanti, hρanti, hδlim⟩, ⟨hwin, hrecent, hlinkS, hlate⟩, hcan, hTD, hwideF,
      fun n => eventSlabsDerivative_qcanSup_P6WR T.toChain _ _ _ W hshift hoffset F hTower n,
      hnom⟩
  have hP6 : LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
      (C2P6_C11GT6.{u} X2 Γ) :=
    largerBallCanonicalLateSupply_of_core_C11GT2
      (hP6p Cdist _ T (fun j => (hQ j).1) hSCRS F q hTower hdiag haccP6 hradB hordB)
  have hcanP6 := historyCanonicalSupply_mono_C12X hcan (oldC1_le_C1P6_C11GT6.{u} X1 Γ)
    (oldC2_le_C2P6_C11GT6.{u} X2 Γ)
  have hS8 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) :=
    s8_of_smallVolFwd_C11GT6.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
      (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) P hP3 hprof hfixed hradq hordq haccq hacc₀
      records hlinkS hδanti hρanti hcan hwide hwideF
      (fun A hA hw => hspinep T.toChain F q hTower hdiag haccsp hradB hordB A hA hw hP6)
  have hStrong := strongCanonicalSupplyV2_mono_C12X (strongCanonicalSupplyV2_of_towerFull_C12X
    (hfullp T.toChain F q hTower hdiag haccfull hradB hordB)) (C1ceil_le_C1P6_C11GT6.{u} X1 Γ)
    (C2ceil_le_C2P6_C11GT6.{u} X2 Γ)
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2.2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨T.toChain, F, q, κ, records, Γ.epsilon,
    C1P6_C11GT6.{u} X1 Γ, C2P6_C11GT6.{u} X2 Γ, hTower, rfl,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ, hκanti, hδanti, hρanti, hcanP6, hnc, hδlim,
    hrecent, hS8, hlinkS, hTD, hlate, hP6, hStrong, hS17, frontierCollarSupplyFull_C12X F q⟩

/-- **A12′ v6 顶层缺口定理（R-C11-9 修正形，标准 ceiling）**：binder 只有 `hspine″ hP6b′`。`hspine″` =
v5 `hspine` 的 `hw` guard 换成 `q.neckRadius t ≤ r`（由坏点 ceiling + `hradii` 免费）、`hb` 常数换
`C1P6 / C2P6`；`hP6b′` = R-C11-8 D-4 schema（前提 SCRS⁺）。GAP-2 常数 `epsilon0_C11FR` 在选 `pBase`
之前进 reserve。 -/
theorem a12EnhancedFull_of_gaps_v6fwd_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v6fwd_gen_C11GT6 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u} hspine hP6b

/-! ## 4. 方向记录与 consumers -/

/-- **`hspine″` 比 G1 的 `hspine′` 弱**（同常数）：`nr(t) ≤ r` guard 的 window ⇒ 旧 guard 的 window（取 `w = t`），
故旧 guard 的 spine 证明直接给新形；新形的适用性义务（旧 guard）消失。 -/
theorem hspineNrt_of_hspineOld_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
          (C2P6_C11GT6.{u} X2 Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) :
    ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
          (C2P6_C11GT6.{u} X2 Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A := by
  obtain ⟨εsp, hεsp, hp⟩ := hspine
  refine ⟨εsp, hεsp, fun S F q hT hd ha hr ho A hA hw hb => hp S F q hT hd ha hr ho A hA ?_ hb⟩
  obtain ⟨κ'', hκ'', T, hT, hK⟩ := hw
  refine ⟨κ'', hκ'', T, hT, fun n t p r hTt htr hcurv hvol hold => ?_⟩
  exact hK n t p r hTt htr hcurv hvol (hold t (by nlinarith [sq_nonneg r]) le_rfl)

/-- **G1 的 `hP6b′`（SCRS 前提）⇒ v6 冻结形 `hP6b′`（SCRS⁺ 前提）**：前提变强，P6 义务变弱。 -/
theorem hP6bPlus_of_hP6b_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupply_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ)) :
    ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ) := by
  obtain ⟨εP6, hεP6, hp⟩ := hP6b
  exact ⟨εP6, hεP6, fun Cdist εReserve T hB hS F q hT hd ha hr ho =>
    hp Cdist εReserve T hB (scrs_of_plus_C11GT6 hS) F q hT hd ha hr ho⟩

/-- consumer：SCRS⁺ producer ⇒ G1 的 SCRS 在同一 budget tower 上可供（G1 `hP6b′` 的前提 producer-closed）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εS : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εS Γ) ∧
    ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
      (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j) ∧ RequestCofinal_C11W4 j (T.request j)) →
      pB.modelAccuracy ≤ εS Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      SameConstructionRetentionSupply_C11GT6 T := by
  obtain ⟨εS, hεS, h⟩ := sameConstructionRetentionSupplyPlus_of_tower_C11GT6 P g
  exact ⟨εS, hεS, fun Cdist εReserve T hQ ha hr ho =>
    scrs_of_plus_C11GT6 (h Cdist εReserve T hQ ha hr ho)⟩

/-- consumer：v6（修正形）的结论（A12′）⇒ 晚期共同 neck accuracy 与 A12 的 `hasCommonNeckAccuracy`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-- consumer：v6（修正形）的签名稳定（binder 列表即 `type_of%`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_of_gaps_v6fwd_C11GT6 P g) := a12EnhancedFull_of_gaps_v6fwd_C11GT6 P g

/-- consumer：G1 形（旧 guard）的 `hspine′` 与 `hP6b′` ⇒ A12′（经 `hspineNrt_of_hspineOld_C11GT6`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v6fwd_C11GT6 P g
    (hspineNrt_of_hspineOld_C11GT6 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u} hspine) hP6b

end GC.LongTime.Ch11

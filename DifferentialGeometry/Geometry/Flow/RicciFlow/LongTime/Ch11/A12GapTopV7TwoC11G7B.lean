import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12StrongCoarsenC11G7B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterTwoLevelTimeC11G7B

set_option autoImplicit false

/-!
# A12′ 顶层 v7two：两级精度（双参数阈值）+ 时间载荷（O-CH11-GAPTOP7B G3，后缀 `_C11G7B`）

R-C11-11 D-3（冻结 GAMMA2 G2 的**双参数阈值形** `HSpineTwoLevel_C11G2` / `HP6bTwoLevel_C11G2`，5 行单参数版只作推论）
× R-C11-14 D-2（history-level 时间包；hspine‴ 输入 / hP6b‴ 输出 / 装配三处同步改）：
* **gen 引擎 `a12EnhancedFull_of_gaps_v7two_gen_C11G7B`**（ceiling `X1 X2` + Good-time 常数 `Ct` 泛型）：
  GAPTOP7 v7 gen 引擎（`A12GapTopV7C11G7.lean` sha256 54193d0c9eeb0876…）逐字，只改 (i) hspine‴ 的前提
  `LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6 X1 Γ) (C2P6 X2 Γ)` →
  `CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6 X1 Γ) (C2P6 X2 Γ) (Ct Γ)`；(ii) hP6b‴ 的结论
  `CanonicalLateCore_P6X …` → 同一 `CanonicalLateTimeCore_P6X … (Ct Γ)`；(iii) 装配：hP6b‴ 的 TimeCore 经
  `canonicalLateCore_of_timeCore_P6TC` 投影喂旧 S15（元组的 `hP6`），**完整载荷**喂 hspine‴；(iv) S16 / S6 的粗化换
  G2 的 `strongCanonicalSupplyV2_monoEps_C11G7B`（neck 反演，窗原样）与 `noncollapsed_coarsen_a3_C11G7B`
  （κ·a³）。
  结论 `A12EnhancedFullConclusion_C11F P g` = v6fwd 逐字。reserve 正最小值含 `εsp Γ Γf`、`εP6 Γ Γf`（双参数）、
  `εκ Γf`、`εfull Γf` 与 `epsilon0_C11FR` 在 `Γf`（S8 实际精度）；Budget 用 `Γf.Ctime`。
* **冻结形 `a12EnhancedFull_of_gaps_v7two_C11G7B`**：`X1 X2 := p6X1std / p6X2std`（D-15″ 后的 C1P6* /
  C2P6*）、
  `Ct := p6Ctime_C11G7B`（`C_t*(Γ)`，G1）。合同 def `HSpineTwoLevelTime_C11G7B` /
  `HP6bTwoLevelTime_C11G7B`
  = 冻结形的两个 binder 类型逐字（生成脚本切出）。
* 推论 / 方向：5 行单参数版 `a12EnhancedFull_of_gaps_v7two5_C11G7B`（`εsp Γ _ := εsp Γ`）；旧空间 hspine‴
  （`HSpineTwoLevel_C11G2`）⇒ 新 `HSpineTwoLevelTime`（输入更强，投影即可）；新 `HP6bTwoLevelTime` ⇒ 旧
  `HP6bTwoLevel_C11G2`（投影）。反方向不声称（D-1：空间 core 推不出时间导数界）。
* consumer：G1b 时间版两级 outer wrapper 在 `Ctime := C_t*(Γ)` 处的结论类型 = hP6b‴ 结论类型。
不声称 `hspine‴` / `hP6b‴` 已闭合（仍 OPEN binder；CX-SPINE 新签名 producer、hP6b‴ 完整装配是 repair target）。
生成：build-logs/scratch/O-CH11-GAPTOP7B/gen_g3.py。
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

/-! ## 1. v7two 引擎（ceiling / Good-time 常数泛型，双参数阈值，时间载荷） -/

/-- **A12′ v7two 引擎**：见文件头。 -/
theorem a12EnhancedFull_of_gaps_v7two_gen_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ) (Ct : ClosedBirthConstants → ℝ≥0)
    (hspine : ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
          (C2P6_C11GT6.{u} X2 Γ) (Ct Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ) (Ct Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨Cdist, Γ, Γf, hfine, hΓs, hΓW, -, -, hmake⟩ := hpbaseTwoLevel_C11G2.{u} P g
  obtain ⟨εκ, hεκ, hKp⟩ := hKseed_of_producers_C11KW P g
  obtain ⟨εsp, hεsp, hspinep⟩ := hspine
  obtain ⟨εP6, hεP6, hP6p⟩ := hP6b
  obtain ⟨εfull, hεfull, hfullp⟩ := hfull_ceiling_C11SC P g
  have hε₀ := epsilon0_pos_C11FR.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
    (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P
  have hεT : 0 < εK_threshold_C11GT2 (fun _ => εκ Γf) (fun _ => εsp Γ Γf) (fun _ => εP6 Γ Γf)
      (fun _ => εfull Γf) Γ :=
    εK_threshold_pos_C11GT2 (fun _ => hεκ Γf) (fun _ => hεsp Γ Γf) (fun _ => hεP6 Γ Γf)
      (fun _ => hεfull Γf) Γ
  have hεR : 0 < min εProf_C11E.{u} (min (εK_threshold_C11GT2 (fun _ => εκ Γf)
      (fun _ => εsp Γ Γf) (fun _ => εP6 Γ Γf) (fun _ => εfull Γf) Γ)
      (epsilon0_C11FR.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
        (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P)) :=
    lt_min εProf_pos_C11E (lt_min hεT hε₀)
  obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR
  obtain ⟨hacc, hradB, hordB⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  have haccProf : pB.modelAccuracy ≤ εProf_C11E.{u} := hacc.trans (min_le_left _ _)
  have haccT : pB.modelAccuracy ≤ εK_threshold_C11GT2 (fun _ => εκ Γf) (fun _ => εsp Γ Γf)
      (fun _ => εP6 Γ Γf) (fun _ => εfull Γf) Γ :=
    hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨haccκ, haccsp, haccP6, haccfull⟩ := εK_threshold_le_C11GT2 _ _ _ _ Γ haccT
  have hacc₀ : pB.modelAccuracy ≤ epsilon0_C11FR.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
      (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P :=
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
  obtain ⟨T, hQ⟩ := exists_budget_tower_C11GT2 hΛ Γf.Ctime (1 / 8646) (by norm_num) hstep X₀ hX₀
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
  -- 两级 + 时间载荷：`hP6b‴` 在粗 `Γ` 给 history-level TimeCore；空间投影喂旧 S15（`hP6`），完整载荷喂 spine
  have hP6T : CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
      (C2P6_C11GT6.{u} X2 Γ) (Ct Γ) :=
    hP6p hfine hΓs hΓW Cdist _ T (fun j => (hQ j).1) hSCRS F q hTower hdiag haccP6 hradB hordB
  have hP6 : LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
      (C2P6_C11GT6.{u} X2 Γ) :=
    largerBallCanonicalLateSupply_of_core_C11GT2 (canonicalLateCore_of_timeCore_P6TC hP6T)
  have hΓ11 : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  have hC1 : C1ceil_C11SC.{u} Γf ≤ C1P6_C11GT6.{u} X1 Γ :=
    hfine.2.1.trans (C1ceil_le_C1P6_C11GT6.{u} X1 Γ)
  have hC2 : C2ceil_C11SC.{u} Γf ≤ C2P6_C11GT6.{u} X2 Γ :=
    hfine.2.2.1.trans (C2ceil_le_C2P6_C11GT6.{u} X2 Γ)
  have hcanP6 := historyCanonicalSupply_mono_all_C11G2 hcan hfine.epsilon_le hΓ11
    ((oldC1_le_C1ceil_C11SC.{u} Γf).trans hC1) ((oldC2_le_C2ceil_C11SC.{u} Γf).trans hC2)
  have hS8 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) :=
    s8_of_smallVolFwd_C11GT6.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
      (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P hP3 hprof hfixed hradq hordq haccq hacc₀
      records hlinkS hδanti hρanti hcan hwide hwideF
      (fun A hA hw => hspinep hfine T.toChain F q hTower hdiag haccsp hradB hordB A hA hw hP6T)
  have hStrong := strongCanonicalSupplyV2_monoEps_C11G7B (strongCanonicalSupplyV2_of_towerFull_C12X
    (hfullp T.toChain F q hTower hdiag haccfull hradB hordB)) hfine.epsilon_le hΓ11 hC1 hC2
  obtain ⟨hκ', hκ'anti, hnc'⟩ := noncollapsed_coarsen_a3_C11G7B hfine hκ hκanti hnc
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2.2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_cone_C11G2 hP3 hprof ⟨T.toChain, F, q,
    fun t => κ t * (Γf.epsilon / Γ.epsilon) ^ 3, records, Γ.epsilon,
    C1P6_C11GT6.{u} X1 Γ, C2P6_C11GT6.{u} X2 Γ, hTower, Γ.epsilon_cone,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ', hκ'anti, hδanti, hρanti, hcanP6, hnc', hδlim,
    hrecent, hS8, hlinkS, hTD, hlate, hP6, hStrong, hS17, frontierCollarSupplyFull_C12X F q⟩

/-! ## 2. 冻结形与合同 def -/

/-- **A12′ v7two 顶层缺口定理（冻结形：双参数阈值、标准 ceiling、`C_t*(Γ)`）**：binder 只有 `hspine‴ hP6b‴`。 -/
theorem a12EnhancedFull_of_gaps_v7two_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v7two_gen_C11G7B P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u}
    p6Ctime_C11G7B.{u} hspine hP6b

/-- **hspine‴（时间载荷，双参数）**：冻结形 `hspine` binder 的类型逐字。 -/
def HSpineTwoLevelTime_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
    (∀ Γ Γf, 0 < εsp Γ Γf) ∧
    ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
    (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
    F.tower = S.tower →
    (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
    pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
    2 ≤ pB.modelOrder →
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
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
      LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A

/-- **hP6b‴（时间载荷，双参数）**：冻结形 `hP6b` binder 的类型逐字。 -/
def HP6bTwoLevelTime_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ,
    (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
    ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
    Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
      (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
    (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
      (T.request j)) →
    SameConstructionRetentionSupplyPlus_C11GT6 T →
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
    (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
    pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
    2 ≤ pB.modelOrder →
    CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
      (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ)

/-- 合同形 ⇒ A12′ 增强结论（冻结形的 def 版）。 -/
theorem a12EnhancedFull_of_v7two_contracts_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hs : HSpineTwoLevelTime_C11G7B.{u} P g) (hp : HP6bTwoLevelTime_C11G7B.{u} P g) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v7two_C11G7B P g hs hp

/-! ## 3. 推论与方向 -/

/-- **旧空间 hspine‴ ⇒ 新时间 hspine‴**（输入 TimeCore 投影成空间 core 即可）。 -/
theorem hspineTime_of_hspineTwoLevel_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : HSpineTwoLevel_C11G2.{u} P g) : HSpineTwoLevelTime_C11G7B.{u} P g := by
  obtain ⟨εsp, hεsp, hs⟩ := h
  exact ⟨εsp, hεsp, fun hfine S F q hF hq hacc hrad hord A hA hw hT =>
    hs hfine S F q hF hq hacc hrad hord A hA hw
      (largerBallCanonicalLateSupply_of_core_C11GT2 (canonicalLateCore_of_timeCore_P6TC hT))⟩

/-- **新时间 hP6b‴ ⇒ 旧空间 hP6b‴**（输出投影）。 -/
theorem hP6bTwoLevel_of_time_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : HP6bTwoLevelTime_C11G7B.{u} P g) : HP6bTwoLevel_C11G2.{u} P g := by
  obtain ⟨εP6, hεP6, hp⟩ := h
  exact ⟨εP6, hεP6, fun hfine hs hW Cdist εReserve T hB hS F q hF hq hacc hrad hord =>
    canonicalLateCore_of_timeCore_P6TC
      (hp hfine hs hW Cdist εReserve T hB hS F q hF hq hacc hrad hord)⟩

/-- **5 行单参数版**（推论；阈值 `εsp Γ` / `εP6 Γ` 只依赖粗 `Γ`，取 `fun Γ _ => εsp Γ`）。 -/
theorem a12EnhancedFull_of_gaps_v7two5_C11G7B (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨εsp, hεsp, hs⟩ := hspine
  obtain ⟨εP6, hεP6, hp⟩ := hP6b
  exact a12EnhancedFull_of_gaps_v7two_C11G7B P g ⟨fun Γ _ => εsp Γ, fun Γ _ => hεsp Γ, hs⟩
    ⟨fun Γ _ => εP6 Γ, fun Γ _ => hεP6 Γ, hp⟩


/-! ## 4. consumers -/

/-- consumer (i)：G1b 时间版两级 outer wrapper 在 `Ctime := C_t*(Γ)` 处的结论 = hP6b‴ 的结论类型
`CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6 std Γ) (C2P6 std Γ) (C_t*(Γ))`（类型对齐；
`hgapJ hrestP` 仍 OPEN）。 -/
example : True := by
  obtain ⟨_c₀, -, _Cb, _Rn, _ζ, _δ₀, _m₀, -, -, -, -, -, hW⟩ :=
    ObservedHistory.outerTwoLevelTime_C11G7B.{0}
  have _h := fun {P : OrientedThreeStage.{0}} {g : P.Metric} {pB : CutoffParameters}
      {Γ Γf : ClosedBirthConstants} {Cdist : ℝ≥0} {εReserve : ℝ}
      (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve) hS hfine hs hW'
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} hF hq Ctime₀ T₀ Qt hT₀m hQm hgap
      hrest =>
    (hW Γ.epsilon T hS hfine rfl hs hW' (F := F) (q := q) hF hq
      (Ctime := p6Ctime_C11G7B.{0} Γ) rfl rfl (p6Ctime_bounds_C11G7B.{0} Γ).1
      (p6Ctime_bounds_C11G7B.{0} Γ).2 Ctime₀ T₀ Qt hT₀m hQm hgap hrest :
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{0} p6X1std_C11GT6.{0} Γ)
        (C2P6_C11GT6.{0} p6X2std_C11GT6.{0} Γ) (p6Ctime_C11G7B.{0} Γ))
  trivial

/-- consumer (ii)：旧空间 spine producer + 新时间 hP6b‴ producer 已足以喂 v7two（方向引理的用法）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (hs : HSpineTwoLevel_C11G2.{u} P g)
    (hp : HP6bTwoLevelTime_C11G7B.{u} P g) : A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_v7two_contracts_C11G7B P g (hspineTime_of_hspineTwoLevel_C11G7B P g hs) hp

end GC.LongTime.Ch11

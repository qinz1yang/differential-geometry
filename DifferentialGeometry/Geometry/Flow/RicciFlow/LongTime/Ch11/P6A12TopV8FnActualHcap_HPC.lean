import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12TopV8FnActualS14CXW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12TopV8FnActualCHN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HaccuracyTowerC12C

/-!
# HPCCAP：v8 collar 引擎（fn + 供给 actual 版）的 hcap 透传孪生（后缀 `_HPC`）

D-24-7 / F-24-7：`a12EnhancedFull_of_gaps_v8Collar_actual_S14CXW` 与其 HN wrapper 逐字，只改三处：
(1) `hP6b` 合同在 `LateLinkedRecordsSupply` 后加 tower 的 cap 条款 `hcap`；(2) tower 由 ch12 孪生 builder
`exists_budget_tower_scaled_C12C` 取（前提与 `exists_budget_tower_C11GT2` 逐字相同，额外给出 cap 条款）；
(3) `hP6p` 调用传**同一** tower 的 `hcap`。hcap 在**实际构造点**（引擎内这个 `obtain` 出的 tower）闭合量词：
合同槽对满足 hcap 的 tower 全称，实例化点就是该 tower，不是用"∃ 特殊 tower"付"∀ tower"。
无新 binder；hspine 不动。
-/

set_option autoImplicit false

noncomputable section

universe u

section V8Engine

open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal

namespace GC.LongTime.Ch11
open GC.LongTime.Ch11 (p6CoarseCHN_CHN one_le_p6CoarseCHN_CHN p6CoarseC_le_p6CoarseCHN_CHN)

/-- **X12 引擎（collar v8 引擎的 fn + 供给孪生）**：见文件头。 -/
theorem a12EnhancedFull_of_gaps_v8Collar_actual_hcap_HPC (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ) (Ct : ClosedBirthConstants → ℝ≥0)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hspine : ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder → (Rn Γf ≤ pB.modelRadius ∧ mn Γf ≤ pB.modelOrder) →
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
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q →
      (∀ j : ℕ, (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤
        (T.lookahead j).rNext) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos →
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ) (Ct Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨Cdist, Γ, Γf, hfine, hΓs, hΓW, -, -, hmake⟩ := hpbaseTwoLevel_v8_P6HV8.{u} P g
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
  obtain ⟨pB, prepared, hbase, hdist, hres, hPB, hcollar, hstep⟩ := hmake (Rn Γf) (mn Γf) _ hεR
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
  obtain ⟨T, -, hTc⟩ := exists_budget_tower_scaled_C12C hΛ Γf.Ctime (1 / 8646) (by norm_num)
    hstep X₀ hX₀ hhist hrad₀
  have hQ := fun j => (hTc j).1
  have hcap := fun j => (hTc j).2
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
    hP6p hfine hΓs hΓW Cdist _ T (fun j => (hQ j).1) hSCRS F q hTower hdiag hlate hcap haccP6 hradB
      hordB hcollar
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
      (fun A hA hw =>
        hspinep hfine T.toChain F q hTower hdiag hTD haccsp hradB hordB hPB A hA hw hP6T)
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


/-- **`a12EnhancedFull_of_v8_collar_actual_S14CXW_CHN`**（collar 版 v8 合同形）：`X1 X2 := p6X1std /
    p6X2std`、`Ct := p6CtimeHN_CHN`。 -/
theorem a12EnhancedFull_of_v8_collar_actual_hcap_CHN_HPC (P : OrientedThreeStage.{u})
    (g : P.Metric)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hspine : ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder → (Rn Γf ≤ pB.modelRadius ∧ mn Γf ≤ pB.modelOrder) →
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ)
          (C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ) (p6CtimeHN_CHN.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hp :
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
        GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q →
        (∀ j : ℕ, (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤
        (T.lookahead j).rNext) →
        pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
        2 ≤ pB.modelOrder → collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength
          pB.fixed.collar_pos →
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ)
          (C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ) (p6CtimeHN_CHN.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v8Collar_actual_hcap_HPC P g p6X1HN_CHN.{u} p6X2HN_CHN.{u}
    p6CtimeHN_CHN.{u} Rn mn hspine hp

end GC.LongTime.Ch11

end V8Engine

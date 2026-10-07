import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWireSeedC11KW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV3C11GT3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallScaleSeedC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WindowGlueSeedScaleC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.S8WireC11V4

set_option autoImplicit false

/-!
# A12′ 顶层缺口定理第五版（Route B：hK 槽 seedScale 形；S-CH11-KWIRE G3b，后缀 `_C11KW`；PROVISIONAL）

lead 13:4x 裁定 (b)。消费者核查（`build-logs/scratch/S-CH11-KWIRE/TABLE.md` §5）：v3 `hK` 的结论
`LocalKappaWideSupply_C11Q` 在 A12′ 顶层只有一个消费者——`hS8wire`（`s8_of_smallVol_C11V4`）→
`smallVolWindow_of_hext_C11V4` → **全种子** `nr := 0` window
（`∃ κ'', LocalKappaWindowAt_P6B F (fun _ => 0) A κ''`）→ `hspine` 的 `hw` 前提。种子尺度形只给
**种子限制** 的 `nr := 0` window（SMALLVOL5 G2：只对 `∀ w ∈ [t − r²/2, t], nr w ≤ r` 的种子），
因此：

* `hK` 槽 → `hKseed`（`LocalKappaWideScaledSupply_C11Q4b`，**producer-closed**，
  `hKseed_of_producers_C11KW`）：OK；
* `hspine` 的 `hw` 前提 **必须** 同步换成种子限制 window（`hspine` 是 binder，其 producer 是 P6 selection
  反证链，坏点序列满足 `r/nr → ∞`（`ratio_of_selection_C11Q4b`），只用种子限制 window）：
  **这是唯一一处无法保持 v3 逐字的 binder**（全称 window 需要未缩放 wide ⇐ OPEN-1）。
  `hP6b hfull` 与 v3 逐字同。

本文件：
* `s8_of_smallVolSeed_C11KW`：`s8_of_smallVol_C11V4` 的种子尺度类比（尺度 wide + V5 `hsmallSeed` +
  P6B 真实 `nr` window（`L = 1` 小种子空真）+ V5 G2 拼接 ⇒ 种子限制 window ⇒ `hspine` ⇒ S8）；
* `a12EnhancedFull_of_gaps_v5_C11KW`：binder `hKseed hspine hP6b hfull`；`hKseed` 逐字
  （v3 `hK` 的结论换成尺度 wide）；
  `hspine` 仅 `hw` 前提换成种子限制 window；证明 = v2 证明体（`hpbase` / `hlinkfine` 按 v3 实例化，S8 换成
  `s8_of_smallVolSeed_C11KW`）；
* `a12EnhancedFull_of_gaps_v5_noK_C11KW`：`hKseed` 由 `hKseed_of_producers_C11KW` 供给，binder 只剩
  `hspine hP6b hfull`。
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

/-- `collarAdmitsAllOrders_C11E` 只依赖 `collarLength` 的值（正性证明无关）。 -/
theorem collarAdmitsAllOrders_congr_C11KW (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (h : a = a')
    (hh : collarAdmitsAllOrders_C11E.{u} a ha) : collarAdmitsAllOrders_C11E.{u} a' ha' := by
  subst h
  exact hh

/-! ## 1. S8 wire 的种子尺度类比 -/

/-- **`s8_of_smallVol_C11V4` 的种子尺度类比**：尺度 wide 供给（`hKseed` 的结论）+ P6 (b) + 种子限制 `hspine`
⇒ S8。比 V4 多一个 `q.fixed = pBase.fixed`（`CollarWindowSupply_C11E q` 的 collar 条）。 -/
theorem s8_of_smallVolSeed_C11KW (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {pBase q : CutoffParameters},
      CollarWindowSupply_C11E.{u} pBase → ModelConstraintsSupply_C11E pBase εProf_C11E.{u} →
      q.fixed = pBase.fixed → q.modelRadius = pBase.modelRadius →
      q.modelOrder = pBase.modelOrder → q.modelAccuracy = pBase.modelAccuracy →
      pBase.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, LinkedWindowsSupply_C11E records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      LargerBallCanonicalLateSupply_C11E F ε C1 C2 →
      (∀ A : ℝ, 1 < A →
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
        LargerBallCanonicalLateSupply_C11E F ε C1 C2 →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) →
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) := by
  obtain ⟨ε₀, hε₀, hE⟩ := hsmallSeed_of_wideScaledSupply_C11V5.{u} ε C1 C2 P
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F pBase q hP3 hprof hfixed hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon hwide
    hb hspine A hA
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
  have hq : q.modelAccuracy ≤ ε₀ := by
    rw [hacc]
    exact hacc₀
  have hS7 := largerBallAccuracySupply_diagonal_C11S q hδanti
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B hS7 (localKappaP6B_of_wideScaled_C11KW hwide)) A hA0
  obtain ⟨κ', hκ', hsmall⟩ := hE hA0 hP3q hprofq hq records (hwin_of_linkedWindows_C11V3 hlink)
    hδanti hρanti hcanon hwide
  exact hspine A hA ⟨min κ₁ κ', lt_min hκ₁ hκ',
    localKappaWindow_zero_of_window_and_small_seedScale_C11V5 hW₁ hsmall⟩ hb

/-! ## 2. v5 顶层 -/

/-- **A12′ v5 顶层缺口定理（Route B）**：binder `hKseed hspine hP6b hfull`。`hKseed` = v3 `hK` 的 binder 逐字、
结论换成 `LocalKappaWideScaledSupply_C11Q4b`；`hspine` 仅 `hw` 前提换成种子限制 window；`hP6b hfull` 与 v3 逐字同。 -/
theorem a12EnhancedFull_of_gaps_v5_C11KW (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hKseed : ∃ εκ : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εκ Γ) ∧
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
      LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
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
    A12EnhancedFullConclusion_C11F P g := by
  have hpbase := hpbase_of_provider_C11GT3 P g
  have hlinkfine : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g), LinkedAndFine_C11GT2 S :=
    fun S => hlinkfine_of_chain_C11GT3 S
  obtain ⟨Cdist, Γ, hmake⟩ := hpbase
  obtain ⟨εκ, hεκ, hKp⟩ := hKseed
  obtain ⟨εsp, hεsp, hspinep⟩ := hspine
  obtain ⟨εP6, hεP6, hP6p⟩ := hP6b
  obtain ⟨εfull, hεfull, hfullp⟩ := hfull
  obtain ⟨ε₀, hε₀, hS8wire⟩ := s8_of_smallVolSeed_C11KW.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
    (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) P
  have hεR : 0 < min εProf_C11E.{u} (min (εK_threshold_C11GT2 εκ εsp εP6 εfull Γ) ε₀) :=
    lt_min εProf_pos_C11E (lt_min (εK_threshold_pos_C11GT2 hεκ hεsp hεP6 hεfull Γ) hε₀)
  obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR
  obtain ⟨hacc, hradB, hordB⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  have haccProf : pB.modelAccuracy ≤ εProf_C11E.{u} := hacc.trans (min_le_left _ _)
  have haccT : pB.modelAccuracy ≤ εK_threshold_C11GT2 εκ εsp εP6 εfull Γ :=
    hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨haccκ, haccsp, haccP6, haccfull⟩ := εK_threshold_le_C11GT2 εκ εsp εP6 εfull Γ haccT
  have hacc₀ : pB.modelAccuracy ≤ ε₀ := hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
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
    hrecHEq, hcan, -, hnc, -, hδlim, hrecent⟩, hdiag, -, -, hmi, -⟩ := hOld
  have hconst := canonicalConstantsSupply_of_closedBirthConstants_C11A Γ
  have hdelta : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t :=
    fun t ht => (hdiag t ht).1
  have hlinkS : LinkedWindowsSupply_C11E records :=
    (hlinkfine T.toChain).hlinkS10 F q records hTower ⟨hfixed, hradq, hordq, haccq, hrc⟩
      (fun n i j hij => hrecHEq n i j hij)
  have hP6 : LargerBallCanonicalLateSupply_C11E F Γ.epsilon (max Γ.C1s Γ.Cbirth)
      (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) :=
    largerBallCanonicalLateSupply_of_core_C11GT2
      (hP6p T.toChain F q hTower hdiag haccP6 hradB hordB)
  have hguard : ∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
      q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
        diagonalAccuracy_C11S q.delta A
          ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
      A < 12 * (3 : ℝ) ^ m := by
    intro m i A hA hlt
    obtain ⟨-, -, -, -, hAg, -⟩ := hmi m i
    exact lt_of_accuracyGuard_C11Q6 T.toChain q (fun t ht => (hdiag t ht).1) hA hAg hlt
  have hS8 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) :=
    hS8wire hP3 hprof hfixed hradq hordq haccq hacc₀ records hlinkS hδanti hρanti hcan
      (hKp Cdist _ T (fun j => (hQ j).1) F q hTower hdiag hguard haccκ hradB hordB) hP6
      (fun A hA hw hb => hspinep T.toChain F q hTower hdiag haccsp hradB hordB A hA hw hb)
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
    hcof ((hlinkfine T.toChain).hfine_S14 W)
  have hStrong := strongCanonicalSupplyV2_of_towerFull_C12X
    (hfullp T.toChain F q hTower hdiag haccfull hradB hordB)
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2.2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨T.toChain, F, q, κ, records, Γ.epsilon,
    max Γ.C1s Γ.Cbirth, max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)), hTower, rfl,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ, hκanti, hδanti, hρanti, hcan, hnc, hδlim,
    hrecent, hS8, hlinkS, hTD, hlate, hP6, hStrong, hS17,
    frontierCollarSupplyFull_C12X F q⟩

/-- `hKseed` 由 `hKseed_of_producers_C11KW` 供给：binder 只剩 `hspine hP6b hfull`。 -/
theorem a12EnhancedFull_of_gaps_v5_noK_C11KW (P : OrientedThreeStage.{u}) (g : P.Metric)
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
  a12EnhancedFull_of_gaps_v5_C11KW P g (hKseed_of_producers_C11KW P g) hspine hP6b hfull

/-- consumer：v5 的结论（A12′）⇒ 晚期共同 neck accuracy 与 A12 的 `hasCommonNeckAccuracy`
（与 v1–v4 同一结论类型，下游不变）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

end GC.LongTime.Ch11

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV3C11GT3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingWireC11SC

set_option autoImplicit false

/-!
# A12′ 顶层缺口定理第四版：`hfull` 在 shared strong ceiling 上（O-CH11-S16CEIL G4，后缀 `_C11SC`）

v3（`a12EnhancedFull_of_gaps_v3_C11GT3`，不改）的 `hfull` binder 常数是旧 ceiling
`max Γ.C1s Γ.Cbirth` / `max Γ.C2s (max Γ.Cbirth Γ.Cgrad)`。S16 uniform engine 的 strong 常数只被
shared ceiling `C1ceil_C11SC Γ = C1star_C12X Γ Ccore Cu`（`Ccore Cu` = engine 的闭项，只依赖 `Γ.epsilon`，
在 `P / g / B / κ` 之前固定）支配，旧 ceiling 上的 `hfull` 不可得（常数只能升）。所以：

* `a12EnhancedFull_of_gaps_v4_C11SC`：binder `hK hspine hP6b hfull`，**前三个与 v3 逐字相同**，`hfull`
  只把两个常数换成 `C1ceil_C11SC Γ` / `C2ceil_C11SC Γ`（其余字段逐字，不放宽）。证明 = v2 证明体
  （`hpbase` / `hlinkfine` 按 v3 实例化），`hext` 的共用对取 shared ceiling：S4 / S5 / S15 用
  `canonicalConstantsSupply_mono_C11RD` / `historyCanonicalSupply_mono_C12X` /
  `largerBallCanonicalLateSupply_mono_C12X` 从旧 ceiling 升上来（`oldC1_le_C1ceil_C11SC`），S16 直接在
  ceiling 上；`hS8` 仍在旧 ceiling 上消费 `hP6`（不变）。
* `hfull_ceiling_C11SC`：v4 的 `hfull` binder 对一切 `P g` 成立（`hfull_of_chain_C11SC`，`εfull := 1`），
  依赖 G2 的 state 字段 `C1S_le / C2S_le`；于是
* `a12EnhancedFull_of_gaps_v4_noFull_C11SC`：binder 只剩 `hK hspine hP6b`（3 个）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-- **A12′ v4 顶层缺口定理**：binder `hK hspine hP6b hfull`；前三个与 v3 逐字相同，`hfull` 的常数是
shared ceiling `C1ceil_C11SC Γ` / `C2ceil_C11SC Γ`。 -/
theorem a12EnhancedFull_of_gaps_v4_C11SC (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hK : ∃ εκ : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εκ Γ) ∧
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
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
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
        ∃ W : SpatialCanonicalWitness s.metric Γ.epsilon (C1ceil_C11SC.{u} Γ)
            (C2ceil_C11SC.{u} Γ) x,
          W.capTubeHasNeckChart Γ.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ)
              (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
              (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
                G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
              s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G Γ.epsilon x
                s.time) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨Cdist, Γ, hmake⟩ := hpbase_of_provider_C11GT3 P g
  obtain ⟨εκ, hεκ, hKp⟩ := hK
  obtain ⟨εsp, hεsp, hspinep⟩ := hspine
  obtain ⟨εP6, hεP6, hP6p⟩ := hP6b
  obtain ⟨εfull, hεfull, hfullp⟩ := hfull
  obtain ⟨ε₀, hε₀, hS8wire⟩ := s8_of_smallVol_C11V4.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
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
  have hconst := canonicalConstantsSupply_mono_C11RD
    (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) (oldC1_le_C1ceil_C11SC.{u} Γ)
    (oldC2_le_C2ceil_C11SC.{u} Γ)
  have hdelta : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t :=
    fun t ht => (hdiag t ht).1
  have hlinkS : LinkedWindowsSupply_C11E records :=
    (hlinkfine_of_chain_C11GT3 T.toChain).hlinkS10 F q records hTower
      ⟨hfixed, hradq, hordq, haccq, hrc⟩
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
    hS8wire hP3 hprof hradq hordq haccq hacc₀ records hlinkS hδanti hρanti hcan
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
    hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hStrong := strongCanonicalSupplyV2_of_towerFull_C12X
    (hfullp T.toChain F q hTower hdiag haccfull hradB hordB)
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2.2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨T.toChain, F, q, κ, records, Γ.epsilon,
    C1ceil_C11SC.{u} Γ, C2ceil_C11SC.{u} Γ, hTower, rfl,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ, hκanti, hδanti, hρanti,
    historyCanonicalSupply_mono_C12X hcan (oldC1_le_C1ceil_C11SC.{u} Γ)
      (oldC2_le_C2ceil_C11SC.{u} Γ), hnc, hδlim, hrecent, hS8, hlinkS, hTD, hlate,
    largerBallCanonicalLateSupply_mono_C12X hP6 (oldC1_le_C1ceil_C11SC.{u} Γ)
      (oldC2_le_C2ceil_C11SC.{u} Γ), hStrong, hS17,
    frontierCollarSupplyFull_C12X F q⟩


/-- **v4 的 `hfull` binder 无条件成立**（G2 之后）：`εfull := 1`，`hfull_of_chain_C11SC`。 -/
theorem hfull_ceiling_C11SC (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εfull : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εfull Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εfull Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
        ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
        ∃ W : SpatialCanonicalWitness s.metric Γ.epsilon (C1ceil_C11SC.{u} Γ)
            (C2ceil_C11SC.{u} Γ) x,
          W.capTubeHasNeckChart Γ.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ)
              (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
              (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
                G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
              s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G Γ.epsilon x
                s.time :=
  ⟨fun _ => 1, fun _ => one_pos, fun S F q hTower hdiag _ _ _ =>
    hfull_of_chain_C11SC S F hTower q (fun t ht => (hdiag t ht).2)⟩

/-- **A12′ v4，`hfull` 已付**：binder 只剩 `hK hspine hP6b`（类型与 v3 逐字相同）。 -/
theorem a12EnhancedFull_of_gaps_v4_noFull_C11SC (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hK : ∃ εκ : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εκ Γ) ∧
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
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
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
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)))) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v4_C11SC P g hK hspine hP6b (hfull_ceiling_C11SC P g)

/-- consumer：v4（`hfull` 已付）的结论（A12′）⇒ 晚期共同 neck accuracy 与 A12 的
`hasCommonNeckAccuracy`（与 v1 / v2 / v3 同一结论类型）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-- consumer：v4 的签名稳定（binder 列表即 `type_of%`），`hfull` 已付版同。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_of_gaps_v4_noFull_C11SC P g) :=
  a12EnhancedFull_of_gaps_v4_noFull_C11SC P g

end GC.LongTime.Ch11

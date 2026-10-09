import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopC11GT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopBudgetC11GT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopAdapterC11GT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopLinkedC11GT2

set_option autoImplicit false

/-!
# S-CH11-GAPTOP2 G1 / G2：A12′ 顶层缺口定理第二版 `a12EnhancedFull_of_gaps_v2_C11GT2`（后缀 `_C11GT2`）

`a12EnhancedFull_of_gaps_C11GT`（`A12GapTopC11GT`，不改）的 R-C11-6 D-13 四项修正 + D-14 合并。
结论仍是 `A12EnhancedFullConclusion_C11F P g`；binder 列表（逐字、可 grep）：

`hpbase  hK  hspine  hP6b  hlinkfine  hfull`（**6 个**；旧版 7 个，`hlinkS10` + `hfine` 合并为 `hlinkfine`）。
旧版的自由参数 `εK hεK` 消失：阈值由各 producer binder 的 `∃ ε_i` 给（G4）。

## 与旧版的逐项差异
* **G1 `hK` 改 budget 形**（D-13(1)）：`hK` 不再对任意 `PreparedSpatialChain` 成立，而是对
  `BlockTower_C11W` 且 `∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
  (T.lookahead j) (T.request j)`（FINEPACK `budgetChoice_dominating_C11Q6` 结论形，允许依赖
  `(j, X, ℓ, req)`）成立，chain 即 `T.toChain`。W0 在 `exists_budget_tower_C11GT2` 里**生产**该证书
  （`budgetChoice_certified_C11GT2`，同时给 `RequestCofinal_C11W4` 与 `accuracyCap ≤ 1/8646`）。
  所以顶层**没有**单独的 `hbudget` binder：证书不是假设，是 W0 的输出，`hK` 只在带证书的 tower 上被调用。
  **α 绑定核（D-2(iii)）**：κ 线的精度 `α = diagonalAccuracy_C11S q.delta` 由顶层固定（`hK` 的结论里
  就是它，producer 不能自由重选）；"指定 α 满足预算"由顶层**证**并作为 `hK` 的前提 `hguard` 交给
  producer：每个 block 事件时刻 `s` 上 `q.delta s < α(A, s) → A < 12·3^m`（raw caps 的 m-i 子句 +
  FINEPACK `lt_of_accuracyGuard_C11Q6`），即 guard 把 α 的比较范围限在本 block 请求覆盖的 level `m` 内。
* **G2 `hfine` → `hfine_S14`**（D-13(2)）：S14 的 `hasLinkedCanonicalWindow` 供给（晚期 fine static
  caps linked），现为 `hlinkfine` 的 `hfine_S14` 字段。它**不是**κ 内部的 `hfine_K3`
  （`KappaFineScale_C11Q5`，K3 请求的精度包络）：后者是另一个义务，在 `hK` 的 producer 内
  （FINEPACK `exists_pre841Data_of_retention_C11Q6` / KWRAP hK3 wrapper）；event-contact / URE 请求
  仍在 `hnode / hure`，也在 `hK` 的 producer 内。`hfine_S14` 不含整个 quotient 上的 `hact`。
* **G3 `hP6b` : `CanonicalLateCore_P6X`**（D-13(3)）：`hP6b` 的类型换成 P6SEL 的 (b) 最小合同；
  `hspine` 的输入、`s8_of_smallVol_C11V4` 的 `hP6`、`a12EnhancedFull_of_chain_C12X` 的 P6 (b) 字段经
  adapter `largerBallCanonicalLateSupply_of_core_C11GT2`（S15 G2a 桥）喂入。adapter **不需要额外的
  boundary binder**（全时刻条件已在 `CanonicalLateCore_P6X` 的形里）。
* **G4 `εK` 来源**（D-13(4)）：`hK / hspine / hP6b / hfull` 各带 `∃ ε_i`（`∀ Γ, 0 < ε_i Γ`），
  顶层取 `εK_threshold_C11GT2 εκ εsp εP6 εfull`（四者 min），`pB.modelAccuracy ≤` 它 ⇒ 各 producer 的
  阈值条件（`εK_threshold_le_C11GT2`）。producer 因此是对**它自己给的**阈值证全称结论。
* **G5 `hlinkfine`**（D-14）：`hlinkS10` 与 `hfine_S14` 合成 `LinkedAndFine_C11GT2 S`，对全体 chain
  `∀ S` 一个 binder（同一 insertion producer + transport）。字段形对齐 S10HORN 的
  `linkedWindowsSupply_of_chain_C11SL`（`hstatic` + 五项 bridge）与 P5L `hlink`（`∃ k₁, ∀ k ≥ k₁`），
  都比旧版 binder 弱。

## 保持不变
`hpbase`（W6 输出 + 对同一 `pB` 的 collar 合取项，PBASE 路线 A）、`hspine`（`1 < A`，D-14 取整说明
同旧版）、`hfull`（S16 tower Full 形；仍独立义务，不并入 static linked-window 或 P6 (b)）。
`hK` 不并入需要 P6 (b) 的 package（它是 P6 K-route 的上游输入）；`hspine / hP6b` 内部仍按 (a)→(b)→(c)
生产（本文件只是把 binder 并排列出，不隐藏相互调用）。
证明体 = 旧版的 W6 tower + `exists_surgery_with_retained_raw_caps` 逐项供给，其中 W0 换成
`exists_budget_tower_C11GT2`，S8 接线的 `hK` 取 budget 形，`hP6` 经 adapter。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-- **A12′ v2 顶层缺口定理，第二版**：binder `hpbase hK hspine hP6b hlinkfine hfull`（6 个）。
`hK` = 带预算证书的 tower 上的 κ 线（G1）；`hlinkfine = hlinkS10 + hfine_S14`（G2 / G5）；
`hP6b : CanonicalLateCore_P6X`（G3）；各阈值由 producer 的 `∃ ε_i` 给（G4）。
证明 = W6 tower（W0 带预算证书）+ `exists_surgery_with_retained_raw_caps` 逐项调用生产者，再喂
`a12EnhancedFull_of_chain_C12X`。 -/
theorem a12EnhancedFull_of_gaps_v2_C11GT2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hpbase : ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), ∀ εReserve : ℝ, 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j)
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
    (hlinkfine : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g), LinkedAndFine_C11GT2 S)
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
  obtain ⟨Cdist, Γ, hmake⟩ := hpbase
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

/-- consumer：v2 顶层定理的结论（A12′）⇒ 晚期共同 neck accuracy 与 A12 的 `hasCommonNeckAccuracy`
（与 v1 同一结论类型，下游不变）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-- consumer：顶层定理的签名稳定（binder 列表即 `type_of%`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_of_gaps_v2_C11GT2 P g) := a12EnhancedFull_of_gaps_v2_C11GT2 P g

end GC.LongTime.Ch11

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.A12FullConsumerC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.TimeDerivativeC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.FrontierCollarFullC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.CompatibleCapsC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeltaKnobC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.P5LinkedSupplyC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.LinkedWindowsC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongSupplyV2PackMainC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.RequestCofinalC11W4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.ReserveByPointC11W6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.S8WireC11V4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRawCapsPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBirthVolumeOrReserve

set_option autoImplicit false

/-!
# S-CH11-GAPTOP G2：A12′ v2 的顶层缺口定理 `a12EnhancedFull_of_gaps_C11GT`（后缀 `_C11GT`）

`a12EnhancedFull_of_gaps_C11GT P g εK hεK hpbase hK hspine hP6b hlinkS10 hfine hfull :
A12EnhancedFullConclusion_C11F P g`：把树内现有全部供给逐项调用，再喂
`a12EnhancedFull_of_chain_C12X`（`Ch11/External/A12FullConsumerC12X`）；**binder 列表 = "A12′ 还差什么"**
（逐字、可 grep：`hpbase hK hspine hP6b hlinkS10 hfine hfull`，外加自由阈值参数 `εK hεK`）。

## 路线（与 `a12Enhanced_of_chain_C11P2` 的"裸 chain"不同：用 W6 block tower）
裸 `exists_prepared_spatial_chains_from_initial` 只给 `S`，给不出 S11 / S14 需要的 retention 族 `W`、
`hshift`、`hoffset`；W 路线（`Outer/ReserveByPointC11W6` + `Outer/BlockStepDefsC11W`）的 `BlockTower`
自带 `(T.extension m).retention`，且 `εReserve` 在 `C`、`P g` 之后选（GAP-2 的量词次序）。

1. `hpbase`（W6 输出 + collar）给 `Cdist Γ`，`ε₀ := s8_of_smallVol_C11V4 …`（只依赖 `(ε,C1,C2,N(P))`），
   `εReserve := min εProf (min (εK Γ) ε₀)`，取 `pB`、`prepared`、`∀ j, BlockStep`；
2. `exists_inv_base_C11W` 取 `X₀`；`tower_of_blockSteps_pred_C11GT`（`tower_of_blockSteps_C11W` 同证明，
   W0 换成"共尾 + `accuracyCap ≤ 1/8646`"的版本 `budgetChoice_cofinal_capped_C11GT`）取 `T`；
3. `T.toChain.exists_surgery_with_retained_raw_caps`（`SH/PreparedSpatialRawCapsPortC11P`）在
   `S := T.toChain`、`W := choice retention`、`a₀`（`exists_initialControl_C11GT`）上给出同一个
   `(F, q, κ, records)` 的 W1 十项、m-i / block 子句与对角等式；
4. 逐项供给（见下表），喂 `a12EnhancedFull_of_chain_C12X`。

## 按 hext 顺序（`A12FullConsumerC12X` 的 `hext`）：已供给 / 缺口
记号：【供】= 本定理里已由树内定理供给（无 binder）；【缺】= 对应的显式 binder。
* hP3 / hprof（`pBase`）：【供】hprof 全部与半径条（`HasReserveQuality` +
  `pBase_bounds_of_reserve_C11W6`）；【缺】`hpbase` 里的 collar 合取项。
* `F.tower = S.tower`、`ε = C.epsilon`、`q` 的四个参数等式：【供】raw_caps 的合取项；`rfl`。
* CanonicalConstants、`κ > 0`、`κ` antitone、`δ / ρ` antitone、HistoryCanonical、noncollapsed、
  `δ → 0`、Recent：【供】`canonicalConstantsSupply_of_closedBirthConstants_C11A` + raw_caps 同名合取项。
* S8 `LargerBallScalarLargeSupply_C11S`：【供】`s8_of_smallVol_C11V4`，GAP-2 的 `ε₀` 由 `εReserve`
  供；【缺】`hK`（GAP-3 κ 线）、`hspine`（P6 (c)）、`hP6b`、`hlinkS10`。
* S10 `LinkedWindowsSupply_C11E`：【缺】`hlinkS10`。
* S11 `TimeDerivativeSupply_C11E`：【供】`timeDerivativeSupply_of_astra_C12X`（W / hshift / hoffset
  取自 tower）。
* S14 `LateLinkedRecordsSupply_C11E`：【供】`lateLinkedRecordsSupply_of_outer_C12X`，`hcof` 由
  共尾 budget + `tower_fine_request_eventually_C11W4` 供（不需要 HCOF patch）；【缺】`hfine`。
* S15 `LargerBallCanonicalLateSupply_C11E`（P6 (b)）：【缺】`hP6b`。`s15_of_s8_C11S15` 的 `hband`
  要 S8，而 S8 接线 `s8_of_smallVol_C11V4` 要 (b)：成环，所以顶层以 (b) 本身为 binder。
* S16 `StrongCanonicalSupplyV2_C11E`：【供】`strongCanonicalSupplyV2_of_towerFull_C12X`；【缺】`hfull`。
* S17 `CompatibleCapsSupply_C11E`：【供】`compatibleCapsSupply_of_eventDelta_C12X` +
  `eventDelta_of_accuracy_C12X`，`δ₀ = 1/8646` 由 budget cap 供。
* S19 `FrontierCollarSupplyFull_C11F`：【供】`frontierCollarSupplyFull_C12X`。

## binder 形说明
* 每个 chain 层缺口都是 **∀-闭合**（与 `a12_of_astra_byPoint_window_C11W7` 的 `hK / hclosure` 同口径）：
  对任意 `pB Γ`、`S : PreparedSpatialChain pB Γ P g`、`F q`（`F.tower = S.tower`、`q.delta / neckRadius`
  是 `S` 的对角）成立；`pB` 的小性前提 `pB.modelAccuracy ≤ εK Γ`、`capWindowRadius_C11E + 1 ≤
  pB.modelRadius`、`2 ≤ pB.modelOrder` 作前提（`εK` 是 κ 线生产者要的阈值，调用者自由取）。
* `hpbase`：不能 ∀ 闭合——`collarAdmitsAllOrders_C11E A` 对 `A` 有真条件，而 `pB.fixed` 在 astra provider
  的 `∃` 下（≈ 13 层，`out/CH12X-PBASE-GAP.md`）。所以 `hpbase` = W6 `exists_blockSteps_byPoint_C11W6`
  在 `(P, g)` 处的陈述 + 对**同一个 `pB`** 的 collar 合取项；S-CH11-PBASE 路线 A 落树后把 collar 穿进
  W6 provider 即可用定理替换（W6 本体已证）。
* `hP6b` 的 (b) 合同形（lead 07:5x，R-C11-5 D-16）：最终形将是 `CanonicalLateCore`（P6SEL 定义）；
  这里按现有 `LargerBallCanonicalLateSupply_C11E` 形占位，P6SEL 落地后只换这一个 binder 的类型。
  `hspine` 以 (b) 为输入（D-16 确认的口径）。
* `hspine` 的 `A` 是严格 `1 < A`（`s8_of_smallVol_C11V4` 的 spine 形）；要求严格 `1 < A` 的消费者
  对 `A ≤ 1` 取 `max A 2`（D-14），不要取 `max A 1` 再交严格不等式——本文件不做这种取整。
* `hlinkS10`：`records` 以 HEq 绑到 `S.observation` 的 records（`records` 是 raw_caps 的输出）。
* `hfine`：∀ retention 族（S10HORN 给 retention 加 `fineLinked` 字段后是定理）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- W0 的共尾 + 精度上界加强（`budgetChoice_cofinal_C11W4` 再加 `accuracyCap ≤ δ₀`）。 -/
theorem budgetChoice_cofinal_capped_C11GT (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (δ₀ : ℝ)
    (hδ₀ : 0 < δ₀) (j : ℕ) :
    ∀ X : BlockState_C11W pBase C P g j, Inv_C11W Cdist cMax Dstar εReserve X →
      ∀ ℓ : BlockLookahead_C11W X, LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ →
        ∃ req : BlockRequest_C11W, RequestReady_C11W X req ∧ RequestCofinal_C11W4 j req ∧
          req.accuracyCap ≤ δ₀ := by
  intro X _ _ _
  have hδ : 0 < X.parameters.delta (preparedSpatialHorizon j) :=
    X.parameters.delta_pos _ (blockActivation_mem_C11W j).1
  have hj2 : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
  refine ⟨BlockRequest_C11W.cofinal j
    (min (min (1 / ((j : ℝ) + 2)) (X.parameters.delta (preparedSpatialHorizon j) / 4)) δ₀),
    ?_, requestCofinal_cofinal_C11W4 _ _, min_le_right _ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hj2 (by positivity)) hδ₀
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact hj2
  · change 0 < (j : ℝ) + 1
    positivity

/-- `tower_of_blockSteps_C11W` 的同证明，W0 换成带谓词 `Q j req` 的版本；多交
`∀ j, Q j (T.request j)`。 -/
theorem tower_of_blockSteps_pred_C11GT {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (Q : ℕ → BlockRequest_C11W → Prop)
    (hW0 : ∀ j, ∀ X : BlockState_C11W pBase C P g j, Inv_C11W Cdist cMax Dstar εReserve X →
      ∀ ℓ : BlockLookahead_C11W X, LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ →
        ∃ req : BlockRequest_C11W, RequestReady_C11W X req ∧ Q j req)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      T.block 0 = X₀ ∧ ∀ j, Q j (T.request j) := by
  classical
  let Certified (n : ℕ) :=
    {X : BlockState_C11W pBase C P g n // Inv_C11W Cdist cMax Dstar εReserve X}
  let look (n : ℕ) (X : Certified n) : BlockLookahead_C11W X.1 :=
    Classical.choose (hstep n X.1 X.2)
  have look_spec (n : ℕ) (X : Certified n) :=
    Classical.choose_spec (hstep n X.1 X.2)
  let req (n : ℕ) (X : Certified n) : BlockRequest_C11W :=
    Classical.choose (hW0 n X.1 X.2 (look n X) (look_spec n X).1)
  have req_spec (n : ℕ) (X : Certified n) :
      RequestReady_C11W X.1 (req n X) ∧ Q n (req n X) :=
    Classical.choose_spec (hW0 n X.1 X.2 (look n X) (look_spec n X).1)
  have ext (n : ℕ) (X : Certified n) := (look_spec n X).2 (req n X) (req_spec n X).1
  let next (n : ℕ) (X : Certified n) : Certified (n + 1) :=
    ⟨Classical.choose (ext n X), (Classical.choose_spec (Classical.choose_spec (ext n X))).2⟩
  let acc (n : ℕ) (X : Certified n) : ℝ := Classical.choose (Classical.choose_spec (ext n X))
  have next_spec (n : ℕ) (X : Certified n) :
      PhysicalExtension_C11W X.1 (next n X).1 (look n X) (req n X) (acc n X) :=
    (Classical.choose_spec (Classical.choose_spec (ext n X))).1
  let chain : ∀ n : ℕ, Certified n := fun n => Nat.rec ⟨X₀, hX₀⟩ (fun n X => next n X) n
  exact ⟨{ block := fun n => (chain n).1
           lookahead := fun n => look n (chain n)
           request := fun n => req n (chain n)
           accuracy := fun n => acc n (chain n)
           inv := fun n => (chain n).2
           ready := fun n => ⟨(look_spec n (chain n)).1, (req_spec n (chain n)).1⟩
           extension := fun n => next_spec n (chain n)
           initial_history := hhist
           initial_radius_le := hrad }, rfl, fun n => (req_spec n (chain n)).2⟩


/-- 取一个 `a₀`（fixed Hamilton–Ivey 初值控制）：取 astra 公开存在定理的前缀，与 `Dstar`、
`pBase` 无关。 -/
theorem exists_initialControl_C11GT (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a₀ : ℝ, ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x := by
  obtain ⟨_εcap, _cBG, -, -, _Cdist, -, _constants, makeInitial⟩ :=
    exists_surgery_with_physical_requests_and_test_volume_or_reserve_at_closed_poles.{u}
      (StandardCap.transitionEnd + 1) (by linarith)
  obtain ⟨a₀, -, hctrl, -⟩ := makeInitial P g
  exact ⟨a₀, hctrl⟩

/-- **A12′ v2 的顶层缺口定理**：binder 列表 `hpbase hK hspine hP6b hlinkS10 hfine hfull`
（+ 自由阈值 `εK hεK`）就是 A12′ 目前还差的全部；每条的含义、归属见模块 docstring 与
`docs/geometrization/chapter8/out/A12-GAP-TOP-20261007.md`。
证明 = W6 tower + `exists_surgery_with_retained_raw_caps` 逐项调用生产者，再喂
`a12EnhancedFull_of_chain_C12X`。 -/
theorem a12EnhancedFull_of_gaps_C11GT (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εK : ClosedBirthConstants → ℝ) (hεK : ∀ Γ, 0 < εK Γ)
    (hpbase : ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), ∀ εReserve : ℝ, 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j)
    (hK : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εK Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
    (hspine : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εK Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A → (∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (max Γ.C1s Γ.Cbirth)
          (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εK Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      LargerBallCanonicalLateSupply_C11E F Γ.epsilon (max Γ.C1s Γ.Cbirth)
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))))
    (hlinkS10 : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : CutoffRecords_C11S F q), F.tower = S.tower →
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).static ((S.observation n).records j).static) →
      LinkedWindowsSupply_C11E records)
    (hfine : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
      (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
        (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)),
      ∀ k (i : Fin (S.state (k + 1)).native.eventCount) b,
        (((W k).fineRecords i).static b).hasLinkedCanonicalWindow_C12X)
    (hfull : ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εK Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
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
  obtain ⟨ε₀, hε₀, hS8wire⟩ := s8_of_smallVol_C11V4.{u} Γ.epsilon (max Γ.C1s Γ.Cbirth)
    (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) P
  have hεR : 0 < min εProf_C11E.{u} (min (εK Γ) ε₀) :=
    lt_min εProf_pos_C11E (lt_min (hεK Γ) hε₀)
  obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR
  obtain ⟨hacc, hradB, hordB⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  have haccProf : pB.modelAccuracy ≤ εProf_C11E.{u} := hacc.trans (min_le_left _ _)
  have haccK : pB.modelAccuracy ≤ εK Γ := hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hacc₀ : pB.modelAccuracy ≤ ε₀ := hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP3 : CollarWindowSupply_C11E.{u} pB := ⟨hcollar, hradB⟩
  have hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u} := by
    refine ⟨haccProf, hordB, ?_⟩
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E at hradB
    linarith
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ := exists_inv_base_C11W Cdist 1 (capWindowRadius_C11E + 1) _
    one_pos prepared hbase hdist hres
  obtain ⟨T, -, hQ⟩ := tower_of_blockSteps_pred_C11GT
    (fun j req => RequestCofinal_C11W4 j req ∧ req.accuracyCap ≤ 1 / 8646)
    (fun j X hX ℓ hℓ => by
      obtain ⟨req, h1, h2, h3⟩ := budgetChoice_cofinal_capped_C11GT Cdist 1
        (capWindowRadius_C11E + 1) _ (1 / 8646) (by norm_num) j X hX ℓ hℓ
      exact ⟨req, h1, h2, h3⟩) hstep X₀ hX₀ hhist hrad₀
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
    hlinkS10 T.toChain F q records hTower (fun n i j hij => (hrecHEq n i j hij).2.2.2.2)
  have hP6 := hP6b T.toChain F q hTower hdiag haccK hradB hordB
  have hS8 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) :=
    hS8wire hP3 hprof hradq hordq haccq hacc₀ records hlinkS hδanti hρanti hcan
      (hK T.toChain F q hTower hdiag haccK hradB hordB) hP6
      (fun A hA hw hb => hspine T.toChain F q hTower hdiag haccK hradB hordB A hA hw hb)
  have hTD := timeDerivativeSupply_of_astra_C12X T.toChain _ _ _ W hshift hoffset F hTower q
    hρanti (diagonal_neckRadius_of_prefix_C12X T.toChain q (fun n t ht => (hpref n t ht).2.1))
  have hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder := by
    intro D ζ m hζ
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
      (tower_fine_request_eventually_C11W4 T (fun j => (hQ j).1) hζ D m)
    refine ⟨k₀, fun k hk => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hk₀ k hk (W k)
    exact ⟨h2, h1, h3⟩
  have hlate := lateLinkedRecordsSupply_of_outer_C12X T.toChain W F q records hfixed hrc hmi hRaw
    hcof (lateLinkedHlink_of_fineLinked_C12X T.toChain W (hfine T.toChain W))
  have hStrong := strongCanonicalSupplyV2_of_towerFull_C12X
    (hfull T.toChain F q hTower hdiag haccK hradB hordB)
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨T.toChain, F, q, κ, records, Γ.epsilon,
    max Γ.C1s Γ.Cbirth, max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)), hTower, rfl,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ, hκanti, hδanti, hρanti, hcan, hnc, hδlim,
    hrecent, hS8, hlinkS, hTD, hlate, hP6, hStrong, hS17,
    frontierCollarSupplyFull_C12X F q⟩

/-- consumer：顶层定理的结论（A12′ v2）⇒ 晚期共同 neck accuracy 与 A12 的 `hasCommonNeckAccuracy`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-- consumer：顶层定理的签名稳定（binder 列表即 `type_of%`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_of_gaps_C11GT P g) := a12EnhancedFull_of_gaps_C11GT P g

end GC.LongTime.Ch11

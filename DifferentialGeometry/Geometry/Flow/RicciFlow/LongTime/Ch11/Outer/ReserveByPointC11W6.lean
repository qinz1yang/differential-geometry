import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.A12OfAstraBlockStepsC11W5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HICompareC11V3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

set_option autoImplicit false

/-!
# O-CH11-OUTER (G6)：按点选 `εReserve`（GAP-2，`_C11W6`）

SMALLVOL3 的 `localKappaWindow_zero_of_narrowTuple_records_C11V3` 要 `q.modelAccuracy ≤ ε₀`，
`ε₀ = ε₀(D, ε, C1, C2, N)`：`ε C1 C2` 来自统一常数 `C`，`N = N(P)`。`Providers:25` 与
`exists_blockSteps_of_astra_C11W5` 把 `εReserve` 放在 `∃ C` 之前，于是 `εReserve` 不能依赖
`C` 或 `N(P)`。本文件把次序改成 `∃ Cdist C, ∀ P g, ∀ εReserve > 0, ∃ pBase …`：

* 在 `εReserve₀ = 1` 处实例化 `exists_prepared_spatial_initial_state_with_distance_scalars_with_
  reserve_quality`（Providers:25），只取 `Cdist fixed recenter C prepareClass analytic`（证明体里它们
  与 `εReserve` 无关；陈述上也只用这些分量）；
* 对每个 `(P, g, εReserve)` 直接调 PCBC
  `exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality`，
  照 Providers:25 的 record 字面量重组 capacity 1 的 class；
* `blockSteps_of_astra_C11W5` 给每块 `BlockStep_C11W`。

`pBase.modelAccuracy ≤ εReserve`、`Dstar ≤ pBase.modelRadius`、`2 ≤ pBase.modelOrder` 都由同一个
`pBase`（= class 参数）给出。消费者取 `εReserve := min εProf_C11E (ε₀ C (N P))`。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **GAP-2 producer**：统一 `Cdist`、`C` 先于 `P g`；`εReserve` 在 `P g` 之后任意选。 -/
theorem exists_blockSteps_byPoint_C11W6 (Dstar : ℝ) (hDstar : 0 < Dstar) (cMax : ℝ)
    (hcMax : 0 < cMax) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.εStrong_C12X.{u} ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (εReserve : ℝ), 0 < εReserve →
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, -, prepareClass, analytic, -⟩ :=
    exists_closedBirthConstants_strong_C12X.{u} Dstar 1 hDstar one_pos
  refine ⟨Cdist, hCdist, C, hεs, fun P g εReserve hεReserve => ?_⟩
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality
      Dstar εReserve hDstar hεReserve Cdist fixed recenter prepareClass
      C.epsilon C.C1 C.C2 C.C1s C.C2s C.Cs C.tauMin C.Cbirth C.Ctime C.Cgrad C.epsilon_pos
      ⟨C.C1_ge_one, C.C2_ge_one, C.C1s_ge_one, C.C2s_ge_one, C.tauMin_pos, hεs⟩ analytic P g
  obtain ⟨pBase, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall,
    hDReserve, hεReserveBound, hmReserve, hscaleReserve, hStrong,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, hQall, hQallPos,
    hcap, hrec, extension, control⟩ := prepareInitial 1 one_pos
  obtain ⟨C1h, C2h, qh, hC1h, hC2h, hC1hb, hC2hb, hqh, hStrongV⟩ := hStrong
  let prepared : ClosedBirthPreparedClass pBase C P g 1 := {
    parameters := pBase
    deltaBound := δb
    radiusBound := ρb
    epsilonClass := εClass
    kappaClass := κClass
    kappa := κ
    qcan := qcan
    qs := qs
    Qzero := Qzero
    Qbirth := Qbirth
    Qall := Qall
    fixed_eq := rfl
    recenter_eq := rfl
    deltaBound_pos := hδb
    radiusBound_pos := hρb
    epsilonClass_pos := hεClass
    epsilonClass_small := hεClass11
    kappaClass_pos := hκClass
    kappa_pos := hκ
    qcan_pos := hqcan
    qcan_le_qs := hqs
    qs_le := hqsC
    Qzero_pos := hQzero
    Qbirth_ge := hQbirth
    Qall_eq := hQall
    Qall_pos := hQallPos
    modelRadius_bound := hcap
    recenter_bound := hrec
    zero_bound := zeroBound
    extension := extension.forget
    control := control
    epsilon_strong := hεs
    C1strong := C1h
    C2strong := C2h
    qStrong := qh
    C1strong_ge_one := hC1h
    C2strong_ge_one := hC2h
    C1strong_le := hC1hb
    C2strong_le := hC2hb
    qs_le_qStrong := hqh
    strongControl := hStrongV }
  have hprep : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist := by
    rw [hfixed, hrc]
    exact prepareClass
  exact ⟨pBase, prepared, rfl, extension,
    ⟨hDReserve, hεReserveBound, hmReserve, hscaleReserve⟩,
    blockSteps_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax hprep analytic⟩

/-- 读出：同一个 `pBase` 给 accuracy / radius / order 三个界。 -/
theorem pBase_bounds_of_reserve_C11W6 {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {prepared : ClosedBirthPreparedClass pBase C P g 1}
    {Dstar εReserve : ℝ} (hbase : prepared.parameters = pBase)
    (hres : prepared.HasReserveQuality Dstar εReserve) :
    pBase.modelAccuracy ≤ εReserve ∧ Dstar ≤ pBase.modelRadius ∧ 2 ≤ pBase.modelOrder := by
  obtain ⟨hD, hε, hm, -⟩ := hres
  rw [hbase] at hD hε hm
  exact ⟨hε, hD, hm⟩

/-- **A12（按点 εReserve 形）**：`εReq : ClosedBirthConstants → ℝ` 在 `C` 之后求值；S8 只需对
满足 `pBase` 三个界（accuracy ≤ `εReq C`、radius ≥ `Dstar`、order ≥ 2）的 produced tower 成立。 -/
theorem a12_of_astra_byPoint_C11W6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dstar : ℝ) (hDstar : 0 < Dstar) (cMax : ℝ) (hcMax : 0 < cMax)
    (εReq : ClosedBirthConstants → ℝ) (hεReq : ∀ C, 0 < εReq C)
    (hS8 : ∀ (Cdist : ℝ≥0) (C : ClosedBirthConstants) (pBase : CutoffParameters)
      (X₀ : BlockState_C11W pBase C P g 0),
      pBase.modelAccuracy ≤ εReq C → Dstar ≤ pBase.modelRadius → 2 ≤ pBase.modelOrder →
      Inv_C11W Cdist cMax Dstar (εReq C) X₀ → X₀.history = RetainedCoreHistory.atZero P g →
      X₀.radius ≤ 1 →
      ∀ T : BlockTower_C11W pBase C P g Cdist cMax Dstar (εReq C), T.block 0 = X₀ →
        ∀ F : GC.Interface.RawSurgery P g, F.tower = T.toChain.tower →
          LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A T.toChain).delta
            (diagonalAccuracy_C11S (chainDiagonal_C11A T.toChain).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) := by
  obtain ⟨Cdist, -, C, -, hmake⟩ := exists_blockSteps_byPoint_C11W6.{u} Dstar hDstar cMax hcMax
  obtain ⟨pBase, prepared, hbase, hdist, hres, hstep⟩ := hmake P g (εReq C) (hεReq C)
  obtain ⟨hacc, hrad, hord⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ :=
    exists_inv_base_C11W Cdist cMax Dstar (εReq C) hcMax prepared hbase hdist hres
  exact a12_of_blockSteps_C11W P g pBase C Cdist cMax Dstar (εReq C) X₀ hX₀ hhist hrad₀ hstep
    (hS8 Cdist C pBase X₀ hacc hrad hord hX₀ hhist hrad₀)

/-- consumer（GAP-2 实例）：`N = N(P)` 取自 `general_uniform_history_degree P g`；`ε₀ C` 取自
SMALLVOL3 `localKappaWindow_zero_of_narrowTuple_records_C11V3`（`ε C1 C2` = `C` 的 canonical
常数，与 `w1_of_preparedSpatialChain_C11A` 同）；`εReq C := min εProf_C11E (ε₀ C)`。produced
`pBase` 同时满足 `modelAccuracy ≤ ε₀ C` 与 `≤ εProf_C11E`。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (Dstar : ℝ) (hDstar : 0 < Dstar)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ Dstar) (cMax : ℝ) (hcMax : 0 < cMax) :
    ∃ (N : ℕ) (ε₀ : ClosedBirthConstants → ℝ), 0 < N ∧ (∀ C, 0 < ε₀ C) ∧
    ∃ Cdist : ℝ≥0, ∃ C : ClosedBirthConstants,
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧
      pBase.modelAccuracy ≤ ε₀ C ∧ pBase.modelAccuracy ≤ εProf_C11E.{u} ∧
      Dstar ≤ pBase.modelRadius ∧ 2 ≤ pBase.modelOrder ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar (min εProf_C11E.{u} (ε₀ C)) j := by
  obtain ⟨N, hN, -⟩ := general_uniform_history_degree P g
  let ε₀ : ClosedBirthConstants → ℝ := fun C =>
    Classical.choose (localKappaWindow_zero_of_narrowTuple_records_C11V3.{u} Dstar hD C.epsilon
      (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) N hN)
  have hε₀ : ∀ C, 0 < ε₀ C := fun C =>
    (Classical.choose_spec (localKappaWindow_zero_of_narrowTuple_records_C11V3.{u} Dstar hD
      C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) N hN)).1
  obtain ⟨Cdist, -, C, -, hmake⟩ := exists_blockSteps_byPoint_C11W6.{u} Dstar hDstar cMax hcMax
  obtain ⟨pBase, prepared, hbase, -, hres, hstep⟩ :=
    hmake P g (min εProf_C11E.{u} (ε₀ C)) (lt_min εProf_pos_C11E (hε₀ C))
  obtain ⟨hacc, hrad, hord⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  exact ⟨N, ε₀, hN, hε₀, Cdist, C, pBase, prepared, hbase, hacc.trans (min_le_right _ _),
    hacc.trans (min_le_left _ _), hrad, hord, hstep⟩

end GC.LongTime.Ch11

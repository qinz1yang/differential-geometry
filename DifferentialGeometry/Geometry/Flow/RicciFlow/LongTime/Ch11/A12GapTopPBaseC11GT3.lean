import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV2C11GT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.PBaseCollarC11PB

set_option autoImplicit false

/-!
# S-CH11-GAPTOP3 G1：顶层 `hpbase` 由 PBASE 的 strong provider 产出（后缀 `_C11GT3`）

`a12EnhancedFull_of_gaps_v2_C11GT2` 的 `hpbase` binder 是 W6 `exists_blockSteps_byPoint_C11W6` 的结论
（取 `cMax = 1`、`Dstar = capWindowRadius_C11E + 1`）加一条 collar 合取项
`collarAdmitsAllOrders_C11E pB.fixed.collarLength pB.fixed.collar_pos`。树内的
`exists_blockSteps_byPoint_C11W6` 把 strong provider
（`exists_closedBirthConstants_strong_C12X`，PBASE G1/G3 落树后）的 collar 槽
`∃ A hA, fixed = ofCollarLength A hA ∧ StaticCollarAdmits A hA` 在解构时丢掉了，
所以 collar 条出不来。本文件（**不改 tracked**）：

* `exists_blockSteps_byPointCollar_C11GT3`：`exists_blockSteps_byPoint_C11W6` 的 collar 保留版（证明体逐行同
  W6，只是不丢 strong provider 的 collar 槽；`pBase.fixed = fixed` 来自 `prepareInitial` 的 `hfixed`，
  collar 条沿 PBASE 的 `collarAdmitsAllOrders_of_staticCollarAdmits_C11PB` 与
  `collarAdmitsAllOrders_of_fixed_ofCollarLength_C11PB` 转成 `collarAdmitsAllOrders_C11E.{u}`），同时多
  导出 `C.epsilon ≤ εStrong_C12X`（v3 的 G4 / S16 以后用）；
* `hpbase_strong_C11GT3`：`hpbase` 逐字形，`∃ Γ` 之后多一条 `Γ.epsilon ≤ εStrong_C12X.{u}`；
* `hpbase_of_provider_C11GT3`：**`hpbase` 逐字形**（丢掉多出的合取项），对**所有** `P g` 无前提成立。

与 GAPTOP2 的 `hpbase` 无 drift：binder 类型逐字相同，不需要 adapter 层（见文末 consumer：直接喂 v2）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **W6 producer 的 collar 保留版**：统一 `Cdist`、`C` 先于 `P g`；`εReserve` 在 `P g` 之后任意选；
结论比 `exists_blockSteps_byPoint_C11W6` 多 `collarAdmitsAllOrders_C11E pBase.fixed.collarLength
pBase.fixed.collar_pos`（同一个 `pBase`）。 -/
theorem exists_blockSteps_byPointCollar_C11GT3 (Dstar : ℝ) (hDstar : 0 < Dstar) (cMax : ℝ)
    (hcMax : 0 < cMax) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ εStrong_C12X.{u} ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (εReserve : ℝ), 0 < εReserve →
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength pBase.fixed.collar_pos ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, ⟨-, A, hA, hfix, hcol⟩, prepareClass, analytic,
      -⟩ := exists_closedBirthConstants_strong_C12X.{u} Dstar 1 hDstar one_pos
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
  have hcollar : collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength
      pBase.fixed.collar_pos := by
    subst hfixed
    exact collarAdmitsAllOrders_of_fixed_ofCollarLength_C11PB
      ⟨A, hA, hfix, collarAdmitsAllOrders_of_staticCollarAdmits_C11PB hcol⟩
  exact ⟨pBase, prepared, rfl, extension,
    ⟨hDReserve, hεReserveBound, hmReserve, hscaleReserve⟩, hcollar,
    blockSteps_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax hprep analytic⟩

/-- **`hpbase`，strong 形**：v2 `hpbase` binder 的逐字形，`∃ Γ` 之后多一条 `Γ.epsilon ≤ εStrong_C12X`。 -/
theorem hpbase_strong_C11GT3 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), Γ.epsilon ≤ εStrong_C12X.{u} ∧
      ∀ εReserve : ℝ, 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j := by
  have hD : 0 < capWindowRadius_C11E + 1 := by
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    positivity
  obtain ⟨Cdist, -, C, hεs, hmake⟩ :=
    exists_blockSteps_byPointCollar_C11GT3.{u} (capWindowRadius_C11E + 1) hD 1 one_pos
  exact ⟨Cdist, C, hεs, fun ε hε => hmake P g ε hε⟩

/-- **G1 主定理：`hpbase` 逐字形**（`a12EnhancedFull_of_gaps_v2_C11GT2` 的第一个 binder 的类型），对所有
`P g` 无前提成立；collar 条由 PBASE 的 strong provider 槽给出，不再是显式假设。 -/
theorem hpbase_of_provider_C11GT3 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), ∀ εReserve : ℝ, 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j := by
  obtain ⟨Cdist, Γ, -, h⟩ := hpbase_strong_C11GT3.{u} P g
  exact ⟨Cdist, Γ, h⟩

/-- consumer：`hpbase_of_provider_C11GT3` 直接是 v2 顶层定理的第一个 binder（类型逐字，无 adapter）；
喂入后剩下 `hK hspine hP6b hlinkfine hfull` 五个 binder。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :=
  a12EnhancedFull_of_gaps_v2_C11GT2 P g (hpbase_of_provider_C11GT3 P g)

end GC.LongTime.Ch11

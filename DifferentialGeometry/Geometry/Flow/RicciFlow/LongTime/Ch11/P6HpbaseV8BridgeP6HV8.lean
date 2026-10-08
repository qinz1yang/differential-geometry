import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpbaseV8P6HV8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpbaseRequestC12P

set_option autoImplicit false

/-!
# 两种 v8 provider 形的桥接：`_P6HV8`（HPBASE-V8 G1）⟷ `_C12P`（C12-3 G1，root #113）（后缀 `_P6HV8`）

对照（详表见 `build-logs/resume/state-O-CH11-HPBASE-V8.md`）：
* `hpbaseTwoLevel_v8_P6HV8 P g`（陈述内联）= 冻结 `HpbaseTwoLevel_C11G2 epsW_CXOU2 P g`
  + `∀ (Rmod : ℝ) (mmod : ℕ)` + PB 合取 `(Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder)`，
  reserve / tower 半径固定 `capWindowRadius_C11E + 1`。
* `HpbaseTwoLevel_v8_C11G2 εW Dstar P g`（C12P 合同 def，`Dstar` 参数）：同一量词序 `∃ Cdist Γ Γf … ∀ Rmod mmod
  εReserve ∃ pB`，请求界写成两个平铺合取 `Rmod ≤ … ∧ mmod ≤ … ∧ collar ∧ …`。
* 在 `Dstar := capWindowRadius_C11E + 1` 处两者**等价**（本文件两向桥，纯合取重组）。C12P 另对任意 `Dstar > 0`
  成立（`hpbaseTwoLevel_v8_C11G2 P g Dstar`），故 C12P 合同族 ⊇ 本车道陈述；producer 层 C12P
  `exists_blockSteps_request_C12P` 是 `∃ C ∀ Dstar`，本车道 `exists_blockSteps_v8_P6HV8` 是 `∀ Dstar ∃ C`
  ⇒ C12P 更强。
* 请求对 `Γf` 的依赖：两个 provider 都是 `∃ Γ Γf` 在 `∀ Rmod mmod` 之前，故都可接 `Rn Γf / mn Γf`；差别只在
  consumer 槽（C12P CC′ 用 `Rn mn : ClosedBirthConstants → _`；PB 定理 / NRPRIME / 本车道 G2 用固定
  `(Rmod, mmod)`）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **P6HV8 ⇒ C12P（泛型 `εW`）**：`hpbaseTwoLevel_v8_eps_P6HV8` 的输出即 C12P 合同在冻结半径处
（合取重组）。 -/
theorem hpbaseTwoLevel_v8_C12P_of_eps_P6HV8 (P : OrientedThreeStage.{u}) (g : P.Metric) (εW : ℝ)
    (hεW : 0 < εW) : HpbaseTwoLevel_v8_C11G2.{u} εW (capWindowRadius_C11E + 1) P g := by
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ :=
    hpbaseTwoLevel_v8_eps_P6HV8.{u} P g εW hεW
  refine ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, fun Rmod mmod εReserve hε => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, ⟨hR, hm⟩, hcollar, hstep⟩ := hmake Rmod mmod εReserve hε
  exact ⟨pB, prepared, hbase, hdist, hres, hR, hm, hcollar, hstep⟩

/-- **P6HV8 ⇒ C12P（闭合）**：与 `hpbaseTwoLevel_v8_cap_C12P` 同类型，另一条独立证明。 -/
theorem hpbaseTwoLevel_v8_C12P_of_P6HV8 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_v8_C11G2.{u} epsW_CXOU2.{u} (capWindowRadius_C11E + 1) P g :=
  hpbaseTwoLevel_v8_C12P_of_eps_P6HV8 P g epsW_CXOU2.{u} epsW_CXOU2_pos.{u}

/-- **C12P ⇒ P6HV8**：C12P 合同在冻结半径处给出本车道 G1 的陈述（合取重组；`εW` 泛型）。 -/
theorem hpbaseV8_P6HV8_of_C12P {εW : ℝ} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (h : HpbaseTwoLevel_v8_C11G2.{u} εW (capWindowRadius_C11E + 1) P g) :
    ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
      Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ εW ∧
      Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ εW ∧
      ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        (Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder) ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j := by
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ := h
  refine ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, fun Rmod mmod εReserve hε => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, hR, hm, hcollar, hstep⟩ := hmake Rmod mmod εReserve hε
  exact ⟨pB, prepared, hbase, hdist, hres, ⟨hR, hm⟩, hcollar, hstep⟩

/-- consumer：C12P 的闭合 provider 经桥给出 `hpbaseTwoLevel_v8_P6HV8` 的**同一类型**
（G2 引擎 :99 可任取一方）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (hpbaseTwoLevel_v8_P6HV8.{u} P g) :=
  hpbaseV8_P6HV8_of_C12P (hpbaseTwoLevel_v8_cap_C12P P g)

/-- consumer：本车道 provider 经桥给出 C12P `hmake_request_C12P` 所消费的合同类型（冻结半径）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_v8_C11G2.{u} epsW_CXOU2.{u} (capWindowRadius_C11E + 1) P g :=
  hpbaseTwoLevel_v8_C12P_of_P6HV8 P g

/-- consumer：两向桥复合回到冻结 `HpbaseTwoLevel_C11G2`（经 C12P 的迁移引理）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_C11G2.{u} epsW_CXOU2.{u} P g :=
  hpbaseTwoLevel_of_v8_C12P (hpbaseTwoLevel_v8_C12P_of_P6HV8 P g)

end GC.LongTime.Ch11

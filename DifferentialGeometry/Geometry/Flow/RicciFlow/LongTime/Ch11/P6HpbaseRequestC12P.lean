import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.PreparedClosedBirthOrderC12P

/-!
# NR′ request-driven provider：`HpbaseTwoLevel_v8_C11G2` + producer（车道 C12-3，后缀 `_C12P`）

D-20-9 / skeleton v8 §6.3 的 C12-3 改写：在构造同一个 `pB / prepared / tower` 之前允许请求下游需要的
`(Rmod, mmod)`，并**证明**该 provider。
* 量词序 = `∃ Cdist Γ Γf, … ∧ ∀ Rmod mmod εReserve, ∃ pB prepared, …`：请求在 `(Γ, Γf)` 之后、在
  `pB` 之前（下游 NR 的 `(R, m₀)` 可依赖 `Γf`，例如经 Dt 常数 `C`）。这是 `∃Γ ∀m` 形，**没有**换成
  `∀m ∃Γ`：原因是 CXCA 的 `C`（`exists_closedBirthConstants_strong_accuracy_CXCA`）的选取只用
  `εbar / 1/200 / coneAccuracy / εStrong / εcap`，`Dstar / εReserve` 只进入最后一个合取（CXOU2 证明里
  用 `-` 丢弃）；故此处用 `Dstar = εReserve = 1` 取 `C`，再对每个请求调用
  `exists_prepared_class_distance_order_C12P`（PreparedClosedBirthClass 的 `∀ mmod` 孪生）。
* `exists_blockSteps_request_C12P`：`exists_blockSteps_byPointCollarAcc_CXOU2` 的孪生——`∃ C` 之后
  `∀ P g Dstar Rmod mmod εReserve`，多 `Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder`。
* `HpbaseTwoLevel_v8_C11G2 εW Dstar`（合同 def，`Dstar` 参数化；冻结 `HpbaseTwoLevel_C11G2` 不动）+
  producer `hpbaseTwoLevel_v8_C11G2`（∀ `Dstar > 0`，PROVED）。
* 迁移：`hpbaseTwoLevel_of_v8_C12P`（v8 在 `Dstar = capWindowRadius + 1` ⇒ 冻结形，同一 `pB`）；
  `hmake_request_C12P`：同一 `pB` 同时给 A12′ `hmake` 的冻结合取、hSL1 / CC 的调用约束
  （`acc ≤ εReserve`、`cap + 1 ≤ radius`、`2 ≤ order`）与 NR 的请求界。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **request-driven provider（producer 层）**：`C` 先于 `P g Dstar Rmod mmod εReserve`；对每个请求，
同一个 `pBase` 给 reserve quality（`Dstar`）、请求界 `Rmod ≤ radius`、`mmod ≤ order`、collar 与
全部 `BlockStep`。 -/
theorem exists_blockSteps_request_C12P (cMax : ℝ) (hcMax : 0 < cMax) (εcap : ℝ)
    (hεcap : 0 < εcap) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ εStrong_C12X.{u} ∧ C.epsilon ≤ εcap ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (Dstar : ℝ), 0 < Dstar →
    ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder ∧
      collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength pBase.fixed.collar_pos ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεcap', hεs, ⟨-, A, hA, hfix, hcol⟩, prepareClass,
      analytic, -⟩ := exists_closedBirthConstants_strong_accuracy_CXCA.{u} 1 1 εcap one_pos
      one_pos hεcap
  refine ⟨Cdist, hCdist, C, hεs, hεcap', fun P g Dstar hDstar Rmod mmod εReserve hεReserve => ?_⟩
  have hD' : 0 < max Dstar Rmod := hDstar.trans_le (le_max_left _ _)
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_class_distance_order_C12P
      (max Dstar Rmod) εReserve mmod hD' hεReserve Cdist fixed recenter prepareClass
      C.epsilon C.C1 C.C2 C.C1s C.C2s C.Cs C.tauMin C.Cbirth C.Ctime C.Cgrad C.epsilon_pos
      ⟨C.C1_ge_one, C.C2_ge_one, C.C1s_ge_one, C.C2s_ge_one, C.tauMin_pos, hεs⟩ analytic P g
  obtain ⟨pBase, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall,
    hDReserve, hεReserveBound, hmReserve, hmReq, hscaleReserve, hStrong,
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
    ⟨(le_max_left _ _).trans hDReserve, hεReserveBound, hmReserve, hscaleReserve⟩,
    (le_max_right _ _).trans hDReserve, hmReq, hcollar,
    blockSteps_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax hprep analytic⟩

/-- **`HpbaseTwoLevel_v8_C11G2`（`Dstar` 参数化、`(Rmod, mmod)` request-driven 孪生）**：冻结
`HpbaseTwoLevel_C11G2` 逐字，只改 (i) reserve / `BlockStep` 的半径 `capWindowRadius_C11E + 1` → 参数
`Dstar`；(ii) `∀ εReserve` 前加 `∀ (Rmod : ℝ) (mmod : ℕ)`（在 `∃ Γ Γf` 之后、`∃ pB` 之前）；(iii) 同一
`pB` 多 `Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder`。 -/
def HpbaseTwoLevel_v8_C11G2 (εW Dstar : ℝ) (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
    Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ εW ∧
    Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ εW ∧
    ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
    ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
      prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder ∧
      collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
      ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 Dstar εReserve j

/-- **v8 provider（泛型 `εW`）**：选取顺序同 `hpbaseTwoLevel_of_accuracy_C11G2`（`εc := epsCoarse εW` →
`Γf`（cap `min εW (p6FineEta εc)`）→ `Γ := coarsenTo Γf εc`），请求在其后。 -/
theorem hpbaseTwoLevel_v8_of_pos_C12P (P : OrientedThreeStage.{u}) (g : P.Metric) (εW : ℝ)
    (hεW : 0 < εW) (Dstar : ℝ) (hDstar : 0 < Dstar) :
    HpbaseTwoLevel_v8_C11G2.{u} εW Dstar P g := by
  have hc0 : 0 < epsCoarse_C11G2.{u} εW := epsCoarse_pos_C11G2 hεW
  have hc1 : epsCoarse_C11G2.{u} εW < 1 / 100 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have hccone : epsCoarse_C11G2.{u} εW ≤ coneAccuracy :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcs : epsCoarse_C11G2.{u} εW ≤ εStrong_C12X.{u} :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcW : epsCoarse_C11G2.{u} εW ≤ εW :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcap : 0 < min εW (p6FineEta_C11GT6 (epsCoarse_C11G2.{u} εW)) :=
    lt_min hεW (p6FineEta_pos_C11GT6 hc0)
  obtain ⟨Cdist, -, Γf, hfs, hfcap, hmake⟩ := exists_blockSteps_request_C12P.{u} 1 one_pos _ hcap
  exact ⟨Cdist, coarsenTo_C11G2.{u} Γf (epsCoarse_C11G2.{u} εW) hc0 hc1 hccone, Γf,
    fineOf_coarsenTo_C11G2 Γf _ hc0 hc1 hccone (hfcap.trans (min_le_right _ _)), hcs, hcW, hfs,
    hfcap.trans (min_le_left _ _),
    fun Rmod mmod εReserve hεReserve => hmake P g Dstar hDstar Rmod mmod εReserve hεReserve⟩

/-- **v8 provider（闭合，PROVED）**：`εW := epsW_CXOU2`，任意 `Dstar > 0`。 -/
theorem hpbaseTwoLevel_v8_C11G2 (P : OrientedThreeStage.{u}) (g : P.Metric) (Dstar : ℝ)
    (hDstar : 0 < Dstar) : HpbaseTwoLevel_v8_C11G2.{u} epsW_CXOU2.{u} Dstar P g :=
  hpbaseTwoLevel_v8_of_pos_C12P P g epsW_CXOU2.{u} epsW_CXOU2_pos.{u} Dstar hDstar

theorem capWindowRadius_add_one_pos_C12P : 0 < capWindowRadius_C11E + 1 := by
  have hte := StandardCap.transitionEnd_pos
  unfold capWindowRadius_C11E
  positivity

/-- v8 provider 在冻结半径 `Dstar := capWindowRadius_C11E + 1`。 -/
theorem hpbaseTwoLevel_v8_cap_C12P (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_v8_C11G2.{u} epsW_CXOU2.{u} (capWindowRadius_C11E + 1) P g :=
  hpbaseTwoLevel_v8_C11G2 P g _ capWindowRadius_add_one_pos_C12P

/-! ## 迁移：冻结形、A12′ `hmake`、hSL1 / CC 调用约束，同一 `pB` -/

/-- v8（`Dstar = capWindowRadius + 1`）⇒ 冻结 `HpbaseTwoLevel_C11G2`（请求取 `(0, 0)`，丢请求界）。 -/
theorem hpbaseTwoLevel_of_v8_C12P {εW : ℝ} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (h : HpbaseTwoLevel_v8_C11G2.{u} εW (capWindowRadius_C11E + 1) P g) :
    HpbaseTwoLevel_C11G2.{u} εW P g := by
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ := h
  refine ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, fun εReserve hεReserve => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, -, -, hcollar, hstep⟩ := hmake 0 0 εReserve hεReserve
  exact ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩

/-- **同一 `pB` 的迁移形**：对每个请求 `(Rmod, mmod, εReserve)`，一个 `pB` 同时给 (a) A12′ `hmake`
（`A12GapTopV7TwoC11G7B:99` 解构的 `hbase hdist hres hcollar hstep`，半径 `capWindowRadius + 1`）的
全部合取；(b) hSL1 / CC / hP6b‴ 的调用约束 `acc ≤ εReserve`、`cap + 1 ≤ radius`、`2 ≤ order`
（`pBase_bounds_of_reserve_C11W6`）；(c) NR 的请求界 `Rmod ≤ radius`、`mmod ≤ order`。 -/
theorem hmake_request_C12P (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
    Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ epsW_CXOU2.{u} ∧
    Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ epsW_CXOU2.{u} ∧
    ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
    ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
      (prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j) ∧
      (pB.modelAccuracy ≤ εReserve ∧ capWindowRadius_C11E + 1 ≤ pB.modelRadius ∧
        2 ≤ pB.modelOrder) ∧
      Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder := by
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ := hpbaseTwoLevel_v8_cap_C12P.{u} P g
  refine ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, fun Rmod mmod εReserve hεReserve => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, hR, hm, hcollar, hstep⟩ :=
    hmake Rmod mmod εReserve hεReserve
  exact ⟨pB, prepared, ⟨hbase, hdist, hres, hcollar, hstep⟩,
    pBase_bounds_of_reserve_C11W6 hbase hres, hR, hm⟩

/-- consumer：v8 provider 经迁移回到冻结 provider 的类型（两者都 PROVED；冻结名不动）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : HpbaseTwoLevel_C11G2.{u} epsW_CXOU2.{u} P g :=
  hpbaseTwoLevel_of_v8_C12P (hpbaseTwoLevel_v8_cap_C12P P g)

end GC.LongTime.Ch11

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV2P6HPB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepP6SS

/-!
# `hceil` ⇐ 两级 outer supply 的粗 Good 分量（O-CH11-HCEIL G1，后缀 `_P6HC2`）

R-C11-20 Q5.2 / D-20-13：HSCALESEP 比较孪生 `hscaleSep_slot_of_ceilOnly_P6SS` 剩的 `hceil`（σ 处 ceiling）
在当前 env 已有直接证明链，不是独立分析叶。接法：
* `outerSupply_twoLevel_C11G2 hS hfine F q hF hq` 的结论同时给 `HistoryCanonicalSupply_C11S F q.neckRadius
  Γ.ε C1 C2`（**粗 Good 元组**）与 `TimeDerivativeSupply_C11E F q.neckRadius Ctime`；
* 标准常数比较 `C1ceil_le_C1P6_C11GT6` / `C2ceil_le_C2P6_C11GT6` / `Ctime_le_p6Ctime_C11G7B`
  （FOOT5 `hmargin_slot_P6F5` 在同一标准元组上的调用方式）；
* `ceiling_of_not_good_P6SS`（同元组 HCS + TDS + `¬Good(σ,y)` ⇒ `R(σ,y) ≤ nr(σ)⁻²`）经
  `canonical_rescale_P6X` / `derivative_rescale_P6X`，证明体逐字取自 `P6ScaleSepP6SS.lean:412–422`。

本文件：
* **`hceil_of_outerSupply_P6HC2`（PROVED）**：结论 = HSCALESEP `hceil` binder 逐字；
* **`hdeltaq_of_scrsPlus_P6HC2`（PROVED）**：结论 = 同槽 `hδq`（S1）binder 逐字，由 SCRS⁺ 自带的
  `Tendsto q₀.delta` + `t ≥ 0` 一致性付；
* consumer：喂 SCALESEP `hscaleSep_of_ceiling_P6SS`（只剩 S14 records）。

不取 `outerSupply_twoLevel_C11G2` 的第 3 分量（fine 元组 `(p6FineEta, p6BadC, p6BadC)`），不做精度转换；
不引入新 binder / 新 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2
  BudgetCertificate_C11GT2 SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A
  C1P6_C11GT6 C2P6_C11GT6 p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B)

/-- **`hceil` 付款（PROVED，0 binder；R-C11-20 Q5.2 / D-20-13）**：结论 = HSCALESEP
`hscaleSep_slot_of_ceilOnly_P6SS` 的 `hceil` binder **逐字**（`P6ParamCompatTwoP6SS.lean:711–761`，
sha 断言见 DELIVERIES）。在 hceil 的 env 中调 `outerSupply_twoLevel_C11G2 hS hfine F q hF hq` @ 标准常数比较
`C1ceil ≤ C1P6 std`、`C2ceil ≤ C2P6 std`、`Γ.Ctime ≤ p6Ctime`，**只取第 2 分量（粗 Good 元组
`(Γ.ε, C1P6 std, C2P6 std)` 上的 HCS）与第 4 分量（TDS @ `p6Ctime`）**，不取第 3 分量（fine
`(p6FineEta, p6BadC, p6BadC)`）；再逐字重用 `P6ScaleSepP6SS.lean:412–422` 的证明体
（`canonical_rescale_P6X` / `derivative_rescale_P6X` / `ceiling_of_not_good_P6SS`）。给出的是 σ 处 ceiling，
不经 radius antitone 从 `Tn` 处偷换。 -/
theorem hceil_of_outerSupply_P6HC2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹ := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  subst hε hC1 hC2 hCt
  have hO := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q hF hq
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6Ctime_C11G7B.{u} Γ)
  obtain ⟨-, hcan, -, hder⟩ := hO
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood hwin hwin' hroom hradii i hi k
  have h := (Kh k).ceiling_of_not_good_P6SS
    (nr := (q.rescale_P6N (c k) (hc k)).neckRadius)
    ((F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcan (ind k)))
    ((F.tower.history (ind k)).derivative_rescale_P6X (hc k)
      (fun v z hlo hhi hR =>
        GC.LongTime.Ch11.stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR))
    (hsel k)
  rw [hRdef k]
  exact h

/-- **S1 `hδq` 付款（PROVED，0 binder）**：结论 = `hscaleSep_slot_of_ceilOnly_P6SS` 的 `hδq` binder
**逐字**（`P6ParamCompatTwoP6SS.lean:697–709`）。来源 = SCRS⁺ `hS` 自带的 `Tendsto q₀.delta atTop (𝓝 0)`
（`SameConstructionRetentionSupplyPlus_C11GT6` 第 4 合取的第 3 分量）+ `hq` / `hq₀`：`t ≥ 0` 时
`q.delta t = (chainDiagonal T).delta t = q₀.delta t` ⇒ `q.delta =ᶠ[atTop] q₀.delta`。 -/
theorem hdeltaq_of_scrsPlus_P6HC2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      Tendsto q.delta atTop (𝓝 0) := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord
  obtain ⟨F₀, q₀, -, -, ⟨-, hq₀, -⟩, -, -, ⟨-, -, hδ₀⟩, -⟩ := id hS
  refine hδ₀.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [(hq t ht).1, (hq₀ t ht).1]

/-- **consumer（G1）**：两条 PROVED 付款 + 树内 S14 投影（`lateRecords_of_S14_P6SS` /
`hrec_of_lateRecords_P6SS`）直接喂 SCALESEP `hscaleSep_of_ceiling_P6SS`：σ 处 ceiling 与 `δ → 0` 都来自
同一 SCRS⁺ env，只剩 S14 records。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) {pB : CutoffParameters}
    {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ)
    (hs : Γ.epsilon ≤ εStrong_C12X.{u}) (hW : Γ.epsilon ≤ epsW_CXOU2.{u}) (Cdist : ℝ≥0)
    (εReserve : ℝ) (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
      (T.block j) (T.lookahead j) (T.request j))
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T) (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hacc : pB.modelAccuracy ≤ εP6 Γ Γf) (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :=
  ObservedHistory.hscaleSep_of_ceiling_P6SS (ε := Γ.epsilon)
    (C1 := C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2 := C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)
    (Ctime := p6Ctime_C11G7B.{u} Γ)
    (hdeltaq_of_scrsPlus_P6HC2 εP6 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (ObservedHistory.hrec_of_lateRecords_P6SS (ObservedHistory.lateRecords_of_S14_P6SS hS14))
    (hceil_of_outerSupply_P6HC2 εP6 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord
      rfl rfl rfl rfl)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

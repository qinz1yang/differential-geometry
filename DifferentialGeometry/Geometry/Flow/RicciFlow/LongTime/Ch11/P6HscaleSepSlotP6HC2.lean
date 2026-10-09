import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilOfOuterSupplyP6HC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ParamCompatTwoP6SS

/-!
# HP6B2 `hscaleSep` 槽 ⇐ `hceil` / `hδq` 付款（O-CH11-HCEIL G2a，后缀 `_P6HC2`）

HSCALESEP 比较孪生 `hscaleSep_slot_of_ceilOnly_P6SS`（PROVISIONAL[`hceil` | S1 `hδq`, S14 `hS14`]）喂入
G1 两条 PROVED 付款：`hceil_of_outerSupply_P6HC2`（outerSupply_twoLevel 粗 HCS + TDS 分量）与
`hdeltaq_of_scrsPlus_P6HC2`（SCRS⁺ 自带 `Tendsto q₀.delta`）。剩余只有具名结构 supply S14
`LateLinkedRecordsSupply_C11E F q`（槽 env 里的 `q`；SCRS⁺ 只给 `q₀` 版，`q` 与 `q₀` 只在 `t ≥ 0` 上
`delta / neckRadius` 一致，`fixed / recenterConstant` 无关系，且 S14 要求函数等式 `p.delta = q.delta`，
故不能由 SCRS⁺ 搬运——S14 照旧为已登记具名 supply）。

* **`hscaleSep_slot_of_outerSupply_P6HC2`（PROVISIONAL[S14]）**：结论 = HSCALESEP 槽结论逐字
  （= HP6B2 v2 `hscaleSep` 槽）；
* consumer：经 named argument 喂 `hP6bTwoLevelTime_of_slots_v2_P6HPB2`。
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

/-- **HP6B2 `hscaleSep` 槽（PROVISIONAL[S14 `hS14`]）**：结论 = `hscaleSep_slot_of_ceilOnly_P6SS` 结论
逐字（`P6ParamCompatTwoP6SS.lean:762–815`）；`hS14` binder = 同定理 `hS14` 逐字（l.683–695）。`hceil` 与
S1 `hδq` 由 G1 PROVED 付清（0 binder）。 -/
theorem hscaleSep_slot_of_outerSupply_P6HC2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hS14 :
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
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :
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
      ∀ QA : ℝ, 0 < QA →
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
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
  hscaleSep_slot_of_ceilOnly_P6SS εP6 hS14 (hdeltaq_of_scrsPlus_P6HC2 εP6)
    (hceil_of_outerSupply_P6HC2 εP6)

/-- **consumer（G2a，HP6B2 v2）**：槽产出经 named argument 喂 `hP6bTwoLevelTime_of_slots_v2_P6HPB2`
（只剩 S14 `hS14`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 =>
  ObservedHistory.hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6
    (hscaleSep := hscaleSep_slot_of_outerSupply_P6HC2 (P := P) (g := g) εP6 hS14)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

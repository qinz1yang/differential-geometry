import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3DerivSlotP6F5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FootSecondP6F2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3MarginRecordsP6F5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6Foot3MarginCHN.lean` 机械克隆]
# CHN G2a：hmargin 槽（HN ceiling）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6Foot3MarginRecordsP6F5.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1HN_CH2 p6X2HN_CH2 p6CtimeHN_CH2 p6BadCH2_CH2 htransMBadHN_CH2)
namespace ObservedHistory
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- **G3a `hmargin_slot_P6F5_CH2`**（PROVED，0 binder）：结论 = HP6B2 v2 `hmargin` 槽逐字；= FOOT2
`hmargin_of_supplies_P6F2` 在 HP6b env 上实例化（常数比较全部已付，见文件头）。 -/
theorem hmargin_slot_P6F5_CH2 (P : OrientedThreeStage.{u}) (g : P.Metric)
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
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ →
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  subst hε hC1 hC2 hCt
  obtain ⟨F₀, q₀, -, -, ⟨hF₀, hq₀, -⟩, -, -, ⟨-, -, hδ₀⟩, ⟨-, -, -, hP5L₀⟩, -⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨-, hcanS, -, -⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q₀ hF hq₀
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1HN_CH2.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2HN_CH2.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6CtimeHN_CH2.{u} Γ)
  have hΓ : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  exact hmargin_of_supplies_P6F2 F (Ctime := p6CtimeHN_CH2.{u} Γ) Γ.epsilon_pos hΓ
    (GC.LongTime.Ch11.capCollar_le_C1P6HN_CH2 Γ) (GC.LongTime.Ch11.capCollar_le_C2P6HN_CH2 Γ)
    hP5L₀ hδ₀ hcanS le_rfl le_rfl le_rfl
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

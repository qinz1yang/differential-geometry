import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLADriverBridgeGateHCTDCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FreshRescaleP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TRsConj1CeilHTP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TRsJ10SupplyTH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinGateMTR

set_option autoImplicit false

/-!
# TRSHNOT G3b：hTRs 槽桥的 TH 孪生——无 hnot 前提（后缀 `_TH`）

`hTRs_of_res_gate_TJ`（P6DistLADriverBridgeGateTJ，TRSJ10 G3）逐字复制，只动三处：
(1) 去掉槽假设 `hpk`（`∀ ctx, R4HnotC_TJ F ε C1 C2 Ctime`）——hnot 于 R4 中心已由 G1 核证出；
(2) driver 换为 G3a `hTR_of_driver_gate_TH`（去掉 `R4HnotC_TJ` 前提）；
(3) 删去 `hJ10 := hpk …` 及其传给 driver 的一处。
结论（conj1 带天花板 ∧ `∀ Aseed … ∃ Kt …`）与 MTR / TJ 桥逐字相同，故 `hdistLA_win_of_TRs_gate_MTR`
（P6DistLargeWinGateMTR）原样消费（consumer `example`）。桥内 conj1（hsepWK）仍由 recent + 天花板付
（`conj1_of_recent_ceil_HTP`，同 MTR / TJ 桥）。⇒ 顶层 `_hTRs` binder 的内容整个可去（不再是 binder）。
生成器 build-logs/scratch/O-CH11-TRSHNOT/gen/g3.py。
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
open ObservedHistory (DepthExtendable)
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)



/-- **hTRs 槽（conj1 带天花板）无 hnot 前提（`_TH`，INTEGRATION-ONLY 于 G1/G2）**：见模块文档。 -/
theorem hTRs_of_res_gate_TH :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric)
      (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ), (∀ Γ Γf, εP6 Γ Γf ≤ ε₀) →
    (∀ Γ Γf, εP6 Γ Γf ≤ min GC.LongTime.Ch11.εProf_C11E.{u}
      (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon (GC.LongTime.Ch11.chainC1_C11KD Γf)
        (GC.LongTime.Ch11.chainC2_C11KD Γf) P)) →
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
      GC.LongTime.Ch11.collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ →
      ∀ (pF : CutoffParameters) (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      pF.modelRadius = pB.modelRadius → pF.modelOrder = pB.modelOrder →
      pF.modelAccuracy = pB.modelAccuracy →
      (∀ t : ℝ, 0 ≤ t → pF.delta t = q.delta t ∧ pF.neckRadius t = q.neckRadius t) →
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) →
      (∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) →
      (∀ n e, ((F.tower.history n).toHistory.event e).old =
        ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
      Tendsto pF.delta atTop (𝓝 0) →
      (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
          ∀ h, (records n e).nominalRadius h ≤ η * pF.neckRadius t) →
      (
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
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale)∧
      ∀ Aseed : ℝ, 1 < Aseed →
      ∀ (T r : ℝ), 0 < T → 0 < r → ∃ Kt : ℝ, 0 ≤ Kt ∧
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
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
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
            ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
              (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Kt * R k) := by
  obtain ⟨ε₀, hε₀, hdrv⟩ := hTR_of_driver_gate_TH.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g εP6 hle hεP6'
    pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hcol ε C1 C2 Ctime
    hε hC1 hC2 hCt pF records hprad hpord hpacc hpq hcan hlink hradl hold hδ hrec
  have hte : StandardCap.transitionEnd + 10 < capWindowRadius_C11E + 1 := by
    have := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    linarith
  have hεs : ε ≤ εStrong_C12X.{u} := by rw [hε]; exact hs
  have hcw : εStrong_C12X.{u} ≤ crossingWindowNeckAccuracy.{u} := by
    unfold εStrong_C12X
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcn : εStrong_C12X.{u} ≤ crossingNeckAccuracy.{u} := by
    unfold εStrong_C12X
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcone : εStrong_C12X.{u} ≤ coneAccuracy := by
    unfold εStrong_C12X
    exact min_le_left _ _
  have hε0 : 0 < ε := by rw [hε]; exact Γ.epsilon_pos
  have hC2' : 0 ≤ C2 := by
    rw [hC2]
    exact (zero_le_one.trans (GC.LongTime.Ch11.one_le_C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ))
  -- 同一 SCRS⁺ 元组（F-24-8）
  obtain ⟨F₀, q₀, -, recQ, ⟨h1, h2, -⟩, -, -, ⟨-, hanti, hδ₀⟩, ⟨-, hrecQ, -, -⟩, -, hTD₀, -, -,
    h9⟩ := hS
  obtain rfl : F = F₀ := (GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (h1.trans hF.symm)).symm
  have hfineK : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale := by
    intro D ζ m hζ
    obtain ⟨T₀, hT⟩ := h9 D ζ m hζ
    refine ⟨T₀, fun n => ?_⟩
    obtain ⟨p, -, -, -, -, hD, hζ', hm, rec', hlink', hrel⟩ := hT n
    exact ⟨p, hD, hζ', hm, rec', fun i hi b =>
      GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _ (hlink' i hi b),
      fun i hi b => (hrel i hi).2.2.2.2.1 b⟩
  have hTD := timeDerivativeSupply_mono_HCTD hTD₀
    (((GC.LongTime.Ch11.fine_Ctime_le_p6Ctime_A6K.{u} hfine).trans
      (GC.LongTime.Ch11.p6Ctime_le_p6CtimeHN_CH2.{u} Γ)).trans_eq hCt.symm)
  have hsupA := GC.LongTime.Ch11.hsupA_of_hP6bEnv_P6JA (hεP6' Γ Γf) hcol T hcert F q₀ hF h2
    hacc hrad hord
  have hdq : ∀ x : ℝ, 0 ≤ x → q₀.neckRadius x = q.neckRadius x := fun x hx =>
    (h2 x hx).2.trans (hq x hx).2.symm
  -- conj1（hsepWK）⇐ recent + 天花板（G1 `conj1_of_recent_ceil_HTP`；q₀ 版喂 driver，q 版为槽输出）
  have hpF0 : ∀ x : ℝ, 0 ≤ x → pF.neckRadius x = q₀.neckRadius x := fun x hx =>
    (hpq x hx).2.trans (hdq x hx).symm
  have hantiq : AntitoneOn q.neckRadius (Ici 0) := by
    intro a ha b hb hab
    rw [← hdq a ha, ← hdq b hb]
    exact hanti ha hb hab
  have hsep₀ := conj1_of_recent_ceil_HTP (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) F records
    hpF0 hanti hδ hrec
  have hsep := conj1_of_recent_ceil_HTP (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) F records
    (fun x hx => (hpq x hx).2) hantiq hδ hrec
  refine ⟨hsep, fun Aseed hA T r hT hr => ?_⟩
  obtain ⟨Kt, hKt, hfr'⟩ := hdrv F records hcan (hpacc ▸ hacc.trans (hle Γ Γf)) (hpord ▸ hord)
    (hprad ▸ hte.trans_le hrad) hε0 (hεs.trans hcw) (hεs.trans hcn) (hεs.trans hcone) hC2' q₀
    hanti hδ₀ recQ hrecQ hfineK hTD hsupA hsep₀
    Aseed hA T r hT hr
  refine ⟨Kt, hKt, ?_⟩
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvolG h2G hnrG seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  refine hfr' ind c hc Tn pT hTc aSeed haT hclock hone hsm hvolG h2G ?_ seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ ?_ i hi
  · intro k x hx1 hx2
    have hxpos : 0 < x := by linarith [h2G k]
    have h0 : 0 ≤ 4 * (c k * x) / 3 := by have := hc k; positivity
    rw [hdq _ h0]
    exact hnrG k x hx1 hx2
  · intro k
    have h0 : 0 ≤ c k * (Tn k : ℝ) := mul_nonneg (hc k).le (Tn k).2.1
    have e : (q₀.rescale_P6N (c k) (hc k)).neckRadius (Tn k) =
        (q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) := by
      change q₀.neckRadius (c k * (Tn k : ℝ)) / Real.sqrt (c k) =
        q.neckRadius (c k * (Tn k : ℝ)) / Real.sqrt (c k)
      rw [hdq _ h0]
    rw [e]
    exact hceil k

/-- consumer：TH 桥的结论（无 `hpk`）原样喂 `hdistLA_win_of_TRs_gate_MTR`（同顶层 hTRs 消费链）。 -/
example (P : OrientedThreeStage.{0}) (g : P.Metric) : True := by
  obtain ⟨ε₁, hε₁, hDL⟩ := hdistLA_win_of_TRs_gate_MTR.{0}
  obtain ⟨ε₀, hε₀, hGate⟩ := hTRs_of_res_gate_TH.{0}
  let e' : ClosedBirthConstants → ClosedBirthConstants → ℝ := fun Γ Γf =>
    min (min ε₀ ε₁) (min GC.LongTime.Ch11.εProf_C11E.{0}
      (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon (GC.LongTime.Ch11.chainC1_C11KD Γf)
        (GC.LongTime.Ch11.chainC2_C11KD Γf) P))
  have := @hDL P g e' (fun _ _ => (min_le_left _ _).trans (min_le_right _ _))
    (@hGate P g e' (fun _ _ => (min_le_left _ _).trans (min_le_left _ _))
      (fun _ _ => min_le_right _ _))
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

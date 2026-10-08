import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4NotTRGateHCT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4DriverLeV2CXW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HanchorHPNFrameG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusRecentP6SF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinchSlotP6HP2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR

set_option autoImplicit false

/-!
# R4 driver 的 gate + 天花板孪生：hK 在 driver 内付（O-CH11-HCEILT G3，后缀 `_HCT`）

`hTR_of_driver_gate_HCT`：`hTR_of_driver_le_v2_CXW` 孪生。
* 输出 hTR 合同收窄为 hTR‴（`∀ Aseed > 1`，前缀 + gate 块 + 天花板 `hceil`；义务变弱，§0.2，lead R39/R41）；
* 前提包删 `hK`；R4 中心 kernel 体由 `sliceBCBD_kernel_R4center_fine_seq_HCT` 在 driver 内付，
  环境加：`ε ≤ coneAccuracy`、`0 ≤ C2`、`q`（反单调、`δ → 0`）、`q`-records `recQ` 及其 recent 供给、
  SCRS⁺ (9) 细 records `hfine`、`TimeDerivativeSupply`、FRESH `hsupA`（均为 SCRS⁺ 投影 / 已登记合同）；
  HI 初值由 `exists_initialHI_P6WR`（PROVED）付，`hpinchK0` ⇐ `hpinch_core_of_HIProp_P6HP2`。
* 因子 2：R4 中心 `R′ < 2R ≤ 2ρ̂⁻²`，取 `ρs := ρ̂/√2`；`hsepρ` 由 recent 路线取 `N = 2(k+1)`
  （`sepRhoK_recent_N_HCT`），阈值 `Θ k = max (T_rec(η_k)) (2Tδ)` 经 E1′ 对角选点付；
  `hRle` ⇐ E1′ 的 `2k + 2 ≤ R`。
其余证明逐字。生成器 build-logs/scratch/O-CH11-HCEILT/gen/genC.py。
-/

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open ObservedHistory (DepthExtendable)

universe u

/-- **(SEP-ρ⁺) K 帧 recent 形，任意因子 `N`（`_HCT`，PROVED）**：`sepRhoPlusK_branch_of_recent_P6SF`
的孪生，结论 `N n · ρ(Tn)⁻² ≤ scale`（去 `habs`，`2 ≤ Tn` 代 `c / Tno`）。 -/
theorem sepRhoK_recent_N_HCT {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {Tn R Tr η Nn : ℕ → ℝ} {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀) (hR : ∀ n, 0 < R n)
    (hTn2 : ∀ n, 2 ≤ Tn n)
    (hwin : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop, Tn n - 1 / 2 ≤ t n - B / R n)
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0))
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hρ0 : ∀ᶠ n in atTop, 8 * θ₀ * (p n).neckRadius 0 ^ 2 ≤ Tn n)
    (hη : ∀ n, 0 ≤ η n) (hηN : ∀ n, 2 * η n ^ 2 * Nn n ≤ 1)
    (hTr : ∀ n, Tr n ≤ Tn n)
    (hrec : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) (s : ℝ),
      Tr n ≤ s → (K n).time i.succ ∈ Icc (s / 2) s →
      ∀ h, (recordsK n i hi).nominalRadius h ≤ η n * (p n).neckRadius s) :
    ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        Nn n * ((p n).neckRadius (Tn n) ^ 2)⁻¹ ≤ ((recordsK n i hi).static b).neck.scale := by
  intro B hB
  filter_upwards [hwin B hB, hρ0] with n hw hρn
  intro i hi b _ hbr
  have hT2 := hTn2 n
  have hlate : Tn n ≤ 2 * (K n).time i.succ := by
    rcases hbr with hwb | hyc
    · linarith
    · have hage := youngCap_age_lt_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) hθ₀ hyc
      have hBR : 0 ≤ B / R n := div_nonneg hB.le (hR n).le
      nlinarith
  exact sepRhoPlus'_of_recentSupply_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) (hη n)
    (hηN n) (by linarith) (hTr n) hlate (hrec n i hi)

/-- **塔 recent ⇒ K 帧 recent（`_HCT`，PROVED）**：`rescale_P6M` 的 `nominalRadius / √c`、
`(q.rescale c).neckRadius s = ρ(c s)/√c`、时间 `/ c`；阈值 `T / c`。 -/
theorem hrecK_of_recent_HCT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e q)
    {ε T : ℝ} (hT : ∀ t, T ≤ t → ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recQ n i).nominalRadius h ≤ ε * q.neckRadius t)
    (n : ℕ) {c : ℝ} (hc : 0 < c) (i : Fin ((F.tower.history n).rescale_P6N c hc).eventCount)
    (s : ℝ) (hs : T / c ≤ s)
    (hmem : ((F.tower.history n).rescale_P6N c hc).time i.succ ∈ Icc (s / 2) s) :
    ∀ h, ((recQ n i).rescale_P6M c hc).nominalRadius h ≤
      ε * (q.rescale_P6N c hc).neckRadius s := by
  intro h
  have htk : ((F.tower.history n).rescale_P6N c hc).time i.succ =
      (F.tower.history n).time i.succ / c := rfl
  rw [htk] at hmem
  have hTs : T ≤ c * s := by
    rw [div_le_iff₀ hc] at hs
    linarith
  have hm1 : c * s / 2 ≤ (F.tower.history n).time i.succ := by
    have := hmem.1
    rw [le_div_iff₀ hc] at this
    linarith
  have hm2 : (F.tower.history n).time i.succ ≤ c * s := by
    have := hmem.2
    rw [div_le_iff₀ hc] at this
    linarith
  have key := hT (c * s) hTs n i ⟨hm1, hm2⟩ h
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  change (recQ n i).nominalRadius h / Real.sqrt c ≤ ε * (q.neckRadius (c * s) / Real.sqrt c)
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right key hsq.le

/-- `((a/√2)²)⁻¹ = 2·(a²)⁻¹`（`_HCT`）。 -/
theorem inv_sq_div_sqrt_two_HCT (a : ℝ) : ((a / Real.sqrt 2) ^ 2)⁻¹ = 2 * (a ^ 2)⁻¹ := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), inv_div, div_eq_mul_inv]

/-- K 帧参数的反单调（`_HCT`）。 -/
theorem antitoneOn_rescale_P6N_HCT {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    {c : ℝ} (hc : 0 < c) : AntitoneOn (q.rescale_P6N c hc).neckRadius (Ici 0) := by
  intro a ha b hb hab
  change q.neckRadius (c * b) / Real.sqrt c ≤ q.neckRadius (c * a) / Real.sqrt c
  have ha' : 0 ≤ c * a := mul_nonneg hc.le ha
  have hb' : 0 ≤ c * b := mul_nonneg hc.le hb
  exact div_le_div_of_nonneg_right
    (hanti (mem_Ici.mpr ha') (mem_Ici.mpr hb') (mul_le_mul_of_nonneg_left hab hc.le))
    (Real.sqrt_nonneg _)

/-- **R4 中心 hK 体 ⇐ driver 环境 + hTR‴ 帧（`_HCT`，PROVED 相对环境前提）**：
`sliceBCBD_kernel_R4center_fine_seq_HCT` 在 R4 中心 `(t, pm)` 的实例化（见模块文档）。 -/
theorem hK_R4center_of_env_HCT {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e q)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale)
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {Trec : ℕ → ℝ} (hTrec : ∀ k : ℕ, ∀ t, Trec k ≤ t →
      ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recQ n i).nominalRadius h ≤ 1 / (2 * ((k : ℝ) + 1)) * q.neckRadius t)
    {Tδ : ℝ} (hTδ : ∀ t : ℝ, Tδ ≤ t → q.recenterConstant * q.delta t ≤ 1 / 2)
    {phi : ℝ → ℝ} (hpinK : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ)
        (i' : Fin ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.eventCount),
        Perelman.PhiAlmostNonnegative
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.event i').incoming.flow
          (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.castSucc)
            (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.succ) ∩
            Ici (1 / 2)) phi)
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Aseed : ℝ} (hA : 1 < Aseed) {κA Tf : ℝ} (hκA : 0 < κA)
    (hsupK : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
      KappaSeedWindowFwd_C11PK
        (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κA
        (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory) :
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
          (∀ k,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
              ((seedTrace k).point ((Kh k).activeStage (t k)) ((Kh k).activeStage_mono (hat k))
                ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (1 / Real.sqrt (R k))) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ k, max (Trec k) (2 * Tδ) ≤ c k * (Tn k : ℝ)) → (∀ k : ℕ, 2 * (k : ℝ) + 2 ≤ R k) →
      ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((Kh n).event (i n)).incoming.flow.base.metric (t n))
            (pm n)
            (A / Real.sqrt (((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n))),
          ((Kh n).event (i n)).incoming.flow.scalar (t n) z ≤
            Q * ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n)
 := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    _hRdef hRpos hRr hL _hsel _hgood haS hTnS _hroom _hradii hgateP hceil i _hi pm t y' hat hts hy'
    _hcross hslab hclose hcompR hcmp hcmpL hgood' hΘ h2R
  let K : ℕ → RetainedCoreHistory.{u} := fun n =>
    (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
  have hact : ∀ n, (Kh n).activeStage (t n) = (i n).castSucc := fun n =>
    RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K n) (i n) (t n) (hslab n)
  have hRc : ∀ n, 0 < ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := fun n => by
    have h := (K n).scalar_of_incoming_P6X (i n) (hact n).symm (t n) (pm n) (y' n) (hy' n)
    rw [← h]
    linarith [hcmpL n, hRpos n]
  -- ===== hK 内付：R4 中心 kernel（HCEILT） =====
  have hscal : ∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n) =
      ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := fun n =>
    (K n).scalar_of_incoming_P6X (i n) (hact n).symm (t n) (pm n) (y' n) (hy' n)
  have hR1 : ∀ n, (1 : ℝ) ≤ R n := fun n => by
    have h1 := hRr n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hcmpLK : ∀ n, R n / 2 < ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) :=
    fun n => (hscal n) ▸ hcmpL n
  have hcmpK : ∀ n, ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) < 2 * R n :=
    fun n => (hscal n) ▸ hcmp n
  have hRleK : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) :=
    fun n => by linarith [hcmpLK n, h2R n]
  have hρpos : ∀ n, 0 < (q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) := fun n =>
    (q.rescale_P6N (c n) (hc n)).neckRadius_pos _ (Tn n).2.1
  have hceilK : ∀ n, ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) ≤
      (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) / Real.sqrt 2) ^ 2)⁻¹ := fun n => by
    rw [inv_sq_div_sqrt_two_HCT]
    linarith [hcmpK n, hceil n]
  have hjtK : ∀ n, (K n).time (i n).castSucc < (t n : ℝ) := fun n => (hslab n).1
  have htjK : ∀ n, (t n : ℝ) < (K n).time (i n).succ := fun n => (hslab n).2
  have htTn : ∀ n, t n ≤ Tn n := fun n => (hts n).trans (hsT n)
  have hTn1 : ∀ n, (1 : ℝ) ≤ Tn n := fun n => by linarith [hTn2 n]
  -- T₀ := Tn − 1/2；c · T₀ → ∞
  have hcT₀ : ∀ n : ℕ, ((n : ℝ) + 1) / 2 ≤ c n * ((Tn n : ℝ) - 1 / 2) := fun n => by
    have h1 := hTc n
    have h2 : 0 ≤ c n * ((Tn n : ℝ) / 2 - 1 / 2) :=
      mul_nonneg (hc n).le (by linarith [hTn1 n])
    nlinarith
  have hT₀tend : Tendsto (fun n => c n * ((Tn n : ℝ) - 1 / 2)) atTop atTop :=
    tendsto_atTop_mono hcT₀
      ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_div_const two_pos)
  have hfineK := hfineK_of_tower_RU recQ hfine ind c hc (fun n => (Tn n : ℝ) - 1 / 2) hT₀tend
  have hpinchK0 : ∀ n (i' : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i').incoming.flow
      (Ico ((K n).time i'.castSucc) ((K n).time i'.succ) ∩ Ici ((Tn n : ℝ) - 1 / 2)) phi :=
    fun n i' s hs => hpinK ind c hc n i' s
      ⟨hs.1, le_trans (by linarith [hTn2 n]) (mem_Ici.mp hs.2)⟩
  -- 窗口（R4 中心，`Rt := R`）
  have hT₀K : ∀ B : ℝ, ∀ᶠ n in atTop, (Tn n : ℝ) - 1 / 2 ≤ (t n : ℝ) - B / R n := by
    intro B
    filter_upwards [hTnS (|B| + 1) (by positivity)] with n hn
    have h1 := hclose n
    have h2 : (|B| + 1) / R n = |B| / R n + 1 / R n := add_div _ _ _
    have h3 : B / R n ≤ |B| / R n := div_le_div_of_nonneg_right (le_abs_self B) (hRpos n).le
    norm_num at hn
    linarith
  have hwinK : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / R n := by
    intro T' hT'
    filter_upwards [haS (T' + 1) (by linarith)] with n hn
    have h1 := hclose n
    have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
    linarith
  have hwinFK : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop,
      (Tn n : ℝ) - 1 ^ 2 / 2 ≤ (t n : ℝ) - T' / R n := by
    intro T' hT'
    filter_upwards [hTnS (T' + 1) (by linarith)] with n hn
    have h1 := hclose n
    have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
    linarith
  -- FRESH
  have hTκ : ∀ᶠ n in atTop, Tf / c n ≤ (Tn n : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt Tf
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [div_le_iff₀ (hc n)]
    have h1 := hTc n
    have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hvolS : ∀ n, ENNReal.ofReal ((Aseed + 7)⁻¹ * 1 ^ 3) ≤ ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) 1 := fun n => by
    have hA0 : 0 < Aseed := by linarith
    have h7 : (Aseed + 7)⁻¹ ≤ Aseed⁻¹ := inv_anti₀ hA0 (by linarith)
    exact le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h7 (by positivity)))
      (hvol n)
  -- gate / 端点有限（R4 中心）
  have hσtop : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add (hgateP n))
  have hdσK : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
      ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
        ((Kh n).activeStage_mono (htTn n))) (y' n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hσtop n, ENNReal.ofReal_ne_top⟩) (hcompR n)
  have hgateK : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
          ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
            ((Kh n).activeStage_mono (htTn n))) (y' n) +
        ENNReal.ofReal (((L n - 2) / 2 + 1) /
          Real.sqrt (((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n))) ≤
        ENNReal.ofReal ((Aseed + 7) * 1) := by
    filter_upwards [hL.eventually_ge_atTop 2] with n hLn
    set R' := ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) with hR'
    have hsR := Real.sqrt_pos.mpr (hRpos n)
    have hR'pos : 0 < R' := by linarith [hcmpLK n, hRpos n]
    have hsR' := Real.sqrt_pos.mpr hR'pos
    have hsq : Real.sqrt (R n) ≤ 2 * Real.sqrt R' := by
      have h4 : Real.sqrt (4 * R') = 2 * Real.sqrt R' := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [← h4]
      exact Real.sqrt_le_sqrt (by linarith [hcmpLK n])
    have hb : ((L n - 2) / 2 + 1) / Real.sqrt R' ≤ L n / Real.sqrt (R n) := by
      rw [div_le_div_iff₀ hsR' hsR]
      nlinarith
    have hb0 : 0 ≤ ((L n - 2) / 2 + 1) / Real.sqrt R' := div_nonneg (by linarith) hsR'.le
    have ha0 : 0 ≤ 1 / Real.sqrt (R n) := by positivity
    have hsum : ENNReal.ofReal (1 / Real.sqrt (R n)) +
        ENNReal.ofReal (((L n - 2) / 2 + 1) / Real.sqrt R') ≤
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) := by
      rw [← ENNReal.ofReal_add ha0 hb0]
      apply ENNReal.ofReal_le_ofReal
      have : (L n + 1) / Real.sqrt (R n) = 1 / Real.sqrt (R n) + L n / Real.sqrt (R n) := by ring
      linarith
    calc _ ≤ (riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (1 / Real.sqrt (R n))) +
          ENNReal.ofReal (((L n - 2) / 2 + 1) / Real.sqrt R') := add_le_add (hcompR n) le_rfl
      _ ≤ riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) := by
          rw [add_assoc]
          exact add_le_add le_rfl hsum
      _ ≤ ENNReal.ofReal ((Aseed + 3) * 1) := hgateP n
      _ ≤ ENNReal.ofReal ((Aseed + 7) * 1) := ENNReal.ofReal_le_ofReal (by linarith)
  -- (SEP-ρ⁺) ⇐ recent（N = 2(k+1)），ρs := ρ̂/√2
  have hantiK : ∀ n, AntitoneOn (q.rescale_P6N (c n) (hc n)).neckRadius (Ici 0) := fun n =>
    antitoneOn_rescale_P6N_HCT hanti (hc n)
  have hΘk : ∀ n, max (Trec n) (2 * Tδ) ≤ c n * (Tn n : ℝ) := hΘ
  have hΛδK : ∀ n (i' : Fin (K n).eventCount), (Tn n : ℝ) - 1 / 2 ≤ (K n).time i'.succ →
      (q.rescale_P6N (c n) (hc n)).recenterConstant *
        (q.rescale_P6N (c n) (hc n)).delta ((K n).time i'.succ) ≤ 1 / 2 := fun n i' hi' => by
    change q.recenterConstant * q.delta (c n * (K n).time i'.succ) ≤ 1 / 2
    apply hTδ
    have h1 := mul_le_mul_of_nonneg_left hi' (hc n).le
    have h2 := hcT₀ n
    have h3 : 2 * Tδ ≤ c n * (Tn n : ℝ) := (le_max_right _ _).trans (hΘk n)
    have h4 : c n * ((Tn n : ℝ) / 2) ≤ c n * ((Tn n : ℝ) - 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hTn1 n]) (hc n).le
    nlinarith
  have hρ0K : ∀ᶠ n in atTop,
      8 * 1 * (q.rescale_P6N (c n) (hc n)).neckRadius 0 ^ 2 ≤ (Tn n : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (8 * q.neckRadius 0 ^ 2)
    filter_upwards [eventually_ge_atTop N] with n hn
    change 8 * 1 * (q.neckRadius (c n * 0) / Real.sqrt (c n)) ^ 2 ≤ (Tn n : ℝ)
    rw [mul_zero, div_pow, Real.sq_sqrt (hc n).le, mul_one, ← mul_div_assoc,
      div_le_iff₀ (hc n)]
    have h1 := hTc n
    have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hwinR' : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop, (Tn n : ℝ) - 1 / 2 ≤ (t n : ℝ) -
      B / ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := by
    intro B hB
    filter_upwards [hT₀K (2 * B)] with n hn
    have hR'pos : 0 < ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := by
      linarith [hcmpLK n, hRpos n]
    have : B / ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) ≤ 2 * B / R n := by
      rw [div_le_div_iff₀ hR'pos (hRpos n)]
      nlinarith [hcmpLK n]
    linarith
  have hsepN := sepRhoK_recent_N_HCT (K := K) (j := i) (t := fun n => (t n : ℝ))
    (T₀ := fun n => (Tn n : ℝ) - 1 / 2) (p := fun n => q.rescale_P6N (c n) (hc n))
    (fun n i' _ => (recQ (ind n) i').rescale_P6M (c n) (hc n))
    (Tn := fun n => (Tn n : ℝ))
    (R := fun n => ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n))
    (Tr := fun n => Trec n / c n) (η := fun n => 1 / (2 * ((n : ℝ) + 1)))
    (Nn := fun n => 2 * ((n : ℝ) + 1)) (θ₀ := 1) zero_le_one
    (fun n => by linarith [hcmpLK n, hRpos n]) (fun n => (hTn2 n).le) hwinR' hantiK hΛδK hρ0K
    (fun n => by positivity)
    (fun n => by
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
      nlinarith)
    (fun n => by
      rw [div_le_iff₀ (hc n)]
      have := (le_max_left _ _).trans (hΘk n)
      linarith)
    (fun n i' _ s hs hmem => hrecK_of_recent_HCT recQ (hTrec n) (ind n) (hc n) i' s hs hmem)
  have hsepρK : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i' : Fin (K n).eventCount) (hi' : (Tn n : ℝ) - 1 / 2 ≤ (K n).time i'.succ)
        (b : ((K n).toHistory.event i').RetainedBoundaryIndex),
        i'.succ ≤ (i n).castSucc →
        ((t n : ℝ) - B / ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) ≤
            (K n).time i'.succ ∨
          (t n : ℝ) - (K n).time i'.succ ≤
            1 * ((((recQ (ind n) i').rescale_P6M (c n) (hc n)).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1)
            (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) / Real.sqrt 2) ^ 2)⁻¹ ≤
          (((recQ (ind n) i').rescale_P6M (c n) (hc n)).static b).neck.scale := by
    intro B hB
    filter_upwards [hsepN B hB] with n hn i' hi' b hij hor
    have h := hn i' hi' b hij hor
    have hab : (n : ℝ) + 1 ≤ ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := by
      have h1 := hRr n
      have h2 := hceil n
      linarith
    rw [inv_sq_div_sqrt_two_HCT, max_eq_right (by linarith)]
    linarith
  -- 前缀 Dt（阈值 ≥ max (n+1) ρ̂⁻²）
  obtain ⟨hp1, hp2⟩ := hpre_Tn_G9S hTD hanti ind hc (j := i) (t := fun n => (t n : ℝ))
    hjtK htjK (fun n => (Tn n : ℝ)) (fun n => Subtype.coe_le_coe.mpr (htTn n))
  have hqle : ∀ n : ℕ,
      max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      max ((n : ℝ) + 1)
        (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) / Real.sqrt 2) ^ 2)⁻¹ := fun n => by
    rw [inv_sq_div_sqrt_two_HCT]
    have : 0 ≤ ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := by positivity
    exact max_le_max le_rfl (by linarith)
  have hhK : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((Kh n).event (i n)).incoming.flow.base.metric (t n))
          (pm n)
          (A / Real.sqrt (((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n))),
        ((Kh n).event (i n)).incoming.flow.scalar (t n) z ≤
          Q * ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := by
    exact ObservedHistory.sliceBCBD_kernel_R4center_fine_seq_HCT (K := K) (j := i)
      (t := fun n => (t n : ℝ)) (T₀ := fun n => (Tn n : ℝ) - 1 / 2)
      (p0 := fun n => q.rescale_P6N (c n) (hc n))
      (recordsK0 := fun n i' _ => (recQ (ind n) i').rescale_P6M (c n) (hc n)) (yG := pm)
      (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := one_pos) (hjt := hjtK)
      (htj := htjK) (hfineK := hfineK) (hpinchK0 := hpinchK0) (Kh := Kh) (hKh := rfl)
      (σ := t) (hσ := fun _ => rfl) (y := y') (hyG := hy')
      (R := fun n => ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n))
      (hRpos := hRc) (hRn := fun _ => rfl) (hRle := hRleK) (Rt := R) (hRtpos := hRpos)
      (hcmpL := hcmpLK) (hT₀ := hT₀K) (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := htTn)
      (has := hat) (pT := pT) (seedTrace := seedTrace) (Lt := L) (hL := hL)
      (L := fun n => (L n - 2) / 2) (hLdef := fun _ => rfl) (hCg := le_rfl) (hgood' := hgood')
      (hwin := hwinK) (hr := one_pos) (hsmall := hsm) (hclock := hclock) (a₀ := fun _ => 0)
      (ha₀ := fun _ => le_rfl)
      (hpin := fun n s x =>
        ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc n s x)
      (hRa := fun n => by nlinarith [hRleK n, hone n, Nat.cast_nonneg (α := ℝ) n])
      (T₀X := fun _ => 0) (hT₀X := fun n => (aSeed n).2.1) (hOldX := fun _ _ _ => rfl)
      (hdσ := hdσK) (hκ := hκA)
      (nr := fun n w => q.neckRadius (4 * (c n * w) / 3) / Real.sqrt (c n))
      (Tκ := fun n => Tf / c n) (Aκ := Aseed + 7) (hWK := fun n => hsupK ind c hc n)
      (hTκ := hTκ) (htimeS := fun n => by linarith [hTn2 n]) (hvolS := hvolS)
      (hnrS := fun n w h1 h2 => hnrS n w h1 h2) (hwinF := hwinFK) (hgate := hgateK)
      (ρs := fun n _ => (q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) / Real.sqrt 2)
      (hceil := hceilK) (hsepρ := hsepρK)
      (hpre1 := fun n e he => derivativeBoundBefore_mono_qcan_P6SN _ (hqle n) (hp1 n e he))
      (hpre2 := fun n => derivativeBoundBefore_mono_qcan_P6SN _ (hqle n) (hp2 n))
  exact hhK

/-- **R4 driver gate + 天花板孪生（`_HCT`，PROVISIONAL[hsepWK, hbcadC, hkappaC, hseed, hsurvive,
hextend, hpinch]；hK 退场）**：见模块文档。 -/
theorem hTR_of_driver_gate_HCT :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters}
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      pF.modelAccuracy ≤ ε₀ → 2 ≤ pF.modelOrder →
      StandardCap.transitionEnd + 10 < pF.modelRadius →
      0 < ε → ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
      -- HCEILT 环境（R4 中心 kernel 内付 hK）：SCRS⁺ 投影 / FRESH / 数值
      ε ≤ coneAccuracy → 0 ≤ C2 →
      ∀ (q : CutoffParameters), AntitoneOn q.neckRadius (Ici 0) → Tendsto q.delta atTop (𝓝 0) →
      ∀ (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e q),
      (∀ ε' : ℝ, 0 < ε' → ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
        ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, (recQ n i).nominalRadius h ≤ ε' * q.neckRadius t) →
      (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale) →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      (∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
        ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
          KappaSeedWindowFwd_C11PK
            (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
            (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory) →
      -- hsepWK（塔帧 (SEP-ρ)，owner HNOT-LOCALDT）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale) →
      ∀ {Cst : ℝ≥0} {r₀ w κ : ℝ} {Phi : ℝ → ℝ}, 0 < r₀ → 0 < w → 0 < κ →
      Perelman.AdmissiblePinchingFunction Phi →
      -- hsurvive（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
          (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
              (A / Real.sqrt (R n)),
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) z ≤ Q * R n) →
          (Kh n).isTracedRegion (t n) (y' n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      -- hextend（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
        (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Kh t y' R σ T) →
        (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
        ∀ x ∈ riemannianBallOf ((Kh (σ i)).stageMetric
            ((Kh (σ i)).activeStage (t (σ i))) (t (σ i))) (y' (σ i))
            (A / Real.sqrt (R (σ i))),
        ∀ (w : Icc (0 : ℝ) (Kh (σ i)).horizon),
          (w : ℝ) = t (σ i) - T' / R (σ i) →
        ∀ (hwt : w ≤ t (σ i))
          (Bt : BackwardPointTrace (Kh (σ i)) ((Kh (σ i)).activeStage w)
            ((Kh (σ i)).activeStage (t (σ i)))
            ((Kh (σ i)).activeStage_mono hwt) x),
          metricScalarAt ((Kh (σ i)).stageMetric ((Kh (σ i)).activeStage w) w)
            (Bt.point ((Kh (σ i)).activeStage w) le_rfl
              ((Kh (σ i)).activeStage_mono hwt)) ≤
            M * R (σ i)) →
        DepthExtendable Kh t y' R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))) →
      -- hseed（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (t n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
              (r₀ / Real.sqrt (R n)))) →
      -- hkappaC（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ (1 / 200) →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      -- hpinch（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) →
      -- hbcadC（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (v : ℝ) = t n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
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
  obtain ⟨ε₁, hε₁, hG1⟩ := exists_R4_center_family_of_notTR_gate_HCT.{u}
  obtain ⟨ε₂, hε₂, hW⟩ := hwitC_hderivC_of_hPN_anyPos_le_P6DP4E2.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro P g F ε C1 C2 Ctime pF records hcanF hacc hord hrad hε hεX hεN hεcone hC20 q hanti hδq
    recQ hrecent hfine hTD hsupA hsepWK Cst r₀ w κ Phi hr₀ hw hκ hPhi hsurvive hextend hseed
    hkappaC hpinch hbcadC Aseed hA T r hT hr
  -- recent 阈值（η_k = 1/(2(k+1))）、late recenter、HI、FRESH
  choose Trec hTrec0 hTrec using fun k : ℕ =>
    hrecent (1 / (2 * ((k : ℝ) + 1))) (by positivity)
  obtain ⟨Tδ, hTδ0, hTδ⟩ := exists_late_recenter_CXW hδq
  obtain ⟨phi, hphi, hpinK, -⟩ := hpinch_core_of_HIProp_P6HP2 F
    (fun n => by
      obtain ⟨a, ha, h⟩ := exists_initialHI_P6WR F
      exact ⟨a, ha, fun x => h n x⟩)
    (fun n => ⟨pF, ⟨records n⟩⟩)
  obtain ⟨κA, hκA, Tf, hsupK⟩ := hsupA Aseed hA
  by_contra hcon
  refine hG1 (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) F records hcanF
    (hacc.trans (min_le_left _ _)) hord hrad q Aseed (fun k => max (Trec k) (2 * Tδ)) hsepWK T r
    hT hr (fun m hm => hcon ⟨(m : ℝ), Nat.cast_nonneg m, hm⟩) ?_
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat hts hy' hcross
    hslab hclose hcompR hcmp hcmpL hgood' hbadTR hΘ h2R
  have hhsurvive := hsurvive ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhextend := hextend ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhseed := hseed ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose hcmp
    hcmpL hgood'
  have hhkappaC := hkappaC ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhpinch := hpinch ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhbcadC := hbcadC ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hsepWK' := hsepWK ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  let K : ℕ → RetainedCoreHistory.{u} := fun n =>
    (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hRr n]) tendsto_natCast_atTop_atTop
  -- hanchor0 ⇐ SLICE-BCBD2 G5 (C = 2), kernel frame (K, i, t, pm)
  have hact : ∀ n, (Kh n).activeStage (t n) = (i n).castSucc := fun n =>
    RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K n) (i n) (t n) (hslab n)
  have hRc : ∀ n, 0 < ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := fun n => by
    have h := (K n).scalar_of_incoming_P6X (i n) (hact n).symm (t n) (pm n) (y' n) (hy' n)
    rw [← h]
    linarith [hcmpL n, hRpos n]
  have hhK := hK_R4center_of_env_HCT F records hεcone hC20 q hanti recQ hfine hTD hTrec hTδ hpinK
    hphi hA hκA hsupK ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat
    hts hy' hcross hslab hclose hcompR hcmp hcmpL hgood' hΘ h2R
  have hanchor0 := ObservedHistory.hanchor0_driver_of_kernel_comparable_P6SB2 Kh (K := K) rfl t y'
    (j := i) (yG := pm) (fun n => (hslab n).1) (fun n => (hslab n).2) hy'
    (fun n => ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n)) hRc (fun _ => rfl) R hRpos
    two_pos (Filter.Eventually.of_forall fun n => (hcmp n).le) hhK
  -- window / half-depth / seed-clock data at the R4 center (r := 1)
  have hwin' : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / R n := by
    intro T' hT'
    filter_upwards [haS (T' + 1) (by linarith)] with n hn
    have h1 := hclose n
    have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
    linarith
  have hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ (t n : ℝ) := by
    filter_upwards [haS 1 one_pos, hTnS 1 one_pos] with n _ hn
    linarith [hclose n]
  have htime : ∀ᶠ n in atTop, 2 * (1 : ℝ) ^ 2 ≤ (Tn n : ℝ) :=
    Filter.Eventually.of_forall fun n => by linarith [hclock n, hone n]
  have hL2 : Tendsto (fun n => L n - 2) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-2) hL).congr fun n => by ring
  have hRr1 : Tendsto (fun n => R n * (1 : ℝ) ^ 2) atTop atTop := by simpa using hRlim
  obtain ⟨hwC, hdC⟩ := hW (eps := ε) (C1' := C1) (C2' := C2) (Ctime' := Ctime) K t y' R
    (fun _ => 1) (fun n => L n - 2) Tn aSeed haT (fun n => (hts n).trans (hsT n)) hat pT seedTrace
    hhalf htime hRpos hL2 (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hclock)
    hRr1 (a₀ := 0) le_rfl (Filter.Eventually.of_forall fun n =>
      ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc n)
    (fun n => pF.rescale_P6N (c n) (hc n)) (fun _ => 0)
    (fun n e _ => (records (ind n) e).rescale_P6M (c n) (hc n))
    (Filter.Eventually.of_forall fun n e _ b =>
      ((records (ind n) e).static b).hasCanonicalWindow_rescale_P6M (hcanF _ _ b) _ _)
    (Filter.Eventually.of_forall fun _ => hacc.trans (min_le_right _ _))
    (Filter.Eventually.of_forall fun _ => hord) (Filter.Eventually.of_forall fun _ => hrad)
    (fun T' hT' C hC => by
      filter_upwards [hsepWK' (T' + 1) (by linarith) C hC] with n hn e _ b he
      refine hn e b ?_
      have h1 := hclose n
      have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
      linarith)
    (fun T' hT' => by
      filter_upwards [hwin' T' hT'] with n hn
      linarith [hone n])
    hgood' hwin'
  obtain ⟨σd, hσd, hDE⟩ := ObservedHistory.exists_subseq_forall_depthExtendable_kappaC_P6KA Kh t y'
    R hRpos hRlim hhsurvive hanchor0 hhextend hr₀ hw hhseed hκ (fun _ => 1 / 200) hradii hhkappaC
    hPhi hhpinch hε hεX hεN (Cs := 4) (qs := fun n => 4 * R n) (fun _ => le_rfl) hwC (Cq := 4)
    (qcan := fun n => 4 * R n) (fun _ => le_rfl) hdC hhbcadC
  exact false_of_depthExtendable_of_bad_P6DP4E2 hσd hr hRpos (hDE T hT) hbadTR

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

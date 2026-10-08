import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersLocP6KT2c
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FreshRescaleP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6VolumeRescaleCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersFinalLocP6KT2c
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal

/-!
# hgap4 OPEN 合取 J15（κ on U）⇐ FRESH seed-window supply（O-CH11-HGAPADAPT / J8KAPPA G1，`_P6HA`）

KT2c 局部阈值 producer `hgapJ_loc_of_producers_P6KT2c` 的 OPEN binder `hJ15`（逐字，生成器从
`P6GapProducersLocP6KT2c.lean` l.161–264 抽取并 assert）**不需要** capped κ / traced region：J15 自带
footprint 前提（`d(seed(τ), c) + ρU ≤ A + 3`、`d(c, z) < ρU`、`τ ∈ [Tn − 1/2, Tn]`），恰是 FRESH
`KappaSeedWindowFwd_C11PK` 的 seed-window 形（K 帧 `r = 1`、footprint 系数 `A + 3`、尺度 `ρV := 1/200`）。
* FRESH 的 nr 窗口（`nr w = ρ(4w/3)`）：`w ≥ Tno − c/2 > 3·Tno/4`（`2c < Tno`）⇒ `4w/3 ≥ Tno`，
  `hanti` ⇒ `ρ(4w/3) ≤ ρ(Tno)`；`ρ(Tno) ≤ √c` ⇐ hgap 前提 `1 ≤ R ≤ ρ̃(Tn)⁻² = c·ρ(Tno)⁻²`。
* 体积：`le_ballVolume_castRescale_iff_CXSP`（`r/√c = 1`）+ `(A+3)⁻¹ ≤ A⁻¹`。
* `T ≤ t`：`Tf ≤ n + 1 ≤ Tno`，eventually。
**`hJ15_loc_of_fresh_P6HA`**（PROVED ⇐ FRESH 家族 `hfresh`（= `freshSupply_q_of_certifiedTower_P6JA`
的结论形，对每个 footprint 系数）+ `hanti`）。consumer：certified tower 环境下 `hfresh` 由
`freshSupply_q_of_certifiedTower_P6JA` 付（`hJ15_loc_of_certifiedTower_P6HA`）。
J11（κ 沿 trace）**不在本文件**：它的 footprint 需 hPN 中心的 traced region / BCBD（见 DELIVERIES 块）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6)

namespace ObservedHistory

/-- `∀ᶠ n, Tf ≤ n + 1`（`_P6HA`）。 -/
theorem eventually_le_natSucc_P6HA (Tf : ℝ) : ∀ᶠ n : ℕ in atTop, Tf ≤ (n : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge Tf
  filter_upwards [eventually_ge_atTop N] with n hn
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **FRESH 前提的 K 帧准备（`_P6HA`，PROVED）**：`c = r²`、`Tn = Tno/c`、`pT = castRescale pTo`。
`Tf/c ≤ Tn`、`2·1² < Tn`、体积 `(A+3)⁻¹ ≤ Vol(pT, 1)`（CXSP，`r/√c = 1`）、nr 窗口
`ρ(4·(c w)/3)/√c ≤ 1` on `[Tn − 1/2, Tn]`（`hanti` + `1 ≤ R ≤ ρ̃(Tn)⁻²`）。 -/
theorem freshK_prep_P6HA {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    (Ho : RetainedCoreHistory.{u}) (Tno : Icc (0 : ℝ) Ho.toHistory.horizon)
    (pTo : (Ho.toHistory.stageAt Tno).Carrier) {r : ℝ} (hr : 0 < r) {A Tf R : ℝ} (hA : 0 < A)
    (hTf : Tf ≤ (Tno : ℝ)) (h2r : 2 * r ^ 2 < (Tno : ℝ))
    (hvolo : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (Ho.toHistory.stageMetric
      (Ho.toHistory.activeStage Tno) Tno) pTo r)
    (hR1 : 1 ≤ R)
    (hRρ : R ≤ ((q.rescale_P6N (r ^ 2) (pow_pos hr 2)).neckRadius
      (Ho.rescaleTime_P6X (pow_pos hr 2) Tno) ^ 2)⁻¹) :
    Tf / r ^ 2 ≤ (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) ∧
    2 * (1 : ℝ) ^ 2 < (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) ∧
    ENNReal.ofReal ((A + 3)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume ((Ho.rescale_P6N (r ^ 2) (pow_pos hr 2)).toHistory.stageMetric
        ((Ho.rescale_P6N (r ^ 2) (pow_pos hr 2)).toHistory.activeStage
          (Ho.rescaleTime_P6X (pow_pos hr 2) Tno)) (Ho.rescaleTime_P6X (pow_pos hr 2) Tno))
        (Ho.castRescale_P6X (pow_pos hr 2) Tno pTo) 1 ∧
    ∀ w : ℝ, (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) - 1 ^ 2 / 2 ≤ w →
      w ≤ (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) →
      (fun w => (fun w => q.neckRadius (4 * w / 3)) (r ^ 2 * w) / Real.sqrt (r ^ 2)) w ≤ 1 := by
  have hc : 0 < r ^ 2 := pow_pos hr 2
  have hTnv : (Ho.rescaleTime_P6X hc Tno : ℝ) = (Tno : ℝ) / r ^ 2 := rfl
  have hcT : r ^ 2 * ((Tno : ℝ) / r ^ 2) = Tno := mul_div_cancel₀ _ hc.ne'
  have hTno0 : (0 : ℝ) ≤ (Tno : ℝ) := Tno.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hTnv]
    exact div_le_div_of_nonneg_right hTf hc.le
  · rw [hTnv, lt_div_iff₀ hc]
    linarith
  · have hr1 : r / Real.sqrt (r ^ 2) = 1 := by
      rw [Real.sqrt_sq hr.le, div_self hr.ne']
    have hvolK := (RetainedCoreHistory.le_ballVolume_castRescale_iff_CXSP hc
      (v := Tno) (p := pTo) (κ := A⁻¹) (r := r)).mpr hvolo
    rw [hr1] at hvolK
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolK
    have : (A + 3)⁻¹ ≤ A⁻¹ := inv_anti₀ hA (by linarith)
    nlinarith
  · have hρT : q.neckRadius Tno ≤ Real.sqrt (r ^ 2) := by
      have hρ0 : 0 < q.neckRadius Tno := q.neckRadius_pos _ hTno0
      have hR := hRρ
      rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X hc q, hTnv, hcT] at hR
      have hq2 : 0 < q.neckRadius Tno ^ 2 := by positivity
      have h1c : 1 ≤ r ^ 2 * (q.neckRadius Tno ^ 2)⁻¹ := hR1.trans hR
      have hsq : q.neckRadius Tno ^ 2 ≤ r ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1c hq2.le
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hq2.ne', mul_one] at this
      exact Real.le_sqrt_of_sq_le hsq
    intro w hw1 _
    change q.neckRadius (4 * (r ^ 2 * w) / 3) / Real.sqrt (r ^ 2) ≤ 1
    have hcw : (Tno : ℝ) - r ^ 2 / 2 ≤ r ^ 2 * w := by
      rw [hTnv] at hw1
      have := mul_le_mul_of_nonneg_left hw1 hc.le
      rw [mul_sub, hcT] at this
      linarith
    have hle : (Tno : ℝ) ≤ 4 * (r ^ 2 * w) / 3 := by linarith
    have hanti' := hanti (show (Tno : ℝ) ∈ Ici 0 from hTno0)
      (show 4 * (r ^ 2 * w) / 3 ∈ Ici (0 : ℝ) from le_trans hTno0 hle) hle
    rw [div_le_one (Real.sqrt_pos.mpr hc)]
    exact hanti'.trans hρT

/-- **单时刻 κ on U ⇐ FRESH（`_P6HA`，PROVED）**：K 帧 FRESH（footprint 系数 `A + 3`、`r = 1`）+
J15 的 footprint 前提（`d(seed(τ), c) + ρU ≤ A + 3`、`d(c, z) < ρU`）⇒ `κ b³ ≤ Vol(z, b)`，
`b ≤ 1/200`。stage 指标 `k` 任意（slab 内部或 final stage），只要 `activeStage τ = k`。 -/
theorem kappaU_of_fresh_at_P6HA {H : ObservedHistory.{u}} {nr : ℝ → ℝ} {A κ Tf : ℝ}
    (hsup : KappaSeedWindowFwd_C11PK nr (A + 3) κ Tf H) (Tn : Icc (0 : ℝ) H.horizon)
    (pT : (H.stageAt Tn).Carrier) (hT : Tf ≤ (Tn : ℝ)) (h2 : 2 * (1 : ℝ) ^ 2 < (Tn : ℝ))
    (hsm : GC.LongTime.hasSmallParabolicCurvature H Tn pT 1)
    (hvol : ENNReal.ofReal ((A + 3)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage Tn) Tn) pT 1)
    (hnr : ∀ w : ℝ, (Tn : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn : ℝ) → nr w ≤ 1)
    (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (hclock : (aSeed : ℝ) = Tn - 1 ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {k : Fin (H.eventCount + 1)} (c0 : (H.stage k).Carrier) (U : Set (H.stage k).Carrier)
    {a t ρU : ℝ} (ha : (Tn : ℝ) - 1 ^ 2 / 2 ≤ a) (ht : t ≤ (Tn : ℝ))
    (τ : Icc (0 : ℝ) H.horizon) (haτ : a ≤ (τ : ℝ)) (hτt : (τ : ℝ) ≤ t)
    (hact : H.activeStage τ = k)
    (hUρ : ∀ z ∈ U, ∀ zz cc : (H.stageAt τ).Carrier, HEq zz z → HEq cc c0 →
      riemannianEDistOf (H.stageMetric (H.activeStage τ) τ) cc zz < ENNReal.ofReal ρU)
    (hfoot : ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ Tn), ∀ cc : (H.stageAt τ).Carrier, HEq cc c0 →
      riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
          (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          cc + ENNReal.ofReal ρU ≤ ENNReal.ofReal ((A + 3) * 1))
    (z : (H.stage k).Carrier) (hz : z ∈ U) (zz : (H.stageAt τ).Carrier) (hzz : HEq zz z)
    (b : ℝ) (hb : 0 < b) (hb200 : b ≤ 1 / 200)
    (hctrl : H.isParabolicallyRmControlledBall τ zz b) (hκ : 0 < κ) :
    ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt τ).Carrier (H.stageMetric (H.activeStage τ) τ)
        (riemannianBallOf (H.stageMetric (H.activeStage τ) τ) zz b) := by
  have hav : aSeed ≤ τ := by
    change (aSeed : ℝ) ≤ (τ : ℝ)
    rw [hclock]
    linarith
  have hvt : τ ≤ Tn := by
    change (τ : ℝ) ≤ (Tn : ℝ)
    linarith
  have hτw : (Tn : ℝ) - 1 ^ 2 / 2 ≤ (τ : ℝ) := by linarith
  obtain ⟨cc, hcc⟩ := ObservedHistory.exists_heq_stageAt_P6JW H hact c0
  have hfp := hfoot hav hvt cc hcc
  have hU := hUρ z hz zz cc hzz hcc
  have hball' : zz ∈ riemannianBallOf (H.stageMetric (H.activeStage τ) τ)
      (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav) (H.activeStage_mono hvt))
      ((A + 3) * 1) := by
    change riemannianEDistOf _ _ zz < ENNReal.ofReal ((A + 3) * 1)
    have hne : riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
        (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav) (H.activeStage_mono hvt))
        cc ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hfp)
    refine lt_of_le_of_lt (riemannianEDistOf_triangle _ _ cc zz) ?_
    exact lt_of_lt_of_le (ENNReal.add_lt_add_left hne hU) hfp
  have hb100 : b < 1 / 100 := by linarith
  have key := hsup Tn pT 1 hT h2 hsm hvol hnr aSeed haT hclock seedTrace τ hav hvt hτw zz hball'
    b hb.le hb100 hctrl
  rw [← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul hκ.le]
  exact key

/-- **J15 ⇐ FRESH（`_P6HA`，PROVED ⇐ FRESH 家族 + `hanti`）**：结论 =
KT2c event producer `hgapJ_loc_of_producers_P6KT2c` 的 `hJ15` 逐字。
`κ` = FRESH 在 footprint 系数 `A + 3` 处的 κ，`ρV := 1/200`。 -/
theorem hJ15_loc_of_fresh_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) {Ctime₀ : ℝ≥0} {a₀ : ℝ}
    {T₀ Qt : ℕ → ℝ}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) →
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt Qs p recordsK _ _ _ _ _ _ _ _ _ _
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep : ∀ᶠ n : ℕ in atTop, _ := (eventually_le_natSucc_P6HA Tf).mono fun n hn =>
    freshK_prep_P6HA hanti (Ho n) (Tno n) (pTo n) (hr n) (by linarith : (0 : ℝ) < A)
      (hn.trans (hk n)) (h2r n) (hvolo n)
      (by have := hRr n; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (hRρ n)
  refine ⟨κ, fun _ => 1 / 200, hκ, hradii, ?_⟩
  filter_upwards [hprep] with n hn
  obtain ⟨hT, h2, hvol, hnr⟩ := hn
  intro j c0 U a t ρU ha ht hUρ hfoot τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hctrl
  exact kappaU_of_fresh_at_P6HA (hsupK n) (Tn n) (pT n) hT h2 (hsm n) hvol hnr (aSeed n) (haT n)
    (hclock n) (seedTrace n) c0 U ha ht τ haτ hτt
    ((K n).activeStage_eq_of_mem_slab_P6X j τ hjτ.le hτj) (hUρ τ haτ hτt hjτ hτj)
    (hfoot τ haτ hτt hjτ hτj) z hz zz hzz b hb hbρ hctrl hκ

/-- **J15 ⇐ FRESH（`_P6HA`，PROVED ⇐ FRESH 家族 + `hanti`）**：结论 =
KT2c J8 producer `hgapJ8_loc_of_producers_P6KT2c` 的 `hJ15`（`8·R` hgood、GT6 常数） 逐字。
`κ` = FRESH 在 footprint 系数 `A + 3` 处的 κ，`ρV := 1/200`。 -/
theorem hJ15_8_loc_of_fresh_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) {Ctime₀ : ℝ≥0} {a₀ : ℝ}
    {T₀ Qt : ℕ → ℝ}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) →
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt Qs p recordsK _ _ _ _ _ _ _ _ _ _
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep : ∀ᶠ n : ℕ in atTop, _ := (eventually_le_natSucc_P6HA Tf).mono fun n hn =>
    freshK_prep_P6HA hanti (Ho n) (Tno n) (pTo n) (hr n) (by linarith : (0 : ℝ) < A)
      (hn.trans (hk n)) (h2r n) (hvolo n)
      (by have := hRr n; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (hRρ n)
  refine ⟨κ, fun _ => 1 / 200, hκ, hradii, ?_⟩
  filter_upwards [hprep] with n hn
  obtain ⟨hT, h2, hvol, hnr⟩ := hn
  intro j c0 U a t ρU ha ht hUρ hfoot τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hctrl
  exact kappaU_of_fresh_at_P6HA (hsupK n) (Tn n) (pT n) hT h2 (hsm n) hvol hnr (aSeed n) (haT n)
    (hclock n) (seedTrace n) c0 U ha ht τ haτ hτt
    ((K n).activeStage_eq_of_mem_slab_P6X j τ hjτ.le hτj) (hUρ τ haτ hτt hjτ hτj)
    (hfoot τ haτ hτt hjτ hτj) z hz zz hzz b hb hbρ hctrl hκ

/-- **J15 ⇐ FRESH（`_P6HA`，PROVED ⇐ FRESH 家族 + `hanti`）**：结论 =
KT2c final producer 的 `hJ15F`（slab 内部 + final stage 两合取） 逐字。
`κ` = FRESH 在 footprint 系数 `A + 3` 处的 κ，`ρV := 1/200`。 -/
theorem hJ15F_loc_of_fresh_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {a₀ : ℝ}
    {T₀ Qt : ℕ → ℝ}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
            (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
        (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt Qs p recordsK _ _ _ _ _ _ _
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep : ∀ᶠ n : ℕ in atTop, _ := (eventually_le_natSucc_P6HA Tf).mono fun n hn =>
    freshK_prep_P6HA hanti (Ho n) (Tno n) (pTo n) (hr n) (by linarith : (0 : ℝ) < A)
      (hn.trans (hk n)) (h2r n) (hvolo n)
      (by have := hRr n; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (hRρ n)
  refine ⟨κ, fun _ => 1 / 200, hκ, hradii, ?_, ?_⟩
  · filter_upwards [hprep] with n hn
    obtain ⟨hT, h2, hvol, hnr⟩ := hn
    intro j c0 U a t ρU ha ht hUρ hfoot τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hctrl
    exact kappaU_of_fresh_at_P6HA (hsupK n) (Tn n) (pT n) hT h2 (hsm n) hvol hnr (aSeed n) (haT n)
      (hclock n) (seedTrace n) c0 U ha ht τ haτ hτt
      ((K n).activeStage_eq_of_mem_slab_P6X j τ hjτ.le hτj) (hUρ τ haτ hτt hjτ hτj)
      (hfoot τ haτ hτt hjτ hτj) z hz zz hzz b hb hbρ hctrl hκ
  · filter_upwards [hprep] with n hn
    obtain ⟨hT, h2, hvol, hnr⟩ := hn
    intro c0 U a t ρU ha ht hUρ hfoot τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hctrl
    exact kappaU_of_fresh_at_P6HA (hsupK n) (Tn n) (pT n) hT h2 (hsm n) hvol hnr (aSeed n) (haT n)
      (hclock n) (seedTrace n) c0 U ha ht τ haτ hτt
      ((Kh n).activeStage_eq_last_of_time_last_le τ hjτ.le) (hUρ τ haτ hτt hjτ hτj)
      (hfoot τ haτ hτt hjτ hτj) z hz zz hzz b hb hbρ hctrl hκ

/-- **J15 ⇐ FRESH（`_P6HA`，PROVED ⇐ FRESH 家族 + `hanti`）**：结论 =
KT2c final J8 producer 的 `hJ15F8` 逐字。
`κ` = FRESH 在 footprint 系数 `A + 3` 处的 κ，`ρV := 1/200`。 -/
theorem hJ15F8_loc_of_fresh_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {a₀ : ℝ}
    {T₀ Qt : ℕ → ℝ}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
            (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
        (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt Qs p recordsK _ _ _ _ _ _ _
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep : ∀ᶠ n : ℕ in atTop, _ := (eventually_le_natSucc_P6HA Tf).mono fun n hn =>
    freshK_prep_P6HA hanti (Ho n) (Tno n) (pTo n) (hr n) (by linarith : (0 : ℝ) < A)
      (hn.trans (hk n)) (h2r n) (hvolo n)
      (by have := hRr n; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (hRρ n)
  refine ⟨κ, fun _ => 1 / 200, hκ, hradii, ?_, ?_⟩
  · filter_upwards [hprep] with n hn
    obtain ⟨hT, h2, hvol, hnr⟩ := hn
    intro j c0 U a t ρU ha ht hUρ hfoot τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hctrl
    exact kappaU_of_fresh_at_P6HA (hsupK n) (Tn n) (pT n) hT h2 (hsm n) hvol hnr (aSeed n) (haT n)
      (hclock n) (seedTrace n) c0 U ha ht τ haτ hτt
      ((K n).activeStage_eq_of_mem_slab_P6X j τ hjτ.le hτj) (hUρ τ haτ hτt hjτ hτj)
      (hfoot τ haτ hτt hjτ hτj) z hz zz hzz b hb hbρ hctrl hκ
  · filter_upwards [hprep] with n hn
    obtain ⟨hT, h2, hvol, hnr⟩ := hn
    intro c0 U a t ρU ha ht hUρ hfoot τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hctrl
    exact kappaU_of_fresh_at_P6HA (hsupK n) (Tn n) (pT n) hT h2 (hsm n) hvol hnr (aSeed n) (haT n)
      (hclock n) (seedTrace n) c0 U ha ht τ haτ hτt
      ((Kh n).activeStage_eq_last_of_time_last_le τ hjτ.le) (hUρ τ haτ hτt hjτ hτj)
      (hfoot τ haτ hτt hjτ hτj) z hz zz hzz b hb hbρ hctrl hκ

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

universe v

/-- **`hfresh` 由 certified tower 环境付（`_P6HA`，PROVED）**：`freshSupply_q_of_certifiedTower_P6JA`
对每个 footprint 系数 `A > 0` 给 `κ, Tf`（丢掉 `0 < Tf`）。 -/
theorem hfresh_of_certifiedTower_P6HA {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{v}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hP3 : CollarWindowSupply_C11E.{v} pB) (hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{v})
    (hacc₀ : pB.modelAccuracy ≤
      epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P) :
    ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory := by
  intro A hA
  obtain ⟨κ, hκ, Tf, -, h⟩ :=
    freshSupply_q_of_certifiedTower_P6JA T hcert F hF q hq hP3 hprof hacc₀ hA
  exact ⟨κ, hκ, Tf, h⟩

/-- consumer：certified tower 环境 + `hanti` ⇒ KT2c event producer 的 `hJ15` 槽（逐字）。 -/
example {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{v}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hP3 : CollarWindowSupply_C11E.{v} pB) (hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{v})
    (hacc₀ : pB.modelAccuracy ≤
      epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P)
    (hanti : AntitoneOn q.neckRadius (Set.Ici 0)) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) {Ctime₀ : ℝ≥0} {a₀ : ℝ}
    {T₀ Qt : ℕ → ℝ} : True := by
  have h := ObservedHistory.hJ15_loc_of_fresh_P6HA (F := F) (ε := ε) (C1 := C1) (C2 := C2)
    (Ctime := Ctime) Cb Rn ζ δ₀ m₀ (Ctime₀ := Ctime₀) (a₀ := a₀) (T₀ := T₀) (Qt := Qt) hanti
    (hfresh_of_certifiedTower_P6HA T hcert F hF q hq hP3 hprof hacc₀)
  have h8 := ObservedHistory.hJ15_8_loc_of_fresh_P6HA (F := F) (ε := ε) (C1 := C1) (C2 := C2)
    (Ctime := Ctime) Cb Rn ζ δ₀ m₀ (Ctime₀ := Ctime₀) (a₀ := a₀) (T₀ := T₀) (Qt := Qt) hanti
    (hfresh_of_certifiedTower_P6HA T hcert F hF q hq hP3 hprof hacc₀)
  exact trivial

end GC.LongTime.Ch11

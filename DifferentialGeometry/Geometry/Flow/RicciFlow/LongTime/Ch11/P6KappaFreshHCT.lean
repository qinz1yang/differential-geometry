import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaFreshP6F4

/-!
# FRESH κ / footprint 的天花板透传孪生（O-CH11-HCEILT G5 P1–P2，后缀 `_HCT`）

`hkappaL_of_fresh_P6F4` / `hfpL_of_gate_P6F4` 逐字（加隐式 `qc`），
`hceil : ∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹`
逐 frame 透传（gate 块后插入；证明中 `hdσ` 后插 `hceil`）。
槽形收窄 = 义务变弱（§0.2/§0.3），旧 → 新由忽略 `hceil` 得。生成器 gen/genP.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- **G2（`_P6F4`，PROVISIONAL：`hsupK`（J11 重标度 adapter）、`hfpL`（DIST 局部 footprint））**：结论 =
FOOT3 `hkappaL` + gate 前缀（`2 < Tn`、nr 兼容、top gate `hdσ`），`κ` 与 FRESH 同一个；`ρ_k := 1/200`。 -/
theorem hkappaL_of_fresh_HCT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Aseed : ℝ}
    {nr : ℝ → ℝ} {qc : CutoffParameters} {κ Tf : ℝ} (hAs : 0 < Aseed) (hκ : 0 < κ)
    (hsupK : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
      KappaSeedWindowFwd_C11PK (fun w => nr (c k * w) / Real.sqrt (c k)) (Aseed + 7) κ
        (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory)
    (hfpL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
            nr (c k * w) / Real.sqrt (c k) ≤ 1) →
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
          (∀ k, R k ≤ ((qc.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : Icc (0 : ℝ) (Kh k).horizon,
            t - T / R k ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
            (Kh k).time (i k).castSucc < τ → (τ : ℝ) < (Kh k).time (i k).succ →
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (zz : ((Kh k).stageAt τ).Carrier), HEq zz z →
            ∀ (hav : aSeed k ≤ τ) (hvt : τ ≤ Tn k),
              zz ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
                ((seedTrace k).point ((Kh k).activeStage τ) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) ((Aseed + 7) * 1)) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
            nr (c k * w) / Real.sqrt (c k) ≤ 1) →
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
          (∀ k, R k ≤ ((qc.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∃ ρ : ℕ → ℝ, Tendsto (fun k => ρ k * Real.sqrt (R k)) atTop atTop ∧
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : Icc (0 : ℝ) (Kh k).horizon,
              t - T / R k ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh k).time (i k).castSucc < τ → (τ : ℝ) < (Kh k).time (i k).succ →
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (zz : ((Kh k).stageAt τ).Carrier), HEq zz z →
              ∀ (b : ℝ), 0 < b → b ≤ ρ k →
                (Kh k).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh k).stageAt τ).Carrier
                    ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
                    (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage τ) τ) zz b) := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R
    hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  refine ⟨fun _ => 1 / 200, hradii, ?_⟩
  have hfp := hfpL T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS
    seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  have hTf : ∀ᶠ k in atTop, Tf ≤ c k * (Tn k : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈Tf⌉₊] with k hk
    have h1 := hTc k
    have h2 : (⌈Tf⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.le_ceil Tf]
  filter_upwards [hfp, hTf, hTnS (2 * T) (by positivity)] with k hfk hTfk hwk
  intro p' q hq hcross
  have hRk := hRpos k
  have hTR : 0 < T / R k := div_pos hT hRk
  filter_upwards [hfk p' q hq hcross,
    Ioo_mem_nhdsLT (show (Kh k).time (i k).succ - T / R k < (Kh k).time (i k).succ by linarith)]
    with t ht htI
  intro τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb0 hbρ hctrl
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hσT : (σ k : ℝ) ≤ Tn k := Subtype.coe_le_coe.mpr (hsT k)
  have h2T : 2 * T / R k = T / R k + T / R k := by ring
  have hτw : (Tn k : ℝ) - 1 ^ 2 / 2 ≤ τ := by
    have := htI.1
    linarith
  have hτT : (τ : ℝ) ≤ Tn k := by linarith [htI.2]
  have hav : aSeed k ≤ τ := Subtype.coe_le_coe.mp (by rw [hclock k]; linarith)
  have hvt : τ ≤ Tn k := Subtype.coe_le_coe.mp hτT
  have hTn' : Tf / c k ≤ (Tn k : ℝ) := by
    rw [div_le_iff₀ (hc k)]
    linarith [mul_comm (c k) (Tn k : ℝ)]
  have hvolA : ENNReal.ofReal ((Aseed + 7)⁻¹ * 1 ^ 3) ≤
      ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hvol k)
    have : (Aseed + 7)⁻¹ ≤ Aseed⁻¹ := inv_anti₀ hAs (by linarith)
    simpa using this
  have hK := hsupK ind c hc k (Tn k) (pT k) 1 hTn' (by linarith [hTn2 k]) (hsm k) hvolA
    (hnrS k) (aSeed k) (haT k) (hclock k) (seedTrace k) τ hav hvt hτw zz
    (ht τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz hav hvt) b hb0.le (by linarith) hctrl
  rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow hb0.le] at hK
  exact hK

/-- **G2b（`_P6F4`，PROVISIONAL：`hmargin`（BCDT 逐字，FOOT2 `hmargin_noD_P6F2`）、`hdistL`（DIST 短窗畸变））**：
`hfpL`（G2 的局部 footprint binder）⇐ top gate `hdσ`（前缀）+ `hmargin`（`d_t(O, p′) ≤ d_σ + 1`）+
`d_t(p′, z) < r/√R_k ≤ 1` + 短窗畸变 `hdistL`（`d_τ(O, z) ≤ d_t(O, z) + 1`，`τ ∈ [t − T/R_k, t]`）；
`(Aseed + 3) + 3 < Aseed + 7`，`activeStage τ = i⁻`（`activeStage_eq_castSucc_C11PB`）把 slab 形距离搬到
  FRESH 球。
`hdistL` 的 producer 路线：`ObservedHistory.smooth_distance_distortion_C11D`（stage `i⁻`，端点 `ℓ`-球
`Ric ≤ 3/ℓ²`，`ℓ = ℓ₀/√R_k` ⇒ 畸变 `≤ 8T/(ℓ₀√R_k) → 0`），端点 Ricci 同 PBKAPPA
`PickedBallEndpointRicci_C11PK`（owner DIST / PICKBALL）。 -/
theorem hfpL_of_gate_HCT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Aseed : ℝ}
    {nr : ℝ → ℝ} {qc : CutoffParameters} (hAs : 0 < Aseed)
    (hmargin :
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
                ENNReal.ofReal δ)
    (hdistL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
            nr (c k * w) / Real.sqrt (c k) ≤ 1) →
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
          (∀ k, R k ≤ ((qc.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)),
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : ℝ,
            t - T / R k ≤ τ → τ ≤ t → (Kh k).time (i k).castSucc < τ →
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric τ)
                  ((seedTrace k).point (i k).castSucc h1 h2) z ≤
                riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
                  ((seedTrace k).point (i k).castSucc h1 h2) z + ENNReal.ofReal 1) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
            nr (c k * w) / Real.sqrt (c k) ≤ 1) →
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
          (∀ k, R k ≤ ((qc.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : Icc (0 : ℝ) (Kh k).horizon,
            t - T / R k ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
            (Kh k).time (i k).castSucc < τ → (τ : ℝ) < (Kh k).time (i k).succ →
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (zz : ((Kh k).stageAt τ).Carrier), HEq zz z →
            ∀ (hav : aSeed k ≤ τ) (hvt : τ ≤ Tn k),
              zz ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
                ((seedTrace k).point ((Kh k).activeStage τ) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) ((Aseed + 7) * 1) := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R
    hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  have hma := hmargin ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hdi := hdistL T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS
    seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hma, hdi, hdσ, hRlim.eventually_ge_atTop (r ^ 2), haS 1 one_pos]
    with k hmk hdk hdσk hRr2 haSk
  intro p' q hq hcross
  have hRk := hRpos k
  have haσ : (aSeed k : ℝ) < σ k := by
    have := div_pos one_pos hRk
    linarith
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hσT : (σ k : ℝ) ≤ Tn k := Subtype.coe_le_coe.mpr (hsT k)
  have h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc :=
    (Kh k).activeStage_le_castSucc_P6HE (i k) (aSeed k) (by rw [← hσs]; exact haσ)
  have h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k) :=
    (Kh k).le_activeStage (Tn k) (i k).castSucc (by rw [← hσs] at hcs; linarith)
  have hsR : r ≤ Real.sqrt (R k) := by
    have h := Real.sqrt_le_sqrt hRr2
    rwa [Real.sqrt_sq hr.le] at h
  have hr1 : r / Real.sqrt (R k) ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr hRk)]
    exact hsR
  have hdσ' := le_trans le_self_add hdσk
  filter_upwards [hmk p' q hq hcross h1 h2 1 one_pos, hdk p' q hq hcross h1 h2] with t hmt hdt
  intro τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz hav hvt
  have hact : (Kh k).activeStage τ = (i k).castSucc :=
    ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).activeStage_eq_castSucc_C11PB
      (i k) τ hτ3 hτ4
  have key : ∀ (j : Fin ((Kh k).eventCount + 1)) (_hj : (Kh k).activeStage τ = j)
      (h1' : (Kh k).activeStage (aSeed k) ≤ j) (h2' : j ≤ (Kh k).activeStage (Tn k))
      (z' : ((Kh k).stage j).Carrier), HEq zz z' →
      riemannianEDistOf ((Kh k).stageMetric j τ) ((seedTrace k).point j h1' h2') z' <
        ENNReal.ofReal ((Aseed + 7) * 1) →
      zz ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
        ((seedTrace k).point ((Kh k).activeStage τ) ((Kh k).activeStage_mono hav)
          ((Kh k).activeStage_mono hvt)) ((Aseed + 7) * 1) := by
    intro j hj
    subst hj
    intro h1' h2' z' hzz' hd'
    rw [eq_of_heq hzz']
    exact hd'
  refine key (i k).castSucc hact h1 h2 z hzz ?_
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rw [ObservedHistory.stageMetric_castSucc_apply] at hmt
  have hz' : riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t) p' z ≤
      ENNReal.ofReal 1 := le_trans (le_of_lt hz) (ENNReal.ofReal_le_ofReal hr1)
  have htri := riemannianEDistOf_triangle (((Kh k).event (i k)).incoming.flow.base.metric t)
    ((seedTrace k).point (i k).castSucc h1 h2) p' z
  have hd := hdt τ hτ1 hτ2 hτ3 z hz
  calc riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric τ)
        ((seedTrace k).point (i k).castSucc h1 h2) z
      ≤ ENNReal.ofReal ((Aseed + 3) * 1) + ENNReal.ofReal 1 + ENNReal.ofReal 1 +
          ENNReal.ofReal 1 := by
        refine hd.trans (add_le_add (htri.trans (add_le_add (hmt.trans ?_) hz')) le_rfl)
        exact add_le_add hdσ' le_rfl
    _ = ENNReal.ofReal ((Aseed + 3) * 1 + 1 + 1 + 1) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> linarith
    _ < ENNReal.ofReal ((Aseed + 7) * 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

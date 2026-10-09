import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistortionLocalP6DL

/-!
# DISTLA consumers（O-CH11-DISTLA G2/G3，后缀 `_P6DL`）

`P6DistortionLocalP6DL` 的 G1/G1c/G2 喂三处 consumer；**两条独立结论**（lead 22:5x / R-C11-18 Q2.3）：
1. **小球形 PROVED**（`r ≤ r* := (2C2′Λ₀)^{-1/2}`、`T ≤ T* := 1/(4C2′Λ₀·Ctime′)`）：
   `hdistL_small_P6DL`——FOOT4 `hdistL` 内层（固定 `k`、`t`）的 `d_τ(O, z) ≤ d_t(O, z) + 1`，
   `z ∈ B_t(p′, ρ)`、`τ ∈ [t − T/R, t]`；输入 = hgood + K0 + HI + 顶点值 `R_t(p′) ≤ Mb` + 顶时刻余量。
2. **大球形 BLOCKED**（任意 `r`、任意 `T`；FOOT4 `hdistL`/`hdistLA` 的 `∀ T r`、J10WIRE2 `hballT` 的
   `Cball(r)`）= 空间 bounded curvature at bounded distance（任意半径的空间 BCD 供给）+ 深窗格点
   anchor；witness 链只到 `r*`（clopen spread 的 witness 半径 `≥ R^{-1/2}`），ODE 只到 `T*`。FOOT3 kernel
   `terminal_scalar_bound_local_P6F3` 在其 `∃ Rad Bw` 处实例化 `r = 2·Rad`、`T = 3·Bw`（不可调小，FOOT4 G3），
   J10WIRE2 `r = max (2Rad) 1 ≥ 1 > r*` ⇒ **consumer 不能只用小球形**。repair owner = guarded ShortSLT /
   半径 bootstrap（KSWEXIT）+ 格点 anchor（BCDBOOT）。
* PBKAPPA：`pickedBallFootprint_of_witness_P6DL` 直接给 `PickedBallFootprint_C11PK`（`hfoot`），**绕过**
  `PickedBallEndpointRicci_C11PK` binder（其唯一用途是 footprint）；hpick 由 G1b 给（example）。
* PICKSEL：`hLR_of_witness_scale_P6DL`——witness 尺度 `ℓ = ℓ₀/√R_n` 满足 `pickedCenterFootprint_P6PS` 门槛
  `4(Dc + 8θ/(ℓ√R_n)) ≤ 3L` 当且仅当 `4(Dc + 8θ/ℓ₀) ≤ 3L`（`L → ∞` 时 eventually），不需 `L²R_n` 曲率；
  中心 footprint 本身 = `footprint_lt_of_witness_P6DL`（`Lv = L/4 + Dc` = `seedDist_slice_P6PS` 输出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness I3)

section Footprint

/-- **G2′ `footprint_lt_of_witness_P6DL`（`_P6DL`，PROVED）**：G2 + top gate
`hdσ : d_σ + (L + 1)/√R ≤ A·r` ⇒ 窗口 footprint `d_s(O, x) < A·r`（PBKAPPA / PICKSEL / FOOT4 `hfpL` 的
宏观形）。 -/
theorem ObservedHistory.footprint_lt_of_witness_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (y : (H.stageAt σ).Carrier) {R L Lc A : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (x : (H.stage j.castSucc).Carrier)
    {τ v M ℓ K Lv : ℝ} (hτ1 : H.time j.castSucc < τ) (hτv : τ ≤ v) (hv2 : v < H.time j.succ)
    (haτ : (aSeed : ℝ) ≤ τ) (hvσ : v ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (hM : 0 < M) (hCgM : Cg * R ≤ M) (hC2 : 1 ≤ C2')
    (hxv : (H.event j).incoming.flow.scalar v x ≤ M)
    (hbud : (Ctime' : ℝ) * M * (v - τ) ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓM : ℓ ^ 2 * (2 * C2' * (2 * M)) ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) * (2 * M) ≤ K)
    (hMτ : 1 ≤ 2 * M * τ)
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc) (hLv0 : 0 ≤ Lv)
    (hdv : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lv / Real.sqrt R))
    (hdrift : Lv / Real.sqrt R + (8 / ℓ) * (v - τ) < Lc / Real.sqrt R)
    (hdσ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal ((L + 1) / Real.sqrt R) ≤
      ENNReal.ofReal (A * r)) :
    ∀ s ∈ Icc τ v, riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) x < ENNReal.ofReal (A * r) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hfin : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)
  have hfp := H.footprint_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y hR hgood
    j h1 h2 x hτ1 hτv hv2 haτ hvσ hLτ hM hCgM hC2 hxv hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ hLc hLc0
    hLv0 hdv hdrift hfin
  have hlt : Lc / Real.sqrt R < (L + 1) / Real.sqrt R := by
    rw [div_lt_div_iff_of_pos_right hsR]
    have : Lc / Real.sqrt R ≤ L / Real.sqrt R := by linarith
    rw [div_le_div_iff_of_pos_right hsR] at this
    linarith
  intro s hs
  calc _ ≤ riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R) := hfp s hs
    _ < riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal ((L + 1) / Real.sqrt R) :=
        ENNReal.add_lt_add_left hfin
          ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (div_nonneg hLc0 hsR.le) hlt)).2 hlt)
    _ ≤ ENNReal.ofReal (A * r) := hdσ

end Footprint

section PBKAPPA

/-- **G3 PBKAPPA `hfoot` ⇐ witness（`_P6DL`，PROVED；OPEN 1 绕过）**：
`PickedBallFootprint_C11PK β Rad K j v w O (A·r)` 由 hgood（SC2 形）+ K0 + HI +
hpick `PickedBallTop_C11PB Λ Rad`（G1b 给）+ 中心 Good
`d_v(O, w) ≤ d_σ + Lw/√R` + top gate `hdσ` + 数值（`M = Λq`、`v − τ ≤ β/q`）。U 球点 `z` 的顶时刻距离
`≤ d_σ + (Lw + Rad)/√R`（`R ≤ q`）。不需要 `PickedBallEndpointRicci_C11PK`。 -/
theorem pickedBallFootprint_of_witness_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (K : RetainedCoreHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon}
    (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t) (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {R L Lc A : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (j : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn) (v : ℝ) (hv2 : v < K.time j.succ)
    (hvσ : v ≤ σ) (w : (K.stage j.castSucc).Carrier) {β Rad Λ ℓ Kc Lw : ℝ}
    (hRq : R ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ) (hC2 : 1 ≤ C2')
    (hpick : PickedBallTop_C11PB Λ Rad K j v w) (hRad0 : 0 ≤ Rad) (hLw0 : 0 ≤ Lw)
    (hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) w ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lw / Real.sqrt R))
    (hCgM : Cg * R ≤ Λ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime' : ℝ) * (Λ * (K.toHistory.event j).incoming.flow.scalar v w) *
      (β / (K.toHistory.event j).incoming.flow.scalar v w) ≤ 1 / 2)
    (hℓ : 0 < ℓ)
    (hℓM : ℓ ^ 2 * (2 * C2' * (2 * (Λ * (K.toHistory.event j).incoming.flow.scalar v w))) ≤ 1)
    (hℓr : ℓ ≤ r / 50) (hKℓ : Kc * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ Kc)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) *
      (2 * (Λ * (K.toHistory.event j).incoming.flow.scalar v w)) ≤ Kc)
    (hMτ : 1 ≤ 2 * (Λ * (K.toHistory.event j).incoming.flow.scalar v w) *
      (v - β / (K.toHistory.event j).incoming.flow.scalar v w))
    (haβ : (aSeed : ℝ) ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hLβ : (σ : ℝ) - L ^ 2 / R ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc)
    (hdrift : (Lw + Rad) / Real.sqrt R +
      (8 / ℓ) * (β / (K.toHistory.event j).incoming.flow.scalar v w) < Lc / Real.sqrt R)
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt R) ≤ ENNReal.ofReal (A * r)) :
    PickedBallFootprint_C11PK β Rad K j v w (seedTrace.point j.castSucc h1 h2)
      (ENNReal.ofReal (A * r)) := by
  set q := (K.toHistory.event j).incoming.flow.scalar v w with hqdef
  intro z hz τ hτ1 hτ2 hτ3
  have hq : 0 < q := hR.trans_le hRq
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsq : Real.sqrt R ≤ Real.sqrt q := Real.sqrt_le_sqrt hRq
  have hvτ : v - τ ≤ β / q := by linarith
  have hRadq : Rad / Real.sqrt q ≤ Rad / Real.sqrt R :=
    div_le_div_of_nonneg_left hRad0 hsR hsq
  have hz' : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) w z <
      ENNReal.ofReal (Rad / Real.sqrt q) := hz
  have hdv : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) z ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((Lw + Rad) / Real.sqrt R) := by
    calc _ ≤ riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
            (seedTrace.point j.castSucc h1 h2) w +
          riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) w z :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lw / Real.sqrt R)) +
          ENNReal.ofReal (Rad / Real.sqrt R) :=
          add_le_add hw (hz'.le.trans (ENNReal.ofReal_le_ofReal hRadq))
      _ = _ := by
          rw [add_assoc, ← ENNReal.ofReal_add (div_nonneg hLw0 hsR.le)
            (div_nonneg hRad0 hsR.le), add_div]
  have hbud' : (Ctime' : ℝ) * (Λ * q) * (v - τ) ≤ 1 / 2 := by
    have hCM : (0 : ℝ) ≤ Ctime' * (Λ * q) := mul_nonneg Ctime'.coe_nonneg (by positivity)
    exact (mul_le_mul_of_nonneg_left hvτ hCM).trans hbud
  have hMτ' : 1 ≤ 2 * (Λ * q) * τ := by
    have := mul_le_mul_of_nonneg_left hτ1 (by positivity : (0 : ℝ) ≤ 2 * (Λ * q))
    linarith
  have hdrift' : (Lw + Rad) / Real.sqrt R + (8 / ℓ) * (v - τ) < Lc / Real.sqrt R := by
    have := mul_le_mul_of_nonneg_left hvτ (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hℓ.le)
    linarith
  exact K.toHistory.footprint_lt_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y
    hR hgood j h1 h2 z hτ3 hτ2 hv2 (haβ.trans hτ1) hvσ (hLβ.trans hτ1) (by positivity) hCgM hC2
    (hpick z hz) hbud' hℓ hℓM hℓr hKℓ hKr hKC hMτ' hLc hLc0 (add_nonneg hLw0 hRad0) hdv hdrift'
    hdσ τ ⟨le_rfl, hτ2⟩

/-- **consumer（G1b + G3 ⇒ PBKAPPA hκ）**：hpick 由 `pickedBallTop_of_witness_spread_P6DL`（witness 半
`PickedBallWitness_C11PB`，`Λ = 2C2′Λ₀`、`Rad²·2C2′Λ₀ ≤ 1`）给，footprint 由
`pickedBallFootprint_of_witness_P6DL` 给，喂 `pickedBallKappa_of_fresh_C11PK`（FRESH supply）⇒
`PickedBallKappa_C11PB`。`PickedBallEndpointRicci_C11PK` 不出现。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ} {nr : ℝ → ℝ} {Aκ κ Tκ : ℝ}
    (K : RetainedCoreHistory.{u}) (hWF : KappaSeedWindowFwd_C11PK nr Aκ κ Tκ K.toHistory)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon}
    (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (hTn : Tκ ≤ (Tn : ℝ)) (htime : 2 * r ^ 2 < (Tn : ℝ))
    (hvol : ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤
      ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage Tn) Tn) pT r)
    (hnr : ∀ w : ℝ, (Tn : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn : ℝ) → nr w ≤ r)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t) (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {R L Lc : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (j : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn) (v : ℝ) (hv2 : v < K.time j.succ)
    (hvσ : v ≤ σ) (w : (K.stage j.castSucc).Carrier) {β Rad ρ Λ₀ qthr ℓ Kc Lw : ℝ}
    (hRq : R ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hC2 : 1 ≤ C2') (hΛ₀ : 1 ≤ Λ₀)
    (hWit : PickedBallWitness_C11PB Rad qthr eps C1' C2' K j v w)
    (hthr : qthr ≤ Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hRadΛ : Rad ^ 2 * (2 * C2' * Λ₀) ≤ 1) (hRad0 : 0 ≤ Rad) (hLw0 : 0 ≤ Lw)
    (hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) w ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lw / Real.sqrt R))
    (hCgM : Cg * R ≤ 2 * C2' * Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime' : ℝ) * (2 * C2' * Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w) *
      (β / (K.toHistory.event j).incoming.flow.scalar v w) ≤ 1 / 2)
    (hℓ : 0 < ℓ)
    (hℓM : ℓ ^ 2 * (2 * C2' *
      (2 * (2 * C2' * Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w))) ≤ 1)
    (hℓr : ℓ ≤ r / 50) (hKℓ : Kc * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ Kc)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) *
      (2 * (2 * C2' * Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w)) ≤ Kc)
    (hMτ : 1 ≤ 2 * (2 * C2' * Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w) *
      (v - β / (K.toHistory.event j).incoming.flow.scalar v w))
    (haβ : (aSeed : ℝ) ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hLβ : (σ : ℝ) - L ^ 2 / R ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc)
    (hdrift : (Lw + Rad) / Real.sqrt R +
      (8 / ℓ) * (β / (K.toHistory.event j).incoming.flow.scalar v w) < Lc / Real.sqrt R)
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt R) ≤ ENNReal.ofReal (Aκ * r))
    (hwin : (Tn : ℝ) - r ^ 2 / 2 ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hvT : v ≤ (Tn : ℝ)) (hρ : ρ < r / 100) (hκ : 0 ≤ κ) :
    PickedBallKappa_C11PB β Rad ρ κ K j v w := by
  have hq : 0 < (K.toHistory.event j).incoming.flow.scalar v w := hR.trans_le hRq
  have hpick := pickedBallTop_of_witness_spread_P6DL K j v w hWit hq hC2 hΛ₀ hthr hRadΛ
  have hΛ : 0 < 2 * C2' * Λ₀ := by positivity
  exact pickedBallKappa_of_fresh_C11PK K hWF haT hTn htime hsmall hvol hnr hclock seedTrace j v w
    hwin hvT h1 h2
    (pickedBallFootprint_of_witness_P6DL K haT hsT has hsmall hclock seedTrace ha₀ hpin y hR hgood
      j h1 h2 v hv2 hvσ w hRq hΛ hC2 hpick hRad0 hLw0 hw hCgM hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ
      haβ hLβ hLc hLc0 hdrift hdσ) hρ hκ

end PBKAPPA

section PICKSEL

/-- **G2 PICKSEL 门槛 ⇐ witness 尺度（`_P6DL`，PROVED）**：`ℓ = ℓ₀/√R` 时
`pickedCenterFootprint_P6PS` 的 `hLR : 4(Dc + 8θ/(ℓ√R)) ≤ 3L` ⇔ `4(Dc + 8θ/ℓ₀) ≤ 3L`（与 `R` 无关；
`L → ∞` 时 eventually 成立；`ℓ₀ > 0` 不需要）。端点 Ricci 只需 witness 尺度 `Ric ≤ 3R/ℓ₀²`，不需 `L²R` 曲率。 -/
theorem hLR_of_witness_scale_P6DL {Dc θ ℓ₀ R L : ℝ} (hR : 0 < R)
    (h : 4 * (Dc + 8 * θ / ℓ₀) ≤ 3 * L) :
    4 * (Dc + 8 * θ / (ℓ₀ / Real.sqrt R * Real.sqrt R)) ≤ 3 * L := by
  have hsR : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  rwa [div_mul_cancel₀ ℓ₀ hsR]

end PICKSEL

section FOOT4

/-- **G3 FOOT4 小球形（`_P6DL`，PROVED；结论 1）**：`hdistL` 内层（固定 history / slab `j` / 顶时刻 `t`，
`p′` = crossing 原像）在**小球 + 短窗**上：`ρ²·2C2′·Mb ≤ 1`（`ρ = r/√R_k`、`Mb = Λ₀R_k` ⇒
`r ≤ r* = (2C2′Λ₀)^{-1/2}`）、`Ctime′·(2C2′Mb)·(T/R) ≤ 1/2`（⇒ `T ≤ T* = 1/(4C2′Λ₀Ctime′)`）、
`(8/ℓ)(T/R) ≤ 1`；输入 = hgood + K0 + HI + 顶点值 `R_t(p′) ≤ Mb` + 顶时刻余量
`d_t(O, p′) + ρ + (8/ℓ)(T/R) < d_σ + Lc/√R` ⇒ `∀ τ ∈ [t − T/R, t] ∩ slab`、`∀ z ∈ B_t(p′, ρ)`：
`d_τ(O, z) ≤ d_t(O, z) + 1`。大 `r`/`T`（FOOT3 kernel 的 `2Rad`、`3Bw`）不在此列——结论 2 BLOCKED。 -/
theorem ObservedHistory.hdistL_small_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (y : (H.stageAt σ).Carrier) {R L Lc : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (p' : (H.stage j.castSucc).Carrier)
    {t T ρ Mb ℓ K : ℝ} (ht1 : H.time j.castSucc < t) (ht2 : t < H.time j.succ)
    (haT' : (aSeed : ℝ) ≤ t - T / R) (htσ : t ≤ σ) (hLT : (σ : ℝ) - L ^ 2 / R ≤ t - T / R)
    (hT : 0 ≤ T) (hMb : 0 < Mb) (hCgM : Cg * R ≤ Mb) (hC2 : 1 ≤ C2')
    (hp : (H.event j).incoming.flow.scalar t p' ≤ Mb)
    (hρ : 0 < ρ) (hρM : ρ ^ 2 * (2 * C2' * Mb) ≤ 1)
    (hbud : (Ctime' : ℝ) * (2 * C2' * Mb) * (T / R) ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓM : ℓ ^ 2 * (2 * C2' * (2 * (2 * C2' * Mb))) ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) *
      (2 * (2 * C2' * Mb)) ≤ K)
    (hMτ : 1 ≤ 2 * (2 * C2' * Mb) * (t - T / R))
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc)
    (hdrift : (8 / ℓ) * (T / R) ≤ 1)
    (hp' : riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) p' + ENNReal.ofReal ρ +
        ENNReal.ofReal ((8 / ℓ) * (T / R)) <
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R)) :
    ∀ τ : ℝ, t - T / R ≤ τ → τ ≤ t → H.time j.castSucc < τ →
    ∀ z ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric t) p' ρ,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
          (seedTrace.point j.castSucc h1 h2) z ≤
        riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
          (seedTrace.point j.castSucc h1 h2) z + ENNReal.ofReal 1 := by
  intro τ hτ1 hτ2 hτ3 z hz
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hTR : 0 ≤ T / R := div_nonneg hT hR.le
  have hM2 : Mb ≤ 2 * C2' * Mb := by nlinarith
  have hLcL : ENNReal.ofReal (Lc / Real.sqrt R) ≤ ENNReal.ofReal (L / Real.sqrt R) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hGp : riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
      (seedTrace.point j.castSucc h1 h2) p' + ENNReal.ofReal ρ ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R) :=
    (le_self_add.trans hp'.le).trans (add_le_add le_rfl hLcL)
  have hzt : (H.event j).incoming.flow.scalar t z ≤ 2 * C2' * Mb :=
    H.scalar_ball_of_hgood_P6DL haT hsT has seedTrace y hgood j ht1 ht2
      (haT'.trans (by linarith)) htσ (hLT.trans (by linarith)) h1 h2 p' hMb hCgM hC2 hp hρ hρM
      hGp z hz
  have hz' : riemannianEDistOf ((H.event j).incoming.flow.base.metric t) p' z <
      ENNReal.ofReal ρ := hz
  have hd8 : (8 / ℓ) * (t - τ) ≤ (8 / ℓ) * (T / R) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by norm_num) hℓ.le)
  have hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) z + ENNReal.ofReal ((8 / ℓ) * (t - τ)) <
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R) := by
    refine lt_of_le_of_lt ?_ hp'
    refine add_le_add ?_ (ENNReal.ofReal_le_ofReal hd8)
    exact (riemannianEDistOf_triangle _ _ p' z).trans (add_le_add le_rfl hz'.le)
  have hbud' : (Ctime' : ℝ) * (2 * C2' * Mb) * (t - τ) ≤ 1 / 2 := by
    have hCM : (0 : ℝ) ≤ Ctime' * (2 * C2' * Mb) :=
      mul_nonneg Ctime'.coe_nonneg (by positivity)
    exact (mul_le_mul_of_nonneg_left (by linarith) hCM).trans hbud
  have hMτ' : 1 ≤ 2 * (2 * C2' * Mb) * τ := by
    have := mul_le_mul_of_nonneg_left hτ1 (by positivity : (0 : ℝ) ≤ 2 * (2 * C2' * Mb))
    linarith
  have hdist := H.hdistL_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y hR hgood
    j h1 h2 z hτ3 hτ2 ht2 (haT'.trans hτ1) htσ (hLT.trans hτ1) (by positivity) (hCgM.trans hM2)
    hC2 hzt hbud' hℓ hℓM hℓr hKℓ hKr hKC hMτ' hLc hLc0 hmargin τ ⟨le_rfl, hτ2⟩
  exact hdist.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hd8.trans hdrift)))

end FOOT4

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

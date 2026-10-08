import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalProdP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistortionLocalP6DL

/-!
# `hstayLoc` 的单 slab 段（O-CH11-SLTPROD G1b，后缀 `_P6SP`）

G1 producer `hslabsLoc_of_hgood_P6SP` 的唯一 binder `hstayLoc`（前 slab 坏点尺度 trace stay，距离形）。
本文件证它在**一个** slab 内的段：
* `ObservedHistory.stay_slab_of_top_P6SP`（PROVED）：slab 内 `[τ, v]`，顶时刻 `v` 的点值 `R_v(x) ≤ M`、ODE
  预算、witness 尺度、K0 / HI 与顶时刻距离余量 ⇒ 整段 `[τ, v]` 上 trace 点留在 hgood good region（`hstay` 形）。
  核 = DISTLA `hdistL_of_witness_P6DL`（slab 内 first-exit + worldline ODE + witness Ricci）。
* `ObservedHistory.slabDeriv_prefix_of_slab_top_P6SP`（PROVED，consumer）：K 帧前 slab `i` 内
  `s ∈ [τ, v]` 的导数 ⇐ 上条 + G1 单实例核 `slabDeriv_prefix_of_hgood_stay_P6SP`。
尺度（坏点 `M = max(Cg·R, R(z))`）：`ℓ = ℓ₀/√M`、深度 `v − τ ≤ 1/(2·Ctime′·M)`（一次 ODE 只覆盖这一档，
对应固定 `c⋆` 版）、漂移 `(8/ℓ)(v − τ) ≤ 4/(ℓ₀·Ctime′·√M) ≪ L/√R`。
**未证（repair target）**：slab 顶时刻输入——(i) 跨 `time j.succ` 的 surgery crossing 距离比较
（`d_pre(O, x) ≤ d_post(O, x) + C·h_e`）给顶时刻余量；(ii) 顶时刻点值 `R_v(x) ≤ M`（retained 点跨 surgery
曲率相等 + 后一 slab 的 ODE）；(iii) ∀ `c` 版需多 slab / 多次 ODE 拼接与 `Σ h_e` 有界。**不声称 J10 已去。**
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **G1b 单 slab 段（`_P6SP`，PROVED）**：`hstayLoc` 在**一个** slab 内的段。slab `j` 内 `[τ, v]`
（hgood 时间窗内），trace 点 `x`：顶时刻 `v` 点值 `R_v(x) ≤ M`（`Cg·R ≤ M`）、ODE 预算
`Ctime′·M·(v − τ) ≤ 1/2`、witness 尺度 `ℓ`、K0 / HI、顶时刻余量
`d_v(O, x) + (8/ℓ)(v − τ) < d_σ + Lc/√R`、`Lc/√R + ℓ ≤ L/√R` ⇒ 对 `[τ, v]` 内每个时刻 `s`，`x`（经 HEq 的
`stageAt s` 点）留在 hgood good region：`d_s(seed(s), x) ≤ d_σ(seed, y) + L/√R`（= `hstay` 形）。
证明：DISTLA `hdistL_of_witness_P6DL`（slab 内 first-exit + worldline ODE `R ≤ 2M` + witness Ricci）
给 `d_s ≤ d_v + (8/ℓ)(v − s)`，再接余量；incoming ↔ stage 经 `edist_stage_eq_P6L2` / `point_heq_of_eq_P6M2`。
**不跨 surgery**：slab 顶时刻的余量（= 跨 `time j.succ` 的距离比较）是输入。 -/
theorem ObservedHistory.stay_slab_of_top_P6SP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
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
    (h2 : j.castSucc ≤ H.activeStage Tn) (x : (H.stage j.castSucc).Carrier)
    {τ v M ℓ K : ℝ} (hτ1 : H.time j.castSucc < τ) (hτv : τ ≤ v) (hv2 : v < H.time j.succ)
    (haτ : (aSeed : ℝ) ≤ τ) (hvσ : v ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (hM : 0 < M) (hCgM : Cg * R ≤ M) (hC2 : 1 ≤ C2')
    (hxv : (H.event j).incoming.flow.scalar v x ≤ M)
    (hbud : (Ctime' : ℝ) * M * (v - τ) ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓM : ℓ ^ 2 * (2 * C2' * (2 * M)) ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) * (2 * M) ≤ K)
    (hMτ : 1 ≤ 2 * M * τ)
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc)
    (hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (v - τ)) <
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R))
    (s : Icc (0 : ℝ) H.horizon) (hs : (s : ℝ) ∈ Icc τ v) (hav : aSeed ≤ s) (hvs : s ≤ σ)
    (x' : (H.stageAt s).Carrier) (hx' : HEq x' x) :
    riemannianEDistOf (H.stageMetric (H.activeStage s) s)
        (seedTrace.point (H.activeStage s) (H.activeStage_mono hav)
          (H.activeStage_mono (hvs.trans hsT))) x' ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
  have hd := H.hdistL_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y hR hgood j
    h1 h2 x hτ1 hτv hv2 haτ hvσ hLτ hM hCgM hC2 hxv hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ hLc hLc0
    hmargin s hs
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have h3 : ENNReal.ofReal ((8 / ℓ) * (v - s)) ≤ ENNReal.ofReal ((8 / ℓ) * (v - τ)) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (by linarith [hs.1]) (div_nonneg (by norm_num) hℓ.le))
  have h4 : ENNReal.ofReal (Lc / Real.sqrt R) ≤ ENNReal.ofReal (L / Real.sqrt R) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hinc : riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
      (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R) :=
    calc _ ≤ _ := hd
      _ ≤ riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
            (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (v - τ)) :=
          add_le_add le_rfl h3
      _ ≤ _ := hmargin.le
      _ ≤ _ := add_le_add le_rfl h4
  have hact : H.activeStage s = j.castSucc :=
    H.activeStage_eq_of_slab_P6L3 j s (hτ1.le.trans hs.1) (hs.2.trans_lt hv2)
  have hsd := point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
    (H.activeStage_mono (hvs.trans hsT)) h1 h2
  exact (edist_stage_eq_P6L2 j hact s _ x' _ x hsd hx').trans_le hinc

/-- **consumer：单 slab 段 ⇒ 前 slab 导数（`_P6SP`，PROVED ⇐ slab 顶时刻数据）**：K 帧 `K.prefixAt k` 的
slab `i`（= `K` 的 slab `Fin.castLE _ i`）内时刻 `s ∈ [τ, v]`、trace 点 `x`：G1b `stay_slab_of_top_P6SP`
给 `hstay`，再喂 G1 单实例核 `slabDeriv_prefix_of_hgood_stay_P6SP`（hgood 时间分量）⇒
`|∂_s R(·, x)| ≤ Ctime′·R²`。剩余输入只在 slab 顶时刻 `v`（点值 `≤ M` + 距离余量）——即跨 surgery 的比较。 -/
theorem ObservedHistory.slabDeriv_prefix_of_slab_top_P6SP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg : ℝ} (K : RetainedCoreHistory.{u}) (k : Fin (K.eventCount + 1))
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
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
    (i : Fin (K.prefixAt k).eventCount)
    (h1 : K.toHistory.activeStage aSeed ≤ (Fin.castLE (Nat.le_of_lt_succ k.isLt) i).castSucc)
    (h2 : (Fin.castLE (Nat.le_of_lt_succ k.isLt) i).castSucc ≤ K.toHistory.activeStage Tn)
    (x : ((K.prefixAt k).toHistory.stage i.castSucc).Carrier)
    {τ v M ℓ Kc : ℝ} (hτ1 : (K.prefixAt k).time i.castSucc < τ) (hτv : τ ≤ v)
    (hv2 : v < (K.prefixAt k).time i.succ)
    (haτ : (aSeed : ℝ) ≤ τ) (hvσ : v ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (hM : 0 < M) (hCgM : Cg * R ≤ M) (hC2 : 1 ≤ C2')
    (hxv : ((K.prefixAt k).toHistory.event i).incoming.flow.scalar v x ≤ M)
    (hbud : (Ctime' : ℝ) * M * (v - τ) ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓM : ℓ ^ 2 * (2 * C2' * (2 * M)) ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKℓ : Kc * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ Kc)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) * (2 * M) ≤ Kc)
    (hMτ : 1 ≤ 2 * M * τ)
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc)
    (hmargin : riemannianEDistOf (((K.prefixAt k).toHistory.event i).incoming.flow.base.metric v)
        (seedTrace.point (Fin.castLE (Nat.le_of_lt_succ k.isLt) i).castSucc h1 h2) x +
          ENNReal.ofReal ((8 / ℓ) * (v - τ)) <
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R))
    (s : Icc (0 : ℝ) K.toHistory.horizon) (hs : (s : ℝ) ∈ Icc τ v) (hav : aSeed ≤ s)
    (hvs : s ≤ σ)
    (hq : Cg * R < ((K.prefixAt k).toHistory.event i).incoming.flow.scalar s x) :
    |derivWithin (fun w => ((K.prefixAt k).toHistory.event i).incoming.flow.scalar w x)
        (Iic (s : ℝ)) s| ≤
      Ctime' * ((K.prefixAt k).toHistory.event i).incoming.flow.scalar s x ^ 2 :=
  slabDeriv_prefix_of_hgood_stay_P6SP K k haT hsT has seedTrace y R L hgood i x s hav hvs
    (hτ1.trans_le hs.1) (hs.2.trans_lt hv2) (hLτ.trans hs.1)
    (fun x' hx' => K.toHistory.stay_slab_of_top_P6SP haT hsT has hsmall hclock seedTrace ha₀ hpin
      y hR hgood (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) h1 h2 x hτ1 hτv hv2 haτ hvσ hLτ hM hCgM
      hC2 hxv hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ hLc hLc0 hmargin s hs hav hvs x' hx') hq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

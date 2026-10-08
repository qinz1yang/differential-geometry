import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedClosureLocalC11SC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallKappaC11PK
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# 短窗距离畸变的 witness 局域 producer（O-CH11-DISTLA G1，后缀 `_P6DL`）

三处端点 Ricci（FOOT4 `hdistL`/`hdistLA`、PBKAPPA `PickedBallEndpointRicci_C11PK`、PICKSEL 中心 `hRic`）
都是 `ricci_seed_or_scal_P6L4` 的结论形（窗口时刻 `t`，两端 `ℓ`-球 `Ric ≤ 3/ℓ²`）：seed 端 K0 已付，
U 端只缺 `hscal`（`B_t(x, ℓ)` 上 `R ≤ C·Q`）。本文件用 hgood 的 **witness 球**（`SpatialCanonicalWitness`：
`radius ≥ R^{-1/2}`、domain 上 `C2`-可比）付 `hscal`：
* **G1a `scalar_spread_local_P6DL`（PROVED）**：局域 clopen spread（Ch12 `cn_scalar_spread_S63` 的局域版，
  witness 只在 `B(x, ρ)` 内、只在 `R > N` 处要）：`R(x) ≤ Mb`、`N ≤ Mb`、`ρ²·2C2·Mb ≤ 1` ⇒
  `B(x, ρ)` 上 `R < 2C2·Mb`。球 path-connected + `R` 连续；`R = 2C2·Mb` 的点的 witness 球
  （半径 `≥ (2C2Mb)^{-1/2} ≥ ρ`）上 `R ≥ 2Mb > R(x)`，故不含 `x`，矛盾。
* **G1b `pickedBallTop_of_witness_spread_P6DL`（PROVED）**：hpick `PickedBallTop_C11PB (2C2Λ₀) Rad`
  ⇐ `PickedBallWitness_C11PB Rad qthr` + G1a，条件 `qthr ≤ Λ₀·q`、`1 ≤ Λ₀`、`1 ≤ C2`、
  **`Rad²·2C2Λ₀ ≤ 1`**（即 `Rad ≤ (2C2Λ₀)^{-1/2}`，`Λ = 2C2Λ₀`）。family 形
  `pickedBallTop_of_hgood_P6DL`：hgood（`HgoodCg_C11SH`）+ 中心 Good(L/2) + `Rad ≤ L/2` +
  `Cg·R_n ≤ Λ₀·q` ⇒ hpick，**无 binder**。
* **G1 单时刻**：`scalar_ball_of_hgood_P6DL`（hscal ⇐ hgood witness + 点值 `R_s(x) ≤ Mb` + Good 余量
  `d_s(O, x) + ℓ ≤ d_σ + L/√R`）；`endpointRicci_of_witness_P6DL`（+ K0 + HI ⇒ 两端 `ℓ`-球 Ricci，
  `ricci_seed_or_scal_P6L4`）。
* **G1c `hdistL_of_witness_P6DL`（PROVED，短窗）**：slab `j` 内 `[τ, v]`，顶时刻点值 `R_v(x) ≤ M`、
  `Ctime′·M·(v − τ) ≤ 1/2`（worldline ODE `scalar_le_two_mul_of_localDeriv_C11SC2`，导数 = hgood 时间分量）、
  `ℓ²·4C2′M ≤ 1`、顶时刻余量 `d_v(O, x) + (8/ℓ)(v − τ) < d_σ + Lc/√R`、`Lc/√R + ℓ ≤ L/√R` ⇒
  `∀ s ∈ [τ, v]`，`d_s(O, x) ≤ d_v(O, x) + (8/ℓ)(v − s)`。Good 停止由 `firstExit_distance_stopped_C11SC2`
  内部闭合（不是 hstop）。
* **G2 `footprint_of_witness_P6DL`**：G1c + 顶时刻距离 ⇒ 窗口 footprint `d_s(O, x) < D`。

**尺度**：witness 尺度 `ℓ = ℓ₀/√Q`（`ℓ₀² · 4C2′ · M/Q ≤ 1`）；深度 `θ/Q` 受 ODE 限
`Ctime′·(M/Q)·θ ≤ 1/2`；U 球半径受 spread 限 `r ≤ (2C2Λ₀)^{-1/2}`。∀`r`、∀`T` 大形
（FOOT4 `hdistL`、J10WIRE2 `hballT`）= bounded curvature at bounded distance / 深窗格点 anchor，
witness 链给不出（见 state HANDOVER 的 BLOCKED 精确缺口）。

非循环：只用 hgood（witness 空间分量 + 时间分量）+ K0 seed + HI `hpin` + 算术；不经 hstop / hstopE /
hclosG / hscalU / BCBD / CanonicalLateCore / hspine；hpick 是 **G1b 的结论**，不作输入。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness I3)

section Spread

/-- **G1a 局域 clopen spread（`_P6DL`，PROVED）**：`B(x, ρ)` 内 `R > N` 处有 `SpatialCanonicalWitness`，
`R(x) ≤ Mb`、`N ≤ Mb`、`ρ²·(2C2·Mb) ≤ 1` ⇒ `B(x, ρ)` 上 `R < 2C2·Mb`（Ch12 `cn_scalar_spread_S63`
的局域版：witness 只在球内要）。 -/
theorem scalar_spread_local_P6DL {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I3 M) {ε C1 C2 N Mb ρ : ℝ} (hC2 : 1 ≤ C2) (hMb : 0 < Mb)
    (hNM : N ≤ Mb) (x : M) (hx : metricScalarAt g x ≤ Mb) (hρ : 0 < ρ)
    (hρM : ρ ^ 2 * (2 * C2 * Mb) ≤ 1)
    (hcn : ∀ y ∈ riemannianBallOf g x ρ, N < metricScalarAt g y →
      Nonempty (SpatialCanonicalWitness g ε C1 C2 y)) :
    ∀ y ∈ riemannianBallOf g x ρ, metricScalarAt g y < 2 * C2 * Mb := by
  set L : ℝ := 2 * C2 * Mb with hLdef
  have hL2 : 2 * Mb ≤ L := by rw [hLdef]; nlinarith
  have hLpos : 0 < L := by linarith
  have hNL : N < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hρs : ρ * Real.sqrt L ≤ 1 := by
    have h2 : (ρ * Real.sqrt L) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hLpos.le]
      exact hρM
    nlinarith [mul_nonneg hρ.le hsL.le]
  have hρL : ρ ≤ (Real.sqrt L)⁻¹ := by
    rw [← one_div, le_div_iff₀ hsL]
    exact hρs
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  have hBconn : IsPreconnected (riemannianBallOf g x ρ) :=
    (isPathConnected_riemannianBallOf g x hρ).isConnected.isPreconnected
  have hu : IsOpen {y | metricScalarAt g y < L} := isOpen_lt hcont continuous_const
  have hxB : x ∈ riemannianBallOf g x ρ := by
    change riemannianEDistOf g x x < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hne : (riemannianBallOf g x ρ ∩ {y | metricScalarAt g y < L}).Nonempty :=
    ⟨x, hxB, show metricScalarAt g x < L by linarith⟩
  have hcl : closure {y | metricScalarAt g y < L} ∩ riemannianBallOf g x ρ ⊆
      {y | metricScalarAt g y < L} := by
    rintro y ⟨hyc, hyB⟩
    have hle : metricScalarAt g y ≤ L := closure_lt_subset_le hcont continuous_const hyc
    by_contra hnot
    have heq : metricScalarAt g y = L := le_antisymm hle (not_lt.mp hnot)
    obtain ⟨W⟩ := hcn y hyB (by rw [heq]; exact hNL)
    have hrad : (Real.sqrt L)⁻¹ ≤ W.radius := by
      have := W.radius_lower
      rwa [heq] at this
    have hxout : x ∉ riemannianBallOf g y W.radius := by
      intro hxin
      have hxd := W.ball_inside hxin
      have h1 := (W.scalar_bounds x hxd).1
      rw [heq] at h1
      have hC2pos : 0 < C2 := by linarith
      have h2 : C2⁻¹ * L = 2 * Mb := by
        rw [hLdef]
        field_simp
      rw [h2] at h1
      linarith
    have hxy : ENNReal.ofReal W.radius ≤ riemannianEDistOf g y x := not_lt.mp hxout
    have hyx : riemannianEDistOf g y x < ENNReal.ofReal ρ := by
      rw [riemannianEDistOf_comm]
      exact hyB
    have := hxy.trans_lt hyx
    rw [ENNReal.ofReal_lt_ofReal_iff hρ] at this
    linarith
  exact hBconn.subset_of_closure_inter_subset hu hne hcl

end Spread

section PickedTop

/-- **G1b：hpick ⇐ witness + 局域 spread（`_P6DL`，PROVED）**。`q := R(v, w)`；
`PickedBallWitness_C11PB Rad qthr`（球 `B_v(w, Rad/√q)` 上 `R > qthr` 处 witness）、`qthr ≤ Λ₀·q`、
`1 ≤ Λ₀`、`1 ≤ C2`、`Rad²·(2C2Λ₀) ≤ 1` ⇒ `PickedBallTop_C11PB (2C2Λ₀) Rad`（`B_v(w, Rad/√q)` 上
`R ≤ 2C2Λ₀·q`）。Rad 上限 = `(2C2Λ₀)^{-1/2}`，输出常数 `Λ = 2C2Λ₀`。 -/
theorem pickedBallTop_of_witness_spread_P6DL {Rad qthr ε C1 C2 Λ₀ : ℝ}
    (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) (v : ℝ)
    (w : (K.stage j.castSucc).Carrier)
    (hW : PickedBallWitness_C11PB Rad qthr ε C1 C2 K j v w)
    (hq : 0 < (K.toHistory.event j).incoming.flow.scalar v w)
    (hC2 : 1 ≤ C2) (hΛ₀ : 1 ≤ Λ₀)
    (hthr : qthr ≤ Λ₀ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hRad : Rad ^ 2 * (2 * C2 * Λ₀) ≤ 1) :
    PickedBallTop_C11PB (2 * C2 * Λ₀) Rad K j v w := by
  intro x hx
  set q := (K.toHistory.event j).incoming.flow.scalar v w with hqdef
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  by_cases hR0 : 0 < Rad
  · have hρ : 0 < Rad / Real.sqrt q := div_pos hR0 hsq
    have hMb : 0 < Λ₀ * q := mul_pos (by linarith) hq
    have hρM : (Rad / Real.sqrt q) ^ 2 * (2 * C2 * (Λ₀ * q)) ≤ 1 := by
      rw [div_pow, Real.sq_sqrt hq.le]
      calc Rad ^ 2 / q * (2 * C2 * (Λ₀ * q)) = Rad ^ 2 * (2 * C2 * Λ₀) := by
            field_simp
        _ ≤ 1 := hRad
    have hw : metricScalarAt ((K.toHistory.event j).incoming.flow.base.metric v) w ≤ Λ₀ * q := by
      change q ≤ Λ₀ * q
      nlinarith
    have hcn : ∀ y ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt q),
        qthr < metricScalarAt ((K.toHistory.event j).incoming.flow.base.metric v) y →
        Nonempty (SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
          ε C1 C2 y) := by
      intro y hy hyq
      obtain ⟨W, _⟩ := hW y hy hyq
      exact ⟨W⟩
    have h := scalar_spread_local_P6DL ((K.toHistory.event j).incoming.flow.base.metric v) hC2
      hMb hthr w hw hρ hρM hcn x hx
    change metricScalarAt ((K.toHistory.event j).incoming.flow.base.metric v) x ≤ 2 * C2 * Λ₀ * q
    calc metricScalarAt ((K.toHistory.event j).incoming.flow.base.metric v) x
        ≤ 2 * C2 * (Λ₀ * q) := h.le
      _ = 2 * C2 * Λ₀ * q := by ring
  · exfalso
    have hle : Rad / Real.sqrt q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hR0) hsq.le
    have hx' : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) w x <
        ENNReal.ofReal (Rad / Real.sqrt q) := hx
    rw [ENNReal.ofReal_of_nonpos hle] at hx'
    exact (ENNReal.not_lt_zero hx')

/-- **G1b family 形：hpick ⇐ hgood（`_P6DL`，PROVED，无 binder）**：`pickedBallWitness_of_hgood_C11PB`
（中心 Good(L/2)、`Rad ≤ L/2`、`R_n ≤ q`）+ G1b，阈值 `Cg·R_n ≤ Λ₀·q`。 -/
theorem pickedBallTop_of_hgood_P6DL {Cg : ℝ} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 Λ₀ : ℝ}
    {Ctime : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) (j : Fin (K n).eventCount) (v : Icc (0 : ℝ) (K n).toHistory.horizon)
    (hv1 : (K n).time j.castSucc < v) (hv2 : (v : ℝ) < (K n).time j.succ)
    (hav : aSeed n ≤ v) (hvs : v ≤ σ n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (w : ((K n).stage j.castSucc).Carrier) {Rad : ℝ} (hRn : 0 < R n)
    (hRw : R n ≤ ((K n).toHistory.event j).incoming.flow.scalar v w) (hRad0 : 0 ≤ Rad)
    (hRadL : Rad ≤ L n / 2)
    (hw : riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
        ((seedTrace n).point j.castSucc h1 h2) w ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / 2 / Real.sqrt (R n)))
    (hC2 : 1 ≤ C2) (hΛ₀ : 1 ≤ Λ₀)
    (hthr : Cg * R n ≤ Λ₀ * ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hRad : Rad ^ 2 * (2 * C2 * Λ₀) ≤ 1) :
    PickedBallTop_C11PB (2 * C2 * Λ₀) Rad (K n) j v w :=
  pickedBallTop_of_witness_spread_P6DL (K n) j v w
    (pickedBallWitness_of_hgood_C11PB K hgood n j v hv1 hv2 hav hvs hvL h1 h2 w hRn hRw hRad0
      hRadL hw)
    (hRn.trans_le hRw) hC2 hΛ₀ hthr hRad

end PickedTop

section Single

/-- **G1 单时刻 hscal（`_P6DL`，PROVED）**：slab `j` 内时刻 `s`（hgood 时间窗内）、U 端点 `x`：点值
`R_s(x) ≤ Mb`、`Cg·R ≤ Mb`、Good 余量 `d_s(O, x) + ℓ ≤ d_σ + L/√R`、`ℓ²·(2C2′·Mb) ≤ 1` ⇒
`B_s(x, ℓ)` 上 `R ≤ 2C2′·Mb`（= `ricci_seed_or_scal_P6L4` 的 `hscal`，`C·Q = 2C2′·Mb`）。
witness 只在球内 `R > Cg·R` 处由 hgood 给（`witness_of_hgood_slab_Cg_P6LS3`），再 G1a spread。 -/
theorem ObservedHistory.scalar_ball_of_hgood_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) {R L : ℝ}
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
    (j : Fin H.eventCount) {s Mb ℓ : ℝ} (hs1 : H.time j.castSucc < s)
    (hs2 : s < H.time j.succ) (haS : (aSeed : ℝ) ≤ s) (hsσ : s ≤ σ)
    (hLs : (σ : ℝ) - L ^ 2 / R ≤ s)
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn)
    (x : (H.stage j.castSucc).Carrier) (hMb : 0 < Mb) (hCgM : Cg * R ≤ Mb) (hC2 : 1 ≤ C2')
    (hxs : (H.event j).incoming.flow.scalar s x ≤ Mb)
    (hℓ : 0 < ℓ) (hℓM : ℓ ^ 2 * (2 * C2' * Mb) ≤ 1)
    (hGx : riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ℓ ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ z : (H.stage j.castSucc).Carrier,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z < ENNReal.ofReal ℓ →
      (H.event j).incoming.flow.scalar s z ≤ 2 * C2' * Mb := by
  intro z hz
  have hcn : ∀ y' ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric s) x ℓ,
      Cg * R < metricScalarAt ((H.event j).incoming.flow.base.metric s) y' →
      Nonempty (SpatialCanonicalWitness ((H.event j).incoming.flow.base.metric s)
        eps C1' C2' y') := by
    intro y' hy' hR'
    have hy'' : riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x y' <
        ENNReal.ofReal ℓ := hy'
    have hd : riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) y' ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R) :=
      (riemannianEDistOf_triangle _ (seedTrace.point j.castSucc h1 h2) x y').trans
        ((add_le_add le_rfl hy''.le).trans hGx)
    obtain ⟨W, _⟩ := H.witness_of_hgood_slab_Cg_P6LS3 haT hsT has seedTrace y R L hgood j s hs1
      hs2 haS hsσ hLs h1 h2 y' hd hR'.le
    exact ⟨W⟩
  exact (scalar_spread_local_P6DL ((H.event j).incoming.flow.base.metric s) hC2 hMb hCgM x hxs
    hℓ hℓM hcn z hz).le

/-- **G1 `endpointRicci_of_witness_P6DL`（`_P6DL`，PROVED）**：单时刻 `s`，seed 端 K0（`ℓ ≤ r/50`、
`r⁻² ≤ K`）+ U 端 hscal（`scalar_ball_of_hgood_P6DL`，`C = 2C2′`、`Q` = 点值上界）+ HI pinching
（`2√3(C/2 + max C (2e⁴))Q ≤ K`）、`Kℓ² ≤ 1` ⇒ 两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g`
（= `ricci_seed_or_scal_P6L4` 结论逐字 = PBKAPPA / PICKSEL / FOOT4 端点 Ricci 的点形）。 -/
theorem ObservedHistory.endpointRicci_of_witness_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (y : (H.stageAt σ).Carrier) {R L : ℝ}
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
    (j : Fin H.eventCount) {s Q ℓ K : ℝ} (hs1 : H.time j.castSucc < s)
    (hs2 : s < H.time j.succ) (haS : (aSeed : ℝ) ≤ s) (hsσ : s ≤ σ)
    (hLs : (σ : ℝ) - L ^ 2 / R ≤ s)
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn)
    (x : (H.stage j.castSucc).Carrier) (hQ : 0 < Q) (hCgQ : Cg * R ≤ Q) (hC2 : 1 ≤ C2')
    (hxs : (H.event j).incoming.flow.scalar s x ≤ Q)
    (hℓ : 0 < ℓ) (hℓQ : ℓ ^ 2 * (2 * C2' * Q) ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) * Q ≤ K)
    (hQs : 1 ≤ Q * s)
    (hGx : riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ℓ ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ z : (H.stage j.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
          (seedTrace.point j.castSucc h1 h2) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event j).incoming.flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event j).incoming.flow.base.metric s).inner z ξ ξ := by
  have hσT : (σ : ℝ) ≤ Tn := Subtype.coe_le_coe.mpr hsT
  have hC0 : (0 : ℝ) ≤ 2 * C2' := by linarith
  exact H.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin j h1 h2 x hQ hℓ hKℓ hℓr
    hKr hC0 hKC hs1 hs2 haS (hsσ.trans hσT) hQs
    (H.scalar_ball_of_hgood_P6DL haT hsT has seedTrace y hgood j hs1 hs2 haS hsσ hLs h1 h2 x hQ
      hCgQ hC2 hxs hℓ hℓQ hGx)

end Single

section Window

/-- **G1c `hdistL_of_witness_P6DL`（`_P6DL`，PROVED，短窗）**：slab `j` 内 `[τ, v]`（hgood 时间窗内），
U 端点 `x`：顶时刻点值 `R_v(x) ≤ M`、`Cg·R ≤ M`、ODE 预算 `Ctime′·M·(v − τ) ≤ 1/2`、witness 尺度
`ℓ²·2C2′·(2M) ≤ 1`、P6L4 常数（`Q = 2M`、`C = 2C2′`）、顶时刻余量
`d_v(O, x) + (8/ℓ)(v − τ) < d_σ + Lc/√R`、`Lc/√R + ℓ ≤ L/√R` ⇒ `∀ s ∈ [τ, v]`，
`d_s(O, x) ≤ d_v(O, x) + (8/ℓ)(v − s)`（I.8.3(b)）。
证明：`firstExit_distance_stopped_C11SC2`（`d < d_σ + Lc/√R` 停止）；停止区间内 (1) worldline ODE
`scalar_le_two_mul_of_localDeriv_C11SC2`（导数 = hgood 时间分量 `deriv_of_hgood_slab_Cg_C11SC2`）给
`R_s(x) ≤ 2M`；(2) G1 `endpointRicci_of_witness_P6DL`。 -/
theorem ObservedHistory.hdistL_of_witness_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
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
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R)) :
    ∀ s ∈ Icc τ v, riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (v - s)) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hLcL : ENNReal.ofReal (Lc / Real.sqrt R) ≤ ENNReal.ofReal (L / Real.sqrt R) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  refine H.firstExit_distance_stopped_C11SC2 j hℓ hτv hτ1 hv2 _ x hmargin ?_
  intro s hs hG z ξ hz
  have hs1 : H.time j.castSucc < s := hτ1.trans hs.1
  have hs2 : s < H.time j.succ := hs.2.trans hv2
  have haS : (aSeed : ℝ) ≤ s := haτ.trans hs.1.le
  have hsσ : s ≤ (σ : ℝ) := hs.2.le.trans hvσ
  have hLs : (σ : ℝ) - L ^ 2 / R ≤ s := hLτ.trans hs.1.le
  have hGood : ∀ r' ∈ Icc s v, riemannianEDistOf ((H.event j).incoming.flow.base.metric r')
      (seedTrace.point j.castSucc h1 h2) x ≤ riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R) :=
    fun r' hr' => (hG r' hr').le.trans (add_le_add le_rfl hLcL)
  have hloc : ∀ r' ∈ Ioo s v, M < (H.event j).incoming.flow.scalar r' x →
      |derivWithin (fun w => (H.event j).incoming.flow.scalar w x) (Iic r') r'| ≤
        Ctime' * (H.event j).incoming.flow.scalar r' x ^ 2 := by
    intro r' hr' hMr
    exact H.deriv_of_hgood_slab_Cg_C11SC2 haT hsT has seedTrace y R L hgood j r'
      (hs1.trans hr'.1) (hr'.2.trans hv2) (haS.trans hr'.1.le) (hr'.2.le.trans hvσ)
      (hLs.trans hr'.1.le) h1 h2 x (hGood r' ⟨hr'.1.le, hr'.2.le⟩) (hCgM.trans hMr.le)
  have hbud' : (Ctime' : ℝ) * M * (v - s) ≤ 1 / 2 := by
    have hCM : (0 : ℝ) ≤ Ctime' * M := mul_nonneg Ctime'.coe_nonneg hM.le
    calc (Ctime' : ℝ) * M * (v - s) ≤ Ctime' * M * (v - τ) :=
          mul_le_mul_of_nonneg_left (by linarith [hs.1]) hCM
      _ ≤ 1 / 2 := hbud
  have hxs : (H.event j).incoming.flow.scalar s x ≤ 2 * M :=
    H.scalar_le_two_mul_of_localDeriv_C11SC2 j hM hs1.le hs.2.le hv2 x hloc hxv hbud' s
      ⟨le_rfl, hs.2.le⟩
  have hGx : riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
      (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ℓ ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R) := by
    calc _ ≤ (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R)) + ENNReal.ofReal ℓ :=
          add_le_add (hG s ⟨le_rfl, hs.2.le⟩).le le_rfl
      _ = riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R + ℓ) := by
          rw [add_assoc, ENNReal.ofReal_add (div_nonneg hLc0 hsR.le) hℓ.le]
      _ ≤ riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt R) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLc)
  have hQs : 1 ≤ 2 * M * s := by
    have := mul_le_mul_of_nonneg_left hs.1.le (by linarith : (0 : ℝ) ≤ 2 * M)
    linarith
  exact H.endpointRicci_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y hgood j
    hs1 hs2 haS hsσ hLs h1 h2 x (by linarith) (by linarith) hC2 hxs hℓ hℓM hℓr hKℓ hKr hKC hQs
    hGx z ξ hz

/-- **G2 `footprint_of_witness_P6DL`（`_P6DL`，PROVED）**：G1c + 顶时刻距离
`d_v(O, x) ≤ d_σ + Lv/√R`、漂移 `Lv/√R + (8/ℓ)(v − τ) < Lc/√R`、`d_σ < ⊤` ⇒ 窗口 footprint
`∀ s ∈ [τ, v]`，`d_s(O, x) ≤ d_σ + Lc/√R`（PBKAPPA `PickedBallFootprint_C11PK` /
PICKSEL 中心 footprint / FOOT4 `hfpL` 的公共核；配 top gate `hdσ` 即 `< A·r`）。 -/
theorem ObservedHistory.footprint_of_witness_P6DL {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
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
    (hfin : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y ≠ ⊤) :
    ∀ s ∈ Icc τ v, riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hv0 : 0 ≤ Lv / Real.sqrt R := div_nonneg hLv0 hsR.le
  have hd0 : 0 ≤ (8 / ℓ) * (v - τ) :=
    mul_nonneg (div_nonneg (by norm_num) hℓ.le) (by linarith)
  have hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (v - τ)) <
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R) := by
    calc _ ≤ (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lv / Real.sqrt R)) +
          ENNReal.ofReal ((8 / ℓ) * (v - τ)) := add_le_add hdv le_rfl
      _ = riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (Lv / Real.sqrt R + (8 / ℓ) * (v - τ)) := by
          rw [add_assoc, ← ENNReal.ofReal_add hv0 hd0]
      _ < riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R) :=
          ENNReal.add_lt_add_left hfin
            ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (add_nonneg hv0 hd0) hdrift)).2 hdrift)
  have hdist := H.hdistL_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y hR hgood j
    h1 h2 x hτ1 hτv hv2 haτ hvσ hLτ hM hCgM hC2 hxv hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ hLc hLc0
    hmargin
  intro s hs
  have hvs : (8 / ℓ) * (v - s) ≤ (8 / ℓ) * (v - τ) :=
    mul_le_mul_of_nonneg_left (by linarith [hs.1]) (div_nonneg (by norm_num) hℓ.le)
  exact (hdist s hs).trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hvs)).trans hmargin.le)

end Window

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

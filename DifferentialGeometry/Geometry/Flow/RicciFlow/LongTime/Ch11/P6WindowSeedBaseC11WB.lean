import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedCenterProducerC11PT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedClosureLocalC11SC2

/-!
# WindowSeed base case：双尺度 closure + first-failure（O-CH11-WSBASE，后缀 `_C11WB`）

PICKT1 真缺口 `PickedCenterWindowSeed_C11PT`（`P6PickedCenterProducerC11PT.lean:103`）：driver 中心区域点 `x`
（slice 时刻 `v`、`x ∈ B_v(tr x₁, Dc/√R_n)`）在公共窗 `[v − θ/R_n, v]` 上 `d_{v′}(O, x) ≤ dσ + L/√R_n`。
SEEDCL2 G3 判中心尺度实例 = 路线 (i) 的归纳步（输入 slice 界 `R(v, ·) ≤ ΛR_n` = 正在追求的 BCBD），R-C11-18 Q4(a)
确认路线 (i) OPEN。

## G0：first-failure 的精确形（与 SEEDCL2 内部 first-exit 同构）
固定 slice 数据 `(j′, v, x₁, tr, x)`，`v* := inf{s : ∀ r ∈ [s, v], d_r(O, x) ≤ dσ + Lc/√R_n}`
（= `seed_closure_firstExit_stopped_C11SC2` 的停止时刻）。`[v*, v]` 上可用：hgood 时间分量
`|∂ₜR(·, x)| ≤ Ctime R²`（`R > Cg R_n`）、空间分量 witness / 梯度、K0 seed、HI；要导出：drift `≲ (L − Lc)/√R_n`。
**关键观察**：SEEDCL2 两核里 slice 界只在 `x` 点被用（G3 example 的 `hslice x hx`），且对窗口尺度 `q` 泛型。

## G1（PROVED，无 binder）
* `ObservedHistory.windowSeed_pointAnchor_C11WB`：逐点 anchor `R(v, x) ≤ Λq` ⇒
  窗 `[v − β/q, v]` closure。
* `pickedCenterWindowSeed_twoScale_C11WB`（主定理）：`q_x := max(R_n, R(v, x)/Λ)` ⇒ anchor 恒真 ⇒ 区域内**每个**
  `x` 在点自身窗 `[v − θ/q_x, v]` 上 closure；低点（`R(v, x) ≤ ΛR_n`）即整个公共窗。
* `pickedCenterWindowSeed_ceilCyl_C11WB` / `pickedCenterWindowSeed_guardKX_C11WB`：KSWEXIT guard
  `2·Ctime·max(R(t, z), q)·(t − v) ≤ 1` 的 seed localization（`Λ R_n ≤ q`、`θ = 1/(2 Ctime Λ)`）。
* consumer `pickedCenterFootprint_twoScale_C11WB`：κ 宏观 footprint 在点自身窗上 ⇐ closure + `hdσ`，
  **无端点 Ricci**。
## G1 合同（PROVISIONAL[base]）
`WindowSeedBase_C11WB` = 双尺度定理没付的那块（高点 `R(v, x) > ΛR_n`、`v′ ∈ [v − θ/R_n, v − θ/q_x)`）；
`pickedCenterWindowSeed_of_base_C11WB`：`PickedCenterWindowSeed_C11PT` ⇐ 双尺度 + base。
## G2（条件定理 PROVED；缺口 BLOCKED）
`windowSeedBase_of_firstFailure_C11WB`：base ⇐ `hceil`（first-failure guarded worldline ceiling：
`x` 仍 Good 时
`R(s, x) ≤ Λ_L R_n`，`Λ_L ~ L²/θ²` 可任意大）。`hceil` 不可局部推出——**Bryant-tip 情景**：`R(·, x) ≡ M ≫ L²R_n`
（steady-soliton cap 尖端）与 hgood / ODE / 梯度 / witness 全部相容，8.3(b) drift `~ θ√M/R_n ≫ L/√R_n`；
排除它 = 中心尺度 BCBD（T1）⇒ 循环；路线 (i) 是 `T1(σ₁) ⇐ T1(σ₁ − θ)` 的无穷后退。repair target = 路线 (ii)：
KSWEXIT guarded ShortSLT 只在 guard 后缀消费 U 数据，seed localization 由本文件 guardKX / pointAnchor 付，公共窗
base 退役（不再需要 `PickedCenterWindowSeed_C11PT` 全形）。

非循环：只 import PICKT1 G2 合同文件与 SEEDCL2；无 hstop / hstopE / hstopX / hstayΩ、无 `DerivativeBoundBefore`、
无 `qcan`、无 hpick / `PickedBallTop_C11PB`、无 hUVC M4 链 / hclosG / hscalU / CanonicalLateCore / hspine。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section PointAnchor

/-- **point-anchor 窗口 seed closure（`_C11WB`，PROVED，无 binder）**：SEEDCL2 两条核
（`seed_closure_firstExit_stopped_C11SC2` + `windowScal_of_pickedTop_local_C11SC2`）的逐点形。
窗口尺度 `q` 泛型（`R ≤ q`、`Cg·R ≤ Λq`、`Ctime′ Λ β ≤ 1/2`）；**anchor 只在 `x` 一点**：`R(v, x) ≤ Λq`
（不要 hpick 整球——SEEDCL2 G3 的 `hslice` 只在 `x` 处被用，球心取 `x` 自身、`Rad := 1`）；ExitGuard 也只在 `x`：
`d_v(O, x) ≤ dσ + (Lc/2)/√R`。结论：`v′ ∈ [v − β/q, v]`（slab `j` 内）⇒ `d_{v′}(O, x) ≤ dσ + L/√R`。
first-failure 结构（= 本车道 G0 的 `v*`）在核内部：`v* := inf{s : ∀ r ∈ [s, v], d_r(O, x) ≤ dσ + Lc/√R}`，
`[v*, v]` 上 `x` Good ⇒ hgood 时间分量给 worldline ceiling（`R(·, x) ≤ 2Λq`，导数只在 `R > Λq`）、
空间分量给 `B_s(x, ρ/√(2Λq))` 上 `R ≤ 6Λq` ⇒ 8.3(b) 端点 Ricci ⇒ drift 吃进 `L − Lc` 余量 ⇒ `v*` 推不上去。 -/
theorem ObservedHistory.windowSeed_pointAnchor_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
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
    (h2 : j.castSucc ≤ H.activeStage Tn)
    {v q Λ β C : ℝ} (hv2 : v < H.time j.succ) (hRq : R ≤ q) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R ≤ Λ * q) (hbud : (Ctime' : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
      max β 0 ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hav : (aSeed : ℝ) ≤ v - β / q) (hvσ : v ≤ σ) (hσL : (σ : ℝ) - L ^ 2 / R ≤ v - β / q)
    (hlate : 1 ≤ R * (v - β / q)) (x : (H.stage j.castSucc).Carrier)
    (hxG : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (Lc / 2 / Real.sqrt R))
    (hxv : (H.event j).incoming.flow.scalar v x ≤ Λ * q)
    (v' : ℝ) (hwin : v - β / q ≤ v') (hv'v : v' ≤ v) (hv'1 : H.time j.castSucc < v') :
    riemannianEDistOf ((H.event j).incoming.flow.base.metric v')
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
  have hq : 0 < q := hR.trans_le hRq
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hLc0 : 0 ≤ Lc := by
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        max β 0 := mul_nonneg (by positivity) (le_max_right _ _)
    linarith
  have hLcL : Lc / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) := by
      have := localPropagationRadius_pos hC2
      positivity
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  have hL' : 2 * max 1 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤
        Lc := by
    rw [max_eq_left zero_le_one]
    linarith
  have hxx : x ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) x
      (1 / Real.sqrt q) := by
    change riemannianEDistOf _ x x < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  set dσ := riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
    (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y
    with hdσdef
  rcases eq_or_ne dσ ⊤ with hT | hT
  · rw [hT, top_add]
    exact le_top
  have hdσ : dσ = ENNReal.ofReal dσ.toReal := (ENNReal.ofReal_toReal hT).symm
  have hlate' : ∀ s : ℝ, v - β / q ≤ s → 1 ≤ q * s := by
    intro s hs
    have hpos : 0 < v - β / q := by
      by_contra hneg
      have hle := not_lt.mp hneg
      nlinarith
    have hRs : R * (v - β / q) ≤ R * s := mul_le_mul_of_nonneg_left hs hR.le
    have hqs : R * s ≤ q * s := mul_le_mul_of_nonneg_right hRq (hpos.le.trans hs)
    linarith
  have hcl := H.seed_closure_firstExit_stopped_C11SC2 haT hsmall hclock seedTrace ha₀
    hpin j h1 h2 x x hdσ ENNReal.toReal_nonneg hR hRq hC1 hRr hL' hxG hxx hwin hv'v hv'1 hv2
    (hav.trans hwin) (hvσ.trans hsT) (hlate' v' hwin)
    (fun s hs1 hsv hs0 hG z hz => windowScal_of_pickedTop_local_C11SC2 hC2 H haT hsT
      has seedTrace y hR hgood j h1 h2 hv2 hq hRq hΛ hCgΛ hbud hΛC hρC hρL hLc0 hvσ x
      hxv s hs1 hsv hs0 (hav.trans hs1) (hσL.trans hs1) (fun r hr => (hG r hr).le) z hz)
  exact hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL))

end PointAnchor

section TwoScale

/-- **slice 时刻区域点的 seed 距离（`_C11WB`，PROVED：hdistQC + 三角不等式）**：PICKSEL
`seedDist_slice_P6PS` 的单 history 副本（PICKSEL 未入 SNAP，不 import）。`hdl`（T1 壳 `hdistQC` 在固定
`n` 处的体，traced 点余量 `L/4`）+ `x ∈ B_v(tr x₁, Dc/√R_n)` ⇒ `d_v(O, x) ≤ dσ + (L/4 + Dc)/√R_n`。 -/
theorem seedDist_slice_C11WB (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier)
    {Rn L Dw Dc Tc : ℝ} (hRn : 0 < Rn) (hL0 : 0 ≤ L) (hDc : 0 ≤ Dc)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (haS : (aSeed : ℝ) ≤ (σ : ℝ) - Tc / Rn)
    (j' : Fin K.eventCount) (v : ℝ) (hv1 : K.time j'.castSucc < v)
    (hv2 : v < K.time j'.succ) (hvT : (σ : ℝ) - Tc / Rn ≤ v) (hvσ : v ≤ σ)
    (x₁ : (K.toHistory.stage (K.toHistory.activeStage σ)).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn))
    (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁)
    (x : (K.stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn))
    (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn) :
    riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (seedTrace.point j'.castSucc h1 h2) x ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L / 4 + Dc) / Real.sqrt Rn) := by
  have hvh : v ≤ K.toHistory.horizon := hvσ.trans σ.2.2
  let vI : Icc (0 : ℝ) K.toHistory.horizon :=
    ⟨v, (K.toHistory.time_nonneg _).trans hv1.le, hvh⟩
  have hact : K.toHistory.activeStage vI = j'.castSucc :=
    K.activeStage_eq_castSucc_C11PB j' vI hv1 hv2
  have hav : aSeed ≤ vI := by
    change (aSeed : ℝ) ≤ v
    linarith
  have hvs : vI ≤ σ := by
    change v ≤ (σ : ℝ)
    exact hvσ
  have key : ∀ (k : Fin (K.toHistory.eventCount + 1))
      (_hk : K.toHistory.activeStage vI = k) (hkσ : k ≤ K.toHistory.activeStage σ)
      (tr' : BackwardPointTrace K.toHistory k (K.toHistory.activeStage σ) hkσ x₁)
      (h1' : K.toHistory.activeStage aSeed ≤ k) (h2' : k ≤ K.toHistory.activeStage Tn),
      riemannianEDistOf (K.toHistory.stageMetric k vI) (seedTrace.point k h1' h2')
          (tr'.point k le_rfl hkσ) ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (L / 4 / Real.sqrt Rn) := by
    intro k hk
    subst hk
    intro hkσ tr' h1' h2'
    exact hdl x₁ hx₁ vI hav hvs hvT tr'
  have htr := key j'.castSucc hact hjσ tr h1 h2
  rw [ObservedHistory.stageMetric_castSucc_apply] at htr
  have hs : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hRn
  have ha0 : 0 ≤ L / 4 / Real.sqrt Rn := div_nonneg (div_nonneg hL0 (by norm_num)) hs.le
  have hb0 : 0 ≤ Dc / Real.sqrt Rn := div_nonneg hDc hs.le
  calc riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (seedTrace.point j'.castSucc h1 h2) x
      ≤ riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
          (seedTrace.point j'.castSucc h1 h2) (tr.point j'.castSucc le_rfl hjσ) +
        riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) x := riemannianEDistOf_triangle _ _ _ _
    _ ≤ (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (L / 4 / Real.sqrt Rn)) +
        ENNReal.ofReal (Dc / Real.sqrt Rn) := add_le_add htr hx.le
    _ = riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal ((L / 4 + Dc) / Real.sqrt Rn) := by
        rw [add_assoc, ← ENNReal.ofReal_add ha0 hb0, ← add_div]

/-- **双尺度窗口 seed closure（`_C11WB`，G1 主定理，PROVED，无 binder）**。driver 中心区域（PICKT1
`PickedCenterWindowSeed_C11PT` 的同一量词前缀：slice 时刻 `v ∈ [σ − Tc/R_n, σ]`、`x₁ ∈ B_σ(y, Dw/√R_n)` 的 trace
`tr`、`x ∈ B_v(tr x₁, Dc/√R_n)`）里**每个** `x`，取**点自身窗口尺度** `q_x := max(R_n, R(v, x)/Λ)`：
窗口 `v′ ∈ (time j′⁻, v)`、`v − θ/q_x ≤ v′` ⇒ `d_{v′}(O j′, x) ≤ dσ + L/√R_n`（无曲率阈值）。
* 低点 `R(v, x) ≤ Λ R_n`：`q_x = R_n`，即**公共窗** `[v − θ/R_n, v]`——SEEDCL2 G3 的 `hslice` 在这里就是分支条件
  本身（只在 `x` 点用），不循环；
* 高点 `R(v, x) > Λ R_n`：`q_x = R(v, x)/Λ`，窗口 `θΛ/R(v, x)`（点自身尺度，路线 (ii) 的窗口形）。
anchor `R(v, x) ≤ Λ q_x` 恒真 ⇒ 不要任何 slice 曲率界 / hpick / BCBD。输入：selection hgood（区域 `L/√R_n`、阈值
`Cg R_n`）+ K0 seed + HI `hpin` + `hdl`（= T1 `hdistQC`，`L/4` 余量）+ 算术（`Cg ≤ Λ`、`Ctime′ Λ θ ≤ 1/2`、
`L/4 + Dc ≤ Lc/2`、`Lc + 2ρ/√(2Λ) ≤ L`、`2 + 16√K(C) θ ≤ Lc`、`Tc + θ ≤ L²`）+ 时间域。
**无** hstop / hstopE / hstopX / hstayΩ、无 `DerivativeBoundBefore`、无 `qcan`、
无 hpick / `PickedBallTop_C11PB`。 -/
theorem pickedCenterWindowSeed_twoScale_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ C : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2) :
    ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
    ∀ v' ∈ Ioo (K.time j'.castSucc) v,
      v - θ / max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) ≤ v' →
      riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v') (O j') x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / Real.sqrt Rn) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hwin
  have hsR : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hR
  have hρ0 := localPropagationRadius_pos hC2
  have hL0 : 0 ≤ L := by
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        θ := by positivity
    have h1 : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) := by positivity
    linarith
  have hTθ : (Tc + θ) / Rn = Tc / Rn + θ / Rn := add_div _ _ _
  have hLR : (Tc + θ) / Rn ≤ L ^ 2 / Rn := div_le_div_of_nonneg_right hTL hR.le
  have haS' : (aSeed : ℝ) ≤ (σ : ℝ) - Tc / Rn := by
    have : 0 ≤ θ / Rn := div_nonneg hθ hR.le
    linarith
  have hvh : v ≤ K.toHistory.horizon := hvσ.trans σ.2.2
  let vI : Icc (0 : ℝ) K.toHistory.horizon :=
    ⟨v, (K.toHistory.time_nonneg _).trans hv1.le, hvh⟩
  have hact : K.toHistory.activeStage vI = j'.castSucc :=
    K.activeStage_eq_castSucc_C11PB j' vI hv1 hv2
  have havI : aSeed ≤ vI := by
    change (aSeed : ℝ) ≤ v
    linarith
  have h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc :=
    hact ▸ K.toHistory.activeStage_mono havI
  have h2 : j'.castSucc ≤ K.toHistory.activeStage Tn :=
    hjσ.trans (K.toHistory.activeStage_mono hsT)
  have hxG0 := seedDist_slice_C11WB K haT hsT has seedTrace y hR hL0 hDc
    hdl haS' j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2
  have hxG : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (seedTrace.point j'.castSucc h1 h2) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / 2 / Real.sqrt Rn) :=
    hxG0.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hDcL hsR.le)))
  set q := max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) with hqdef
  have hRq : Rn ≤ q := le_max_left _ _
  have hq0 : 0 < q := hR.trans_le hRq
  have hCgq : Cg * Rn ≤ Λ * q :=
    (mul_le_mul_of_nonneg_right hCgΛ hR.le).trans (mul_le_mul_of_nonneg_left hRq hΛ.le)
  have hxv : (K.toHistory.event j').incoming.flow.scalar v x ≤ Λ * q := by
    have hle : (K.toHistory.event j').incoming.flow.scalar v x / Λ ≤ q := le_max_right _ _
    rw [div_le_iff₀ hΛ] at hle
    linarith
  have hθq : θ / q ≤ θ / Rn := div_le_div_of_nonneg_left hθ hR hRq
  have hav : (aSeed : ℝ) ≤ v - θ / q := by linarith
  have hσL : (σ : ℝ) - L ^ 2 / Rn ≤ v - θ / q := by linarith
  have hlate' : 1 ≤ Rn * (v - θ / q) := by
    have : (σ : ℝ) - (Tc + θ) / Rn ≤ v - θ / q := by linarith
    exact hlate.trans (mul_le_mul_of_nonneg_left this hR.le)
  have hLθ : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
      max θ 0 ≤ Lc := by
    rw [max_eq_left hθ]
    exact hL
  have h := K.toHistory.windowSeed_pointAnchor_C11WB hC2 haT hsT has hsmall hclock seedTrace
    ha₀ hpin y hR hgood j' h1 h2 hv2 hRq hΛ hCgq hbud hC1 hΛC hρC hRr hLθ hρL hav hvσ hσL
    hlate' x hxG hxv v' hwin hv'.2.le hv'.1
  rw [hO j' h1 h2]
  exact h

end TwoScale

section CeilCyl

/-- **ceiling 柱形接口（`_C11WB`，PROVED，无 binder；KSWEXIT `TopCeilCyl_C11KX` 的 localization 用）**：
双尺度定理的推论。区域点 `x` 若 slice 时刻 `R(v, x) ≤ M`、`Λ R_n ≤ M`，则在深度 `θΛ/M` 的窗口
`[v − θΛ/M, v]` 上 `d_{v′}(O j′, x) ≤ dσ + L/√R_n`（`q_x ≤ M/Λ` ⇒ `θ/q_x ≥ θΛ/M`）。即"已知 top ceiling `M`
的局部柱（深度 `c/M`，`c ≤ θΛ`）"上的窗口 seed closure 逐点付清——不要 hpick 整球，只要 `x` 点的 ceiling。 -/
theorem pickedCenterWindowSeed_ceilCyl_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ C : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2) :
    ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
    ∀ M : ℝ, Λ * Rn ≤ M → (K.toHistory.event j').incoming.flow.scalar v x ≤ M →
    ∀ v' ∈ Ioo (K.time j'.castSucc) v, v - θ * Λ / M ≤ v' →
      riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v') (O j') x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / Real.sqrt Rn) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx M hΛM hxM v' hv' hwin
  refine pickedCenterWindowSeed_twoScale_C11WB hC2 K haT hsT has hsmall hclock seedTrace ha₀ hpin
    y hR hgood hDc hθ hDcL hTL haS hlate hΛ hCgΛ hbud hC1 hΛC hρC hRr hL hρL hdl O hO j' v hv1 hv2
    hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' (le_trans ?_ hwin)
  have hM : 0 < M := (mul_pos hΛ hR).trans_le hΛM
  have hqM : max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) ≤ M / Λ := by
    refine max_le ?_ ?_
    · rw [le_div_iff₀ hΛ]
      linarith
    · exact div_le_div_of_nonneg_right hxM hΛ.le
  have hq0 : 0 < max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) :=
    hR.trans_le (le_max_left _ _)
  have h1 : θ / (M / Λ) ≤ θ / max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) :=
    div_le_div_of_nonneg_left hθ hq0 hqM
  have h2 : θ / (M / Λ) = θ * Λ / M := by
    field_simp
  linarith

end CeilCyl

section BaseContract

/-- **base 合同（`_C11WB`，PROVISIONAL[合同]；本身 BLOCKED，repair target 见 G2 docstring）**：
`PickedCenterWindowSeed_C11PT` 里双尺度定理**没有**付的那一块——区域点 `x`、窗口时刻 `v′` 在公共窗内
（`v − θ/R_n ≤ v′`）但**早于点自身窗** `v′ < v − θ/q_x`（`q_x = max(R_n, R(v, x)/Λ)`；只在高点
`R(v, x) > Λ R_n` 时非空）、`R(v′, x) > qthr` ⇒ `d_{v′}(O j′, x) ≤ D`。 -/
def WindowSeedBase_C11WB (Dw Dc Tc θ Rn Λ qthr : ℝ) (K : RetainedCoreHistory.{u})
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (y : (K.toHistory.stageAt σ).Carrier)
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier) (D : ℝ≥0∞) : Prop :=
  ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
  ∀ v' ∈ Ioo (K.time j'.castSucc) v, v - θ / Rn ≤ v' →
    v' < v - θ / max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) →
    qthr < (K.toHistory.event j').incoming.flow.scalar v' x →
    riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v') (O j') x ≤ D

/-- **inhabitant（`_C11WB`）**：`Dc = 0` 时区域球空，base 合同平凡成立。 -/
theorem windowSeedBase_zero_C11WB (Dw Tc θ Rn Λ qthr : ℝ) (K : RetainedCoreHistory.{u})
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (y : (K.toHistory.stageAt σ).Carrier)
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier) (D : ℝ≥0∞) :
    WindowSeedBase_C11WB Dw 0 Tc θ Rn Λ qthr K σ y O D := by
  intro j' v _ _ _ _ x₁ _ hjσ tr x hx
  exfalso
  have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal (0 / Real.sqrt Rn) := hx
  rw [zero_div, ENNReal.ofReal_zero] at hx'
  exact ENNReal.not_lt_zero hx'

/-- **G1 归约（`_C11WB`，PROVISIONAL[`WindowSeedBase_C11WB`]）**：PICKT1 真缺口
`PickedCenterWindowSeed_C11PT`（`D = dσ + L/√R_n`）⇐ 双尺度定理（PROVED）+ base 合同。证明 = 按
`v − θ/q_x ≤ v′` 分支：是 ⇒ `pickedCenterWindowSeed_twoScale_C11WB`；否 ⇒ `hbase`。
低点（`R(v, x) ≤ Λ R_n`）整个公共窗都走第一支，base 只在高点的 `[v − θ/R_n, v − θ/q_x)` 上被调用。 -/
theorem pickedCenterWindowSeed_of_base_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ C qthr : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2)
    (hbase : WindowSeedBase_C11WB Dw Dc Tc θ Rn Λ qthr K σ y O
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt Rn))) :
    PickedCenterWindowSeed_C11PT Dw Dc Tc θ Rn qthr K σ y O
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt Rn)) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hwin hq
  rcases le_or_gt (v - θ / max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ)) v' with
    h | h
  · exact pickedCenterWindowSeed_twoScale_C11WB hC2 K haT hsT has hsmall hclock seedTrace ha₀
      hpin y hR hgood hDc hθ hDcL hTL haS hlate hΛ hCgΛ hbud hC1 hΛC hρC hRr hL hρL hdl O hO j' v
      hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' h
  · exact hbase j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hwin h hq

end BaseContract

section FirstFailure

/-- **G2：base ⇐ first-failure guarded worldline ceiling（`_C11WB`，PROVED 条件形；`hceil` 本身 BLOCKED）**。
first-failure：对高点 `x`（`Λ R_n < R(v, x)`）在公共窗 `[v − θ/R_n, v]` 上跑核内 stopped first-exit，
`v* := inf{s : ∀ r ∈ [s, v], d_r(O, x) ≤ dσ + Lc/√R_n}`；`[v*, v]` 上 `x` Good ⇒ hgood 空间分量 + 局部传播把
`x` 点的标量界变成球界 `B_s(x, 1/√(C R_n))` 上 `R ≤ C R_n`（`windowScal_of_pickedTop_local_C11SC2` 以 `s` 自身为
anchor、`β = 0`），8.3(b) drift `≲ 16√K(C)·θ/√R_n ≤ Lc/√R_n` ⇒ `v*` 不在窗内 ⇒ closure。**在 `v*` 处缺的唯一一样**
= `hceil`：**x 仍 Good 的时刻 `s` 上 `R(s, x) ≤ Λ_L R_n`**（first-failure guarded worldline ceiling）。
`Λ_L` 只受
`6Λ_L ≤ C`、`2 + 16√K(C) θ ≤ Lc` 约束 ⇒ 可取 `Λ_L ~ c·Lc²/θ²`（`L → ∞` 时任意大），比 lead 原写的 (b)
（全球 slice 界、固定 `Λ` 且 `Ctime Λ θ ≤ 1/2`）弱得多；但在 `s = v` 处它仍含 slice 界 `R(v, x) ≤ Λ_L R_n`。

**为何 `hceil` 不能由局部结构推出（Bryant-tip 情景，R-C11-18/19 用）**：在 `[v*, v]` 上可用的全部局部数据——
hgood 时间分量 `|∂ₜR(·, x)| ≤ Ctime R²`（只在 `R > Cg R_n`）、空间分量 witness / `|∇R| ≤ C₂ R^{3/2}`、K0 seed、HI——
都与 `R(r, x) ≡ M`（`M ≫ L² R_n/θ²`，整个公共窗）相容：ODE 只把 `1/R` 的 Lipschitz 常数限为 `Ctime`，不给下降；
witness 是 ε-cap（steady soliton 尖端在固定点上 `R` 不随时间变），梯度界只在 `d ≲ 1/(C₂√(Cg R_n))` 内传播，
够不到区域半径 `Dc/√R_n`。此时 8.3(b) 给的 backward drift 速率 `~ √M`（cap 尖端径向 Ricci 积分 `~ √M`，
实际可达），在公共窗上累计 `~ θ√M/R_n ≫ L/√R_n` ⇒ closure 真的失败。排除该情景 = "距 `tr x₁`（`R ≤ A R_n`）
`Dc/√R_n` 之内没有 `R ≫ L² R_n` 的点" = 中心尺度 BCBD（Perelman 12.1 Step 2 / T1 结论）⇒ 循环。
用 T1 在较早 slice 付 `hceil` 是路线 (i)：T1(σ₁) 的 U 数据要 T1(σ₁ − θ) ⇒ 无穷后退，base 只能来自
per-slice 局部化的 T1 + slice 时刻 first-failure（取最早失败 slice，KSW 把 `Λ_L` 改进到 `QB·A ≪ Λ_L` 再用连续性），
而 hgood 时间域 `[σ − L²/R_n, σ]` 的底部没有起点 ⇒ OPEN。**repair target**：不付 `hceil`，改由 KSWEXIT guarded
ShortSLT 只在 ceiling 柱上消费 U 数据（`pickedCenterWindowSeed_ceilCyl_C11WB` 逐点付清），公共窗 base 退役（路线 (ii)）。 -/
theorem windowSeedBase_of_firstFailure_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ ΛL C qthr : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn)) (hΛ : 0 < Λ)
    (hΛL : 0 < ΛL) (hCgΛL : Cg ≤ ΛL) (hC1 : 1 ≤ C)
    (hΛC : 6 * ΛL ≤ C) (hρC : 2 * ΛL ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * ΛL)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2)
    (hceil : ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
      Λ * Rn < (K.toHistory.event j').incoming.flow.scalar v x →
      ∀ s : ℝ, v - θ / Rn ≤ s → s ≤ v → K.time j'.castSucc < s →
      (∀ s' ∈ Icc s v,
        riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric s') (O j') x ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt Rn)) →
      (K.toHistory.event j').incoming.flow.scalar s x ≤ ΛL * Rn) :
    WindowSeedBase_C11WB Dw Dc Tc θ Rn Λ qthr K σ y O
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt Rn)) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hwin hlt _hq
  have hsR : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hR
  have hρ0 := localPropagationRadius_pos hC2
  have hLc0 : 0 ≤ Lc := by
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        θ := by positivity
    linarith
  have hL0 : 0 ≤ L := by
    have h1 : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * ΛL)) := by positivity
    linarith
  have hLcL : Lc / Real.sqrt Rn ≤ L / Real.sqrt Rn := by
    have : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * ΛL)) := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  -- 高点：`v′ < v − θ/q_x` 且 `v − θ/R_n ≤ v′` ⇒ `q_x > R_n` ⇒ `Λ R_n < R(v, x)`
  have hhigh : Λ * Rn < (K.toHistory.event j').incoming.flow.scalar v x := by
    have hq : Rn < max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) := by
      by_contra hne
      have heq : max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) = Rn :=
        le_antisymm (not_lt.mp hne) (le_max_left _ _)
      rw [heq] at hlt
      linarith
    rcases lt_max_iff.mp hq with h | h
    · exact absurd h (lt_irrefl _)
    · rw [lt_div_iff₀ hΛ] at h
      linarith
  have hTθ : (Tc + θ) / Rn = Tc / Rn + θ / Rn := add_div _ _ _
  have hLR : (Tc + θ) / Rn ≤ L ^ 2 / Rn := div_le_div_of_nonneg_right hTL hR.le
  have haS' : (aSeed : ℝ) ≤ (σ : ℝ) - Tc / Rn := by
    have : 0 ≤ θ / Rn := div_nonneg hθ hR.le
    linarith
  have hvh : v ≤ K.toHistory.horizon := hvσ.trans σ.2.2
  let vI : Icc (0 : ℝ) K.toHistory.horizon :=
    ⟨v, (K.toHistory.time_nonneg _).trans hv1.le, hvh⟩
  have hact : K.toHistory.activeStage vI = j'.castSucc :=
    K.activeStage_eq_castSucc_C11PB j' vI hv1 hv2
  have havI : aSeed ≤ vI := by
    change (aSeed : ℝ) ≤ v
    linarith
  have h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc :=
    hact ▸ K.toHistory.activeStage_mono havI
  have h2 : j'.castSucc ≤ K.toHistory.activeStage Tn :=
    hjσ.trans (K.toHistory.activeStage_mono hsT)
  have hxG0 := seedDist_slice_C11WB K haT hsT has seedTrace y hR hL0 hDc
    hdl haS' j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2
  have hxG : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (seedTrace.point j'.castSucc h1 h2) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / 2 / Real.sqrt Rn) :=
    hxG0.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hDcL hsR.le)))
  have hL' : 2 * max 1 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        max θ 0 ≤ Lc := by
    rw [max_eq_left zero_le_one, max_eq_left hθ]
    linarith
  have hxx : x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) x
      (1 / Real.sqrt Rn) := by
    change riemannianEDistOf _ x x < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hQτ : 1 ≤ Rn * v' := by
    have : (σ : ℝ) - (Tc + θ) / Rn ≤ v' := by linarith
    exact hlate.trans (mul_le_mul_of_nonneg_left this hR.le)
  have hCgL : Cg * Rn ≤ ΛL * Rn := mul_le_mul_of_nonneg_right hCgΛL hR.le
  have hbud0 : (Ctime' : ℝ) * ΛL * 0 ≤ 1 / 2 := by
    rw [mul_zero]
    norm_num
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y with hdσdef
  rcases eq_or_ne dσ ⊤ with hT | hT
  · rw [hT, top_add]
    exact le_top
  have hdσ : dσ = ENNReal.ofReal dσ.toReal := (ENNReal.ofReal_toReal hT).symm
  have hcl := K.toHistory.seed_closure_firstExit_stopped_C11SC2 haT hsmall hclock seedTrace ha₀
    hpin j' h1 h2 x x hdσ ENNReal.toReal_nonneg hR le_rfl hC1 hRr hL' hxG hxx hwin hv'.2.le
    hv'.1 hv2 (by linarith) (hvσ.trans hsT) hQτ
    (fun s hs1 hsv hs0 hG z hz => by
      have hG' : ∀ s' ∈ Icc s v,
          riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric s') (O j') x ≤
            dσ + ENNReal.ofReal (Lc / Real.sqrt Rn) := by
        intro s' hs'
        rw [hO j' h1 h2]
        exact (hG s' hs').le
      have hxs := hceil j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx hhigh s hs1 hsv hs0 hG'
      exact windowScal_of_pickedTop_local_C11SC2 (v := s) (β := 0) hC2 K.toHistory haT hsT has
        seedTrace y hR hgood j' h1 h2 (hsv.trans_lt hv2) hR le_rfl hΛL hCgL hbud0 hΛC hρC hρL
        hLc0 (hsv.trans hvσ) x hxs s (by rw [zero_div, sub_zero]) le_rfl hs0 (by linarith)
        (by linarith) (fun r hr => (hG r ⟨hr.1, hr.2.trans hsv⟩).le) z hz)
  rw [hO j' h1 h2]
  exact hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL))

/-- **consumer（`_C11WB`）：G2 ∘ G1**——first-failure guarded ceiling `hceil` ⇒ PICKT1 真缺口
`PickedCenterWindowSeed_C11PT`（`D = dσ + L/√R_n`）。双尺度部分用 `Λ`（`Ctime Λ θ ≤ 1/2`）、`hceil` 部分用 `Λ_L`
（可 `~ L²`）；两组常数各自独立。 -/
theorem pickedCenterWindowSeed_of_firstFailure_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ C ΛL CL qthr : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hΛL : 0 < ΛL) (hCgΛL : Cg ≤ ΛL) (hC1L : 1 ≤ CL)
    (hΛCL : 6 * ΛL ≤ CL) (hρCL : 2 * ΛL ≤ localPropagationRadius C2' ^ 2 * CL)
    (hRrL : 2500 * max 1 (2 * Real.sqrt 3 * (CL / 2 + max CL (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hLL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (CL / 2 + max CL (2 * Real.exp 4)))) *
      θ ≤ Lc)
    (hρLL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * ΛL)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2)
    (hceil : ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
      Λ * Rn < (K.toHistory.event j').incoming.flow.scalar v x →
      ∀ s : ℝ, v - θ / Rn ≤ s → s ≤ v → K.time j'.castSucc < s →
      (∀ s' ∈ Icc s v,
        riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric s') (O j') x ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt Rn)) →
      (K.toHistory.event j').incoming.flow.scalar s x ≤ ΛL * Rn) :
    PickedCenterWindowSeed_C11PT Dw Dc Tc θ Rn qthr K σ y O
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (L / Real.sqrt Rn)) :=
  pickedCenterWindowSeed_of_base_C11WB hC2 K haT hsT has hsmall hclock seedTrace ha₀ hpin y hR
    hgood hDc hθ hDcL hTL haS hlate hΛ hCgΛ hbud hC1 hΛC hρC hRr hL hρL hdl O hO
    (windowSeedBase_of_firstFailure_C11WB hC2 K haT hsT has hsmall hclock seedTrace ha₀ hpin y hR
      hgood hDc hθ hDcL hTL haS hlate hΛ hΛL hCgΛL hC1L hΛCL hρCL hRrL hLL hρLL hdl O hO hceil)

end FirstFailure

section GuardForm

/-- **KSWEXIT guard 形接口（`_C11WB`，PROVED，无 binder）**：KSWEXIT 的逐点 guard
`2·Ctime·max(R(v, x), q)·(v − v′) ≤ 1`（top 时刻 = slice 时刻 `v`；`GuardKX_C11KX`，不 import，内联同式）+
`Λ R_n ≤ q` + `1 ≤ 2·Ctime·Λ·θ`（与 `Ctime Λ θ ≤ 1/2` 合起来即 `θ = 1/(2 Ctime Λ)`）⇒ 区域点 `x` 在 `v′` 处
`d_{v′}(O j′, x) ≤ dσ + L/√R_n`。= `pickedCenterWindowSeed_ceilCyl_C11WB` 取 `M := max(R(v, x), q)`。
分工（与 KSWEXIT 22:5x 对齐）：GuardKX 的 seed localization 由本定理 / `windowSeed_pointAnchor_C11WB` 付。 -/
theorem pickedCenterWindowSeed_guardKX_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ C : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2)
    (hθ2 : 1 ≤ 2 * (Ctime' : ℝ) * Λ * θ) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2) :
    ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
    ∀ q : ℝ, Λ * Rn ≤ q →
    ∀ v' ∈ Ioo (K.time j'.castSucc) v,
      2 * (Ctime' : ℝ) * max ((K.toHistory.event j').incoming.flow.scalar v x) q * (v - v') ≤ 1 →
      riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v') (O j') x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / Real.sqrt Rn) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx q hq v' hv' hg
  set M := max ((K.toHistory.event j').incoming.flow.scalar v x) q with hMdef
  have hqM : q ≤ M := le_max_right _ _
  have hM : 0 < M := ((mul_pos hΛ hR).trans_le hq).trans_le hqM
  refine pickedCenterWindowSeed_ceilCyl_C11WB hC2 K haT hsT has hsmall hclock seedTrace ha₀ hpin
    y hR hgood hDc hθ hDcL hTL haS hlate hΛ hCgΛ hbud hC1 hΛC hρC hRr hL hρL hdl O hO j' v hv1 hv2
    hvT hvσ x₁ hx₁ hjσ tr x hx M (hq.trans hqM) (le_max_left _ _) v' hv' ?_
  have hCt : 0 < (Ctime' : ℝ) := by
    rcases (Ctime'.coe_nonneg).lt_or_eq with h | h
    · exact h
    · rw [← h] at hθ2
      norm_num at hθ2
  have hvv : 0 ≤ v - v' := by linarith [hv'.2]
  have hkey : M * (v - v') ≤ θ * Λ := by
    have h2 : 2 * (Ctime' : ℝ) * (M * (v - v')) ≤ 2 * (Ctime' : ℝ) * (θ * Λ) := by
      have := hg.trans hθ2
      linarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hdiv : v - v' ≤ θ * Λ / M := by
    rw [le_div_iff₀ hM]
    linarith
  linarith

end GuardForm

section Footprint

/-- **consumer（`_C11WB`，PROVED）：κ 宏观 footprint ⇐ 双尺度 closure + top gate `hdσ`，无端点 Ricci**。
PICKSEL `pickedCenterFootprint_P6PS` 的 footprint `d_τ(O, x) < A·r` 原本经 I.8.3(b) + 端点 Ricci `hRic`
（OPEN owner DIST）得到；在点自身窗口 `τ ∈ [v − θ/q_x, v]` 上（路线 (ii) / KSWEXIT guard 后缀 ⊆ 此窗），
双尺度定理直接给 `d_τ(O, x) ≤ dσ + L/√R_n < dσ + (L+1)/√R_n ≤ A·r`——`hRic` 在 guard 集上退役。 -/
theorem pickedCenterFootprint_twoScale_C11WB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L Lc : ℝ} (hR : 0 < Rn)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {Dw Dc Tc θ Λ C A : ℝ} (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hDcL : L / 4 + Dc ≤ Lc / 2)
    (hTL : Tc + θ ≤ L ^ 2) (haS : (aSeed : ℝ) ≤ (σ : ℝ) - (Tc + θ) / Rn)
    (hlate : 1 ≤ Rn * ((σ : ℝ) - (Tc + θ) / Rn))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * θ ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hdl : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
        (σ : ℝ) - Tc / Rn ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 4 / Real.sqrt Rn))
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ K.toHistory.activeStage Tn), O j' = seedTrace.point j'.castSucc h1 h2)
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt Rn) ≤ ENNReal.ofReal (A * r)) :
    ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
      (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
    ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
        (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
      (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
    ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
    ∀ v' ∈ Ioo (K.time j'.castSucc) v,
      v - θ / max Rn ((K.toHistory.event j').incoming.flow.scalar v x / Λ) ≤ v' →
      riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v') (O j') x <
        ENNReal.ofReal (A * r) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hwin
  have h := pickedCenterWindowSeed_twoScale_C11WB hC2 K haT hsT has hsmall hclock seedTrace ha₀
    hpin y hR hgood hDc hθ hDcL hTL haS hlate hΛ hCgΛ hbud hC1 hΛC hρC hRr hL hρL hdl O hO j' v
    hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hwin
  have hfin : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y ≠ ⊤ := by
    intro hT
    rw [hT, top_add] at hdσ
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hdσ)
  have hs : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hR
  refine lt_of_le_of_lt h (lt_of_lt_of_le ?_ hdσ)
  refine ENNReal.add_lt_add_left hfin ((ENNReal.ofReal_lt_ofReal_iff (div_pos ?_ hs)).2 ?_)
  · have hρ0 := localPropagationRadius_pos hC2
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        θ := by positivity
    have h1 : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) := by positivity
    linarith
  · exact div_lt_div_of_pos_right (by linarith) hs

end Footprint

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallKappaC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BallContainmentSameSlab_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceScalarControl_P6L

/-!
# 窗口 seed closure 的 first-exit producer（O-CH11-SEEDCL G1，后缀 `_C11SC`）

PICKBALL G4 的 **hseed** `PickedBallWindowSeed_C11PB β Rad qthr K j v w O D` 与 G5 的无阈值形
**hseedAll** `PickedBallWindowSeedAll_C11PB β Rad K j v w O D`（`x ∈ B_v(w, Rad/√q)`、窗口
`[v − β/q, v]` ∩ slab ⇒ `d_τ(O, x) ≤ D`）在 **picked-ball** 处（hpick 门控）的生产：
* 核 = 单 history `seed_closure_firstExit_P6L4`（`Q := q = R(v, w)`、`B := β`；K0 种子端
  `|Rm| ≤ r⁻²`；I.8.3(b) 首出时刻；漂移 `8√K β/√R_n` 由 `L ≥ 2Rad⁺ + 16√K β⁺` 吸收）；初始余量
  = 中心 ExitGuard L/2（`d_v(O, w) ≤ dσ + (L/2)/√R_n`）+ 球半径 `Rad/√q`。
* 核的 U 端标量界 `hscal`（`B_s(x, 1/√(Cq))` 上 `R ≤ Cq`）**无条件**由 picked-ball 数据给出
  （`ObservedHistory.windowScal_of_pickedTop_C11SC`）：
  1. hpick：`Ω := B_v(w, A/√q)` 上 `R(v, ·) ≤ Λq`；
  2. slab 内单点 ODE（event `j` 的 `DerivativeBoundBefore`，`qcan ≤ Λq`，预算
     `Ctime·Λ·β ≤ 1/2`）⇒ `Ω × [v − β/q, v]` 上 `R ≤ 2Λq`
     （`scalar_le_two_mul_of_derivativeBound_C11SC`；slab 内 label 不动）；
  3. Hamilton–Ivey（`sqrt_rmNormSq_le_of_HI_scalar_C11G`）⇒ `|Rm| ≤ Kr q`，
     `Kr := 2√3(2Λ/2 + max (2Λ) (2e⁴))`；
  4. 度量比较 `g(v) ≤ e^{18 Kr β} g(s)` 于 `Ω` + first-exit 球包含
     （`riemannianBallOf_subset_of_inner_le_mul_on_P6L2`）：`Rad + e^{9 Kr β} ≤ A` ⇒
     `B_s(x, 1/√(Cq)) ⊆ Ω`；
  5. `2Λ ≤ C` ⇒ `R(s, z) ≤ Cq`。
* **G1a `pickedBallWindowSeedAll_of_firstExit_C11SC`** ⇒ hseedAll 逐字；**G1
  `pickedBallWindowSeed_of_firstExit_C11SC`** ⇒ hseed 逐字（`.toWindowSeed`，阈值 `qthr` 任意）。
  `O = seedTrace.point j⁻`、`D = dσ + L/√R_n`。唯一非 supply 输入 = PICKBALL 已登记的 hpick
  `PickedBallTop_C11PB Λ A`（PROVISIONAL，owner selection / point-picking）；不用 hgood。
* consumer `pickedBallGrad_of_firstExit_C11SC`：G1 + PICKBALL G4 `pickedBallGrad_of_hgood_C11PB`
  ⇒ picked-ball 的 hgrad（`PickedBallGrad_C11PB`）⇐ hgood + hpick + K0 种子 + 导数界 + HI + 算术。

**G2（BLOCKED，lead 裁定 (a)）**：`shallowSliceRC_of_pickedBall_seed_C11PB` 的 `hseedPB` 对**每个**
合格 `w` 与**每个** `Rad` 要窗口 closure；本文件只在 hpick 成立处生产（任意 `w` 的 hpick ≈ T1 自身的
slice 标量结论 ⇒ 循环；`Λ` 被 `θ₀` 预算钉死而 `Rad` 任意）。repair target = T1 壳
`hsliceR_lateHI_core_short_C11KS` 改 point-picking 形（lead 登记 PICKT1，另开）。
非循环：import PICKBALL G5（→ G4、G1–G3、KSW2、`HUVKappaClosure_P6L3`）、`HclosFirstExit_P6L4`、
`BallContainmentSameSlab_P6L2`、`BackwardTraceScalarControl_P6L`；不经 hscalU / hclosG / hclosC /
hUVC 生产者 / CanonicalLateCore / hspine（审计做传递依赖名字扫描）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section WindowScal

/-- `BackwardTraceScalarControl_P6L` 私有引理 `le_two_mul_of_abs_inv_max_sub_le_P6L` 的公开副本（`_C11SC`）：
`|1/max(M, R) − 1/max(M, Rt)| ≤ C Δ`、`Rt ≤ M`、`C M Δ ≤ 1/2` ⇒ `R ≤ 2M`。 -/
theorem le_two_mul_of_abs_inv_max_sub_le_C11SC {M R Rt Δ : ℝ} {C : ℝ≥0} (hM : 0 < M)
    (hRt : Rt ≤ M) (hrec : |(max M R)⁻¹ - (max M Rt)⁻¹| ≤ C * Δ)
    (htime : C * M * Δ ≤ 1 / 2) : R ≤ 2 * M := by
  rw [max_eq_left hRt] at hrec
  have hlow := (abs_le.mp hrec).1
  have hhalf : C * Δ ≤ (2 * M)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 2 * M)]
    nlinarith
  have htwo : M⁻¹ = 2 * (2 * M)⁻¹ := by field_simp
  have hinv : (2 * M)⁻¹ ≤ (max M R)⁻¹ := by linarith
  exact (le_max_right M R).trans
    ((inv_le_inv₀ (by positivity : 0 < 2 * M) (hM.trans_le (le_max_left M R))).mp hinv)

/-- **slab 内单点 ODE（`_C11SC`）**：event `j` 的 `DerivativeBoundBefore Ctime qcan`（`qcan ≤ M`）、
`R(v, y) ≤ M`、`time j⁻ ≤ s ≤ v < time j⁺`、`Ctime · M · (v − s) ≤ 1/2` ⇒ `R(s, y) ≤ 2M`。 -/
theorem ObservedHistory.scalar_le_two_mul_of_derivativeBound_C11SC (H : ObservedHistory.{u})
    (j : Fin H.eventCount) {Ctime : ℝ≥0} {qcan : ℝ}
    (hder : (H.event j).incoming.DerivativeBoundBefore Ctime qcan (H.time j.succ))
    {v M s : ℝ} (hM : 0 < M) (hqcan : qcan ≤ M) (hv2 : v < H.time j.succ)
    (hs1 : H.time j.castSucc ≤ s) (hsv : s ≤ v) (hbud : (Ctime : ℝ) * M * (v - s) ≤ 1 / 2)
    (y : (H.stage j.castSucc).Carrier) (hy : (H.event j).incoming.flow.scalar v y ≤ M) :
    (H.event j).incoming.flow.scalar s y ≤ 2 * M := by
  have hL := (H.event j).incoming.lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore_P6L
    hM hqcan hv2 y (fun r hr hR => hder y r ⟨hr.1, hr.2.trans hv2⟩ hR)
  have hd := hL.dist_le_mul s ⟨hs1, hsv⟩ v ⟨hs1.trans hsv, le_rfl⟩
  have hsv' : |s - v| = v - s := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [Real.dist_eq, Real.dist_eq, hsv'] at hd
  exact le_two_mul_of_abs_inv_max_sub_le_C11SC hM hy hd hbud

/-- **U 端窗口标量界 ⇐ picked-ball 球顶（`_C11SC`，PROVED）**：`Ω := B_v(w, A/√q)` 上 `R(v, ·) ≤ Λq`（hpick）、
event `j` 导数界（`qcan ≤ Λq`）、预算 `Ctime Λ β ≤ 1/2`、Hamilton–Ivey、`Rad + e^{9 Kr β} ≤ A`
（`Kr := 2√3(2Λ/2 + max (2Λ) (2e⁴))`）、`1 ≤ C`、`2Λ ≤ C`；`x ∈ B_v(w, Rad/√q)`、`s ∈ [v − β/q, v]`
（`time j⁻ < s`、`q s ≥ 1`）⇒ `B_s(x, 1/√(Cq))` 上 `R(s, ·) ≤ Cq`
（= `seed_closure_firstExit_P6L4` 的 `hscal`，无 seed-Good 条件）。 -/
theorem ObservedHistory.windowScal_of_pickedTop_C11SC (H : ObservedHistory.{u})
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (j : Fin H.eventCount) {Ctime : ℝ≥0} {qcan : ℝ}
    (hder : (H.event j).incoming.DerivativeBoundBefore Ctime qcan (H.time j.succ))
    {v q Λ A Rad β C : ℝ} (hv2 : v < H.time j.succ) (hq : 0 < q) (hΛ : 0 < Λ)
    (hqcan : qcan ≤ Λ * q) (hbud : (Ctime : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 2 * Λ ≤ C)
    (hrad : Rad + Real.exp (9 * (2 * Real.sqrt 3 * (2 * Λ / 2 + max (2 * Λ) (2 * Real.exp 4))) *
      β) ≤ A)
    (w x : (H.stage j.castSucc).Carrier)
    (htop : ∀ z ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
        (A / Real.sqrt q), (H.event j).incoming.flow.scalar v z ≤ Λ * q)
    (hxw : x ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt q))
    (s : ℝ) (hs1 : v - β / q ≤ s) (hsv : s ≤ v) (hs0 : H.time j.castSucc < s)
    (hqs : 1 ≤ q * s) (z : (H.stage j.castSucc).Carrier)
    (hz : riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z <
      ENNReal.ofReal (1 / Real.sqrt (C * q))) :
    (H.event j).incoming.flow.scalar s z ≤ C * q := by
  set Kr := 2 * Real.sqrt 3 * (2 * Λ / 2 + max (2 * Λ) (2 * Real.exp 4)) with hKr
  have hmax0 : 0 ≤ max (2 * Λ) (2 * Real.exp 4) :=
    le_trans (by positivity) (le_max_right _ _)
  have hKr0 : 0 ≤ Kr := by positivity
  have hΛq : 0 < Λ * q := mul_pos hΛ hq
  have hCq : 0 < C * q := mul_pos (by linarith) hq
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  -- 时间：`q (v − s) ≤ β`
  have hqvs : q * (v - s) ≤ β := by
    have hvs : v - s ≤ β / q := by linarith
    have h := mul_le_mul_of_nonneg_left hvs hq.le
    rwa [mul_div_cancel₀ _ hq.ne'] at h
  have hs0' : 0 < s := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  -- (2) ODE：`Ω × [s, v]` 上 `R ≤ 2Λq`
  have hode : ∀ y ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
      (A / Real.sqrt q), ∀ r ∈ Icc s v, (H.event j).incoming.flow.scalar r y ≤ 2 * (Λ * q) := by
    intro y hy r hr
    refine H.scalar_le_two_mul_of_derivativeBound_C11SC j hder hΛq hqcan hv2
      (hs0.le.trans hr.1) hr.2 ?_ y (htop y hy)
    have hvr : q * (v - r) ≤ β := by nlinarith [hr.1]
    have hCt : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
    calc (Ctime : ℝ) * (Λ * q) * (v - r) = Ctime * Λ * (q * (v - r)) := by ring
      _ ≤ Ctime * Λ * β := mul_le_mul_of_nonneg_left hvr (by positivity)
      _ ≤ 1 / 2 := hbud
  -- (3) Hamilton–Ivey：`|Rm|² ≤ (Kr q)²`
  have hrm : ∀ y ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
      (A / Real.sqrt q), ∀ r ∈ Icc s v,
      normSq0S (H.stageMetric j.castSucc r) y 4 (metricRm04At (H.stageMetric j.castSucc r) y) ≤
        (Kr * q) ^ 2 := by
    intro y hy r hr
    have hr0 : 0 < r := hs0'.trans_le hr.1
    let τI : Icc (0 : ℝ) H.horizon :=
      ⟨r, hr0.le, hr.2.trans (hv2.le.trans (H.time_le_horizon_at _))⟩
    have hk : H.activeStage τI = j.castSucc :=
      H.activeStage_eq_castSucc_C11G j τI (hs0.le.trans hr.1) (lt_of_le_of_lt hr.2 hv2)
    have hfix := H.inFixedHI_stage_C11G hpin τI j.castSucc hk y
    rw [ObservedHistory.stageMetric_castSucc_apply] at hfix ⊢
    have hsc : metricScalarAt ((H.event j).incoming.flow.base.metric r) y ≤ (2 * Λ) * q := by
      have h := hode y hy r hr
      change (H.event j).incoming.flow.scalar r y ≤ (2 * Λ) * q
      linarith
    have hqr : 1 ≤ q * r := hqs.trans (mul_le_mul_of_nonneg_left hr.1 hq.le)
    have h := sqrt_rmNormSq_le_of_HI_scalar_C11G _ y ha₀ hr0 hq hqr (by positivity) hfix hsc
    have h' : Real.sqrt (normSq0S ((H.event j).incoming.flow.base.metric r) y 4
        (metricRm04At ((H.event j).incoming.flow.base.metric r) y)) ≤ Kr * q := h
    have hN := Real.sqrt_nonneg (normSq0S ((H.event j).incoming.flow.base.metric r) y 4
      (metricRm04At ((H.event j).incoming.flow.base.metric r) y))
    by_cases h0 : 0 ≤ normSq0S ((H.event j).incoming.flow.base.metric r) y 4
      (metricRm04At ((H.event j).incoming.flow.base.metric r) y)
    · rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ hN h' 2
    · nlinarith [sq_nonneg (Kr * q)]
  -- (4) 度量比较 `g(v) ≤ e^{18 Kr β} g(s)` 于 `Ω`
  have hnext : ∀ i : Fin H.eventCount, j.castSucc = i.castSucc → v < H.time i.succ := by
    intro i hi
    obtain rfl := Fin.castSucc_injective _ hi
    exact hv2
  have hvh : v ≤ H.horizon := hv2.le.trans (H.time_le_horizon_at _)
  have hexp : Real.exp (9 * Kr * β) ^ 2 = Real.exp (18 * Kr * β) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hQ : ∀ y ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
      (A / Real.sqrt q), ∀ ξ : TangentSpace ThreeModel y,
      ((H.event j).incoming.flow.base.metric v).inner y ξ ξ ≤
        Real.exp (9 * Kr * β) ^ 2 * ((H.event j).incoming.flow.base.metric s).inner y ξ ξ := by
    intro y hy ξ
    have h := H.stageMetric_inner_le_exp_of_normSq_le j.castSucc y (a := s) (b := v) hs0.le
      hnext hvh (C := (Kr * q) ^ 2) (fun r hr => hrm y hy r hr) ⟨hsv, le_rfl⟩ ⟨le_rfl, hsv⟩ ξ
    rw [ObservedHistory.stageMetric_castSucc_apply,
      ObservedHistory.stageMetric_castSucc_apply] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (metric_inner_self_nonneg _ _ _))
    rw [hexp, Real.sqrt_sq (mul_nonneg hKr0 hq.le), abs_of_nonneg (by linarith)]
    apply Real.exp_le_exp.2
    have h18 := mul_le_mul_of_nonneg_left hqvs (by positivity : (0 : ℝ) ≤ 18 * Kr)
    nlinarith
  -- (4′) first-exit 球包含：`B_s(x, ℓ) ⊆ B_v(x, e^{9Krβ} ℓ) ⊆ Ω`
  have hr0 : 0 < Rad / Real.sqrt q :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le (α := ENNReal)) hxw)
  have hℓ : 0 < 1 / Real.sqrt (C * q) := by
    have := Real.sqrt_pos.2 hCq
    positivity
  have hℓq : 1 / Real.sqrt (C * q) ≤ 1 / Real.sqrt q :=
    one_div_le_one_div_of_le hsq (Real.sqrt_le_sqrt (by nlinarith))
  have hsqe : Real.sqrt (Real.exp (9 * Kr * β) ^ 2) = Real.exp (9 * Kr * β) :=
    Real.sqrt_sq (Real.exp_pos _).le
  have hΩ : riemannianBallOf ((H.event j).incoming.flow.base.metric v) x
      (Real.sqrt (Real.exp (9 * Kr * β) ^ 2) * (1 / Real.sqrt (C * q))) ⊆
      riemannianBallOf ((H.event j).incoming.flow.base.metric v) w (A / Real.sqrt q) := by
    intro y hy
    rw [hsqe] at hy
    have hy' : riemannianEDistOf ((H.event j).incoming.flow.base.metric v) x y <
        ENNReal.ofReal (Real.exp (9 * Kr * β) * (1 / Real.sqrt (C * q))) := hy
    have hx' : riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x <
        ENNReal.ofReal (Rad / Real.sqrt q) := hxw
    change riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w y <
      ENNReal.ofReal (A / Real.sqrt q)
    have hb : Rad / Real.sqrt q + Real.exp (9 * Kr * β) * (1 / Real.sqrt (C * q)) ≤
        A / Real.sqrt q := by
      have h1 : Real.exp (9 * Kr * β) * (1 / Real.sqrt (C * q)) ≤
          Real.exp (9 * Kr * β) * (1 / Real.sqrt q) :=
        mul_le_mul_of_nonneg_left hℓq (Real.exp_pos _).le
      have h2 : Rad / Real.sqrt q + Real.exp (9 * Kr * β) * (1 / Real.sqrt q) =
          (Rad + Real.exp (9 * Kr * β)) / Real.sqrt q := by ring
      have h3 : (Rad + Real.exp (9 * Kr * β)) / Real.sqrt q ≤ A / Real.sqrt q :=
        div_le_div_of_nonneg_right hrad hsq.le
      linarith
    calc riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w y
        ≤ riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x +
          riemannianEDistOf ((H.event j).incoming.flow.base.metric v) x y :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (Rad / Real.sqrt q) +
          ENNReal.ofReal (Real.exp (9 * Kr * β) * (1 / Real.sqrt (C * q))) :=
          ENNReal.add_lt_add hx' hy'
      _ = ENNReal.ofReal (Rad / Real.sqrt q +
          Real.exp (9 * Kr * β) * (1 / Real.sqrt (C * q))) :=
          (ENNReal.ofReal_add hr0.le (by positivity)).symm
      _ ≤ ENNReal.ofReal (A / Real.sqrt q) := ENNReal.ofReal_le_ofReal hb
  have hzΩ := hΩ (DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul_on_P6L2
    ((H.event j).incoming.flow.base.metric s) ((H.event j).incoming.flow.base.metric v) x
    (by positivity) hℓ _ hΩ hQ hz)
  -- (5) `R(s, z) ≤ 2Λq ≤ Cq`
  have hzs := hode z hzΩ s ⟨le_rfl, hsv⟩
  have hCq' := mul_le_mul_of_nonneg_right hΛC hq.le
  linarith

end WindowScal

section SeedClosure

/-- **G1a：picked-ball 窗口 seed closure，无阈值形 hseedAll（`_C11SC`，PROVISIONAL：binder = hpick）**：
`pickedBallWindowSeed_of_firstExit_C11SC` 的同一组输入 ⇒ PICKBALL G5 的 `PickedBallWindowSeedAll_C11PB` 逐字
（闭窗 `τ ∈ [v − β/q, v]`、`time j⁻ < τ`，无曲率阈值）。核 = `seed_closure_firstExit_P6L4`，`hscal` =
`windowScal_of_pickedTop_C11SC`（无 seed-Good 条件）。 -/
theorem pickedBallWindowSeedAll_of_firstExit_C11SC (K : RetainedCoreHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (j : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn) {Ctime : ℝ≥0} {qcan : ℝ}
    (hder : (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan (K.time j.succ))
    (v : ℝ) (hv2 : v < K.time j.succ) (w : (K.stage j.castSucc).Carrier)
    {dσ : ℝ≥0∞} {R L β Rad Λ A C : ℝ} (hR : 0 < R)
    (hRq : R ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ)
    (hqcan : qcan ≤ Λ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C) (hΛC : 2 * Λ ≤ C)
    (hrad : Rad + Real.exp (9 * (2 * Real.sqrt 3 * (2 * Λ / 2 + max (2 * Λ) (2 * Real.exp 4))) *
      β) ≤ A)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤ L)
    (hav : (aSeed : ℝ) ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hvT : v ≤ Tn)
    (hlate : 1 ≤ R * (v - β / (K.toHistory.event j).incoming.flow.scalar v w))
    (hwv : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (htop : PickedBallTop_C11PB Λ A K j v w) :
    PickedBallWindowSeedAll_C11PB β Rad K j v w (seedTrace.point j.castSucc h1 h2)
      (dσ + ENNReal.ofReal (L / Real.sqrt R)) := by
  intro x hx v' hwin hv'v hv'1
  have hq : 0 < (K.toHistory.event j).incoming.flow.scalar v w := hR.trans_le hRq
  rcases eq_or_ne dσ ⊤ with hT | hT
  · rw [hT, top_add]
    exact le_top
  have hdσ : dσ = ENNReal.ofReal dσ.toReal := (ENNReal.ofReal_toReal hT).symm
  have hlate' : ∀ s : ℝ, v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ s →
      1 ≤ (K.toHistory.event j).incoming.flow.scalar v w * s := by
    intro s hs
    have hpos : 0 < v - β / (K.toHistory.event j).incoming.flow.scalar v w := by
      by_contra hneg
      have hle := not_lt.mp hneg
      nlinarith
    have h1' : R * (v - β / (K.toHistory.event j).incoming.flow.scalar v w) ≤ R * s :=
      mul_le_mul_of_nonneg_left hs hR.le
    have h2' : R * s ≤ (K.toHistory.event j).incoming.flow.scalar v w * s :=
      mul_le_mul_of_nonneg_right hRq (hpos.le.trans hs)
    linarith
  exact K.toHistory.seed_closure_firstExit_P6L4 haT hsmall hclock seedTrace ha₀ hpin j h1 h2 w x
    hdσ ENNReal.toReal_nonneg hR hRq hC1 hRr hL hwv hx hwin hv'v hv'1 hv2 (hav.trans hwin)
    hvT (hlate' v' hwin)
    (fun s hs1 hsv hs0 _ z hz => K.toHistory.windowScal_of_pickedTop_C11SC ha₀ hpin j hder hv2 hq
      hΛ hqcan hbud hC1 hΛC hrad w x htop hx s hs1 hsv hs0 (hlate' s hs1) z hz)

/-- **G1：picked-ball 窗口 seed closure（`_C11SC`，PROVISIONAL：binder = hpick
`PickedBallTop_C11PB Λ A`）**。
K0 种子（`hsmall` / `hclock` / `seedTrace`）+ Hamilton–Ivey `hpin` + event `j` 导数界 `hder`（`qcan ≤ Λq`）
+ 预算 `Ctime Λ β ≤ 1/2` + 中心 ExitGuard `d_v(O, w) ≤ dσ + (L/2)/√R`（`R ≤ q := R(v, w)`）+ 算术
（`Rad + e^{9 Kr β} ≤ A`、`1 ≤ C`、`2Λ ≤ C`、`2500 K ≤ R r²`、`L ≥ 2Rad⁺ + 16√K β⁺`，`K` 同核）+ 时间域
（`aSeed ≤ v − β/q`、`v ≤ Tn`、`1 ≤ R (v − β/q)`）+ **hpick** ⇒ `PickedBallWindowSeed_C11PB` 逐字
（`O = seedTrace.point j⁻`、`D = dσ + L/√R`，阈值 `qthr` 任意）。 -/
theorem pickedBallWindowSeed_of_firstExit_C11SC (K : RetainedCoreHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (a₀ + t) x)
    (j : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn) {Ctime : ℝ≥0} {qcan : ℝ}
    (hder : (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan (K.time j.succ))
    (v : ℝ) (hv2 : v < K.time j.succ) (w : (K.stage j.castSucc).Carrier)
    {dσ : ℝ≥0∞} {R L β Rad qthr Λ A C : ℝ} (hR : 0 < R)
    (hRq : R ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ)
    (hqcan : qcan ≤ Λ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C) (hΛC : 2 * Λ ≤ C)
    (hrad : Rad + Real.exp (9 * (2 * Real.sqrt 3 * (2 * Λ / 2 + max (2 * Λ) (2 * Real.exp 4))) *
      β) ≤ A)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤ L)
    (hav : (aSeed : ℝ) ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hvT : v ≤ Tn)
    (hlate : 1 ≤ R * (v - β / (K.toHistory.event j).incoming.flow.scalar v w))
    (hwv : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (htop : PickedBallTop_C11PB Λ A K j v w) :
    PickedBallWindowSeed_C11PB β Rad qthr K j v w (seedTrace.point j.castSucc h1 h2)
      (dσ + ENNReal.ofReal (L / Real.sqrt R)) :=
  (pickedBallWindowSeedAll_of_firstExit_C11SC K haT hsmall hclock seedTrace ha₀ hpin j h1 h2 hder v
    hv2 w hR hRq hΛ hqcan hbud hC1 hΛC hrad hRr hL hav hvT hlate hwv htop).toWindowSeed

/-- **consumer（`_C11SC`）：picked-ball hgrad ⇐ hgood + G1**。PICKBALL G4
`pickedBallGrad_of_hgood_C11PB` 的 binder `hseed`（`D = d_σ(O_σ, y) + L/√R_n`，阈值 `Cg R_n`）
由 G1 在选点处供给：hgrad `PickedBallGrad_C11PB β Rad (Cg R_n) Cgrad` ⇐ hgood + `C2 ≤ Cgrad`
+ 时间域 + K0 种子（index `n`）+ HI + 导数界 + 预算 + ExitGuard L/2 + 算术 + hpick。 -/
theorem pickedBallGrad_of_firstExit_C11SC {Cg β : ℝ} {Cgrad : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) (n : ℕ) {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage t) t)
        (a₀ + t) x)
    (j : Fin (K n).eventCount) (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n)) {Ctime : ℝ≥0} {qcan : ℝ}
    (hder : ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan
      ((K n).time j.succ))
    (v : ℝ) (hv2 : v < (K n).time j.succ) (w : ((K n).stage j.castSucc).Carrier)
    {Rad Λ A C : ℝ} (hR : 0 < R n)
    (hRq : R n ≤ ((K n).toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ)
    (hqcan : qcan ≤ Λ * ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C) (hΛC : 2 * Λ ≤ C)
    (hrad : Rad + Real.exp (9 * (2 * Real.sqrt 3 * (2 * Λ / 2 + max (2 * Λ) (2 * Real.exp 4))) *
      β) ≤ A)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤
        L n)
    (hav : (aSeed n : ℝ) ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hvs : v ≤ (σ n : ℝ))
    (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hlate : 1 ≤ R n * (v - β / ((K n).toHistory.event j).incoming.flow.scalar v w))
    (hwv : riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
      ((seedTrace n).point j.castSucc h1 h2) w ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)))
    (htop : PickedBallTop_C11PB Λ A (K n) j v w) :
    PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) j v w :=
  pickedBallGrad_of_hgood_C11PB K hgood hC2 n j v hv2 h1 h2 w hav hvs hvL
    (pickedBallWindowSeed_of_firstExit_C11SC (K n) (haT n) hsmall hclock (seedTrace n) ha₀ hpin j
      h1 h2 hder v hv2 w hR hRq hΛ hqcan hbud hC1 hΛC hrad hRr hL hav (hvs.trans (hsT n)) hlate
      hwv htop)

end SeedClosure

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

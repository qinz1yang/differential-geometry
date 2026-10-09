import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedClosureC11SC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FirstExitCoreCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGoodCg_P6LS3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.LocalPropagation_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.FirstExitUSC_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.FirstExitDistanceP6M4

/-!
# 窗口 seed closure 的局域导数版（O-CH11-SEEDCL2 G1/G2，后缀 `_C11SC2`；R-C11-17 D-3(iii)/D-9）

SEEDCL G1 `windowScal_of_pickedTop_C11SC`（`P6PickedBallSeedClosureC11SC.lean:95–242`）的 step (2) 在
`Ω = B_v(w, A/√q)` × `[s, v]` 上用 slab 全域 `DerivativeBoundBefore Ctime qcan` + `qcan ≤ Λq` 取标量界。
本文件把这份旧导数背景迁移到 **q_sel 合同**：导数只在 `R > Λq`（`≥ Cg·R`）处要，且只来自 selection
`hgood` 的时间分量（`HasSpatialCanonicalTimeControl.2`）。与 `hRicC_of_hgood_ceiling_CXJD` **结构同构**：
1. **worldline ceiling**（`ObservedHistory.scalar_le_two_mul_of_localDeriv_C11SC2`）：同 slab 内 `x` 不动，
   沿 `r ↦ R(r, x)` 做截断倒数 ODE（树内 `lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc`，即 CXJT0
   ceiling 机制），ceiling `B = Λq` 的初值由 hpick 在 `x` 处给（`R(v, x) ≤ Λq`），导数只在 `R(r, x) > Λq`
   处求值，由 `ObservedHistory.deriv_of_hgood_slab_Cg_C11SC2`（hgood 时间分量的 event-`j` 形）供给，
   需要 `x ∈ U_r := {d_r(O, ·) ≤ d_σ + L/√R}`；
2. **时刻 `s` 的球控制**改用 hgood 空间分量：`gradient_of_hgood_slab_Cg_P6LS3` +
   `scalar_le_on_ball_of_gradient_bound_P6L` ⇒ `B_s(x, ρ/√(2Λq))` 上 `R ≤ 6Λq`（`ρ =
   localPropagationRadius C₂′`）⇒ `hscal`（`6Λ ≤ C`、`2Λ ≤ ρ² C`）。旧版的 Ω 加厚、度量比较、
   `e^{9 Kr β}`、Hamilton–Ivey 标量→Rm 全部不再需要；hpick 只需覆盖 `B_v(w, Rad/√q)`。
3. **停止条件 `x ∈ U_r` 在定理内部由 first-exit 闭合**：`ObservedHistory.firstExit_distance_stopped_C11SC2`
   （`firstExit_window_CXJD` 核 + `edist_le_add_of_slab_ricci_P6M4` + `edist_lt_near_left_P6L4`；
   `hRic` 只在 `[s, t]` 上已 Good 时要）与 `ObservedHistory.seed_closure_firstExit_stopped_C11SC2`
   （`seed_closure_firstExit_P6L4` 的 stopped 副本：`hscal` 只在 `[s, v]` 上 `x` 已 Good 时要）。
   closure 预算 `Lc`、hgood 区域 `L`，`Lc + 2ρ/√(2Λ) ≤ L`；结论 `D = d_σ + L/√R` 逐字
   （中心 ExitGuard `hwv` 改为 `Lc/2`）。
4. **G2 consumer** `pickedBallGrad_of_firstExit_local_C11SC2`：G1 喂 PICKBALL G4
   `pickedBallGrad_of_hgood_C11PB`（同一 hgood 同时给 G1 的导数与 G4 的 witness/梯度）。
5. **G3**（文件末 example）：PICKT1 `PickedCenterWindowSeed_C11PT` 与 G1 的关系——核引理对 `Q` 泛型，
   中心尺度 `Q := R_n` 的实例 = 路线 (i) 的**单 slice 步**（slice 时刻界 ⇒ 该 slice 的窗口 closure），
   不是 base case；见文件末注释。

**直接复用 `hRicC_of_hgood_ceiling_CXJD` 不可行**：它把 trace 端点时刻绑死为 hgood 锚 `σ`（`hz` 在 `σ`、
ceiling `Q_b·R`），是 Icc/stageAt 的跨 slab trace 形；SEEDCL 的端点是 `(v, x)`（`v ≤ σ`，event-`j` 形，
ceiling `Λq`，`q = R(v, w) ≥ R`）。故复用其零件（P6LS3 梯度、P6L 局部传播、P6L4 端点 Ricci、CXJD
first-exit 核），不复用定理本身。

**防循环（G2 证书）**：本文件输入 = hgood（Step 1 selection）+ K0 seed（`hsmall`/`hclock`/`seedTrace`）+
HI `hpin` + hpick（`PickedBallTop_C11PB Λ Rad`）+ 中心 ExitGuard `hwv` + 算术 + 时间域；**无** hstop / hstopE /
hstopX / hstayΩ、无 `DerivativeBoundBefore`、无 `qcan`。停止只是 `x` 自身 seed 距离的首出时刻，在
`seed_closure_firstExit_stopped_C11SC2` 内闭合。不 import CXJD 的 hstop 文件（`P6J10FirstExitHstopCXJD`、
`P6J10FirstExitTraceCXJD`），不 import FOOT3 `P6TerminalBCDLocalDerivP6F3`（hstayΩ）；审计做传递依赖名字扫描。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Worldline

/-- `BackwardTraceScalarControl_P6L` 私有引理 `lipschitzOnWith_inv_max_scalar_Icc_P6L` 的公开副本
（`_C11SC2`，证明逐字）：`[a, b]` 上导数只在 `q < R(·, x)` 处要 ⇒ `(max q R)⁻¹` Lipschitz。 -/
theorem lipschitzOnWith_inv_max_scalar_Icc_C11SC2 {P : OrientedThreeStage.{u}}
    {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn S) {a b q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hsub : Icc a b ⊆ D.carrier) (x : P.Carrier)
    (hbound : ∀ v ∈ Ioo a b, q < S.scalar v x →
      |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2) :
    LipschitzOnWith C (fun v => (max q (S.scalar v x))⁻¹) (Icc a b) := by
  apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    (r' := fun v => derivWithin (fun w => S.scalar w x) (Iic v) v) hq
  · intro v hv
    exact (hS.scalarTime hv hsub x).continuousWithinAt
  · intro v hv _
    have hd : DifferentiableAt ℝ (fun w => S.scalar w x) v :=
      (hS.scalarTime (K := Ioo a b) hv (Ioo_subset_Icc_self.trans hsub) x).differentiableAt
        (Ioo_mem_nhds hv.1 hv.2)
    rw [hd.derivWithin (uniqueDiffWithinAt_Iic v)]
    exact hd.hasDerivAt
  · exact hbound

/-- **worldline ceiling ODE（`_C11SC2`，PROVED）**：slab `j` 内 `[s, v]`、点 `y` 不动；导数只在
`M < R(r, y)`（`r ∈ (s, v)`）处要；`R(v, y) ≤ M`、`Ctime · M · (v − s) ≤ 1/2` ⇒ `[s, v]` 上 `R(·, y) ≤ 2M`。
（CXJT0 `le_two_mul_of_ceilingODE_CXJT0` 的 slab 左导数形；ceiling = 阈值 `M`。） -/
theorem ObservedHistory.scalar_le_two_mul_of_localDeriv_C11SC2 (H : ObservedHistory.{u})
    (j : Fin H.eventCount) {Ctime : ℝ≥0} {s v M : ℝ} (hM : 0 < M)
    (hs0 : H.time j.castSucc ≤ s) (hsv : s ≤ v) (hv2 : v < H.time j.succ)
    (y : (H.stage j.castSucc).Carrier)
    (hloc : ∀ r ∈ Ioo s v, M < (H.event j).incoming.flow.scalar r y →
      |derivWithin (fun w => (H.event j).incoming.flow.scalar w y) (Iic r) r| ≤
        Ctime * (H.event j).incoming.flow.scalar r y ^ 2)
    (hy : (H.event j).incoming.flow.scalar v y ≤ M)
    (hbud : (Ctime : ℝ) * M * (v - s) ≤ 1 / 2) :
    ∀ r ∈ Icc s v, (H.event j).incoming.flow.scalar r y ≤ 2 * M := by
  have hL := lipschitzOnWith_inv_max_scalar_Icc_C11SC2 (H.event j).incoming.equation hM
    (fun r hr => ⟨hs0.trans hr.1, hr.2.trans_lt hv2⟩) y hloc
  intro r hr
  have hd := hL.dist_le_mul r hr v ⟨hsv, le_rfl⟩
  have hrv : |r - v| = v - r := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith [hr.2])
  rw [Real.dist_eq, Real.dist_eq, hrv] at hd
  refine le_two_mul_of_abs_inv_max_sub_le_C11SC hM hy hd ?_
  have hCM : (0 : ℝ) ≤ Ctime * M := mul_nonneg Ctime.coe_nonneg hM.le
  calc (Ctime : ℝ) * M * (v - r) ≤ Ctime * M * (v - s) :=
        mul_le_mul_of_nonneg_left (by linarith [hr.1]) hCM
    _ ≤ 1 / 2 := hbud

end Worldline

namespace ObservedHistory

/-- 时间导数 `stageMetric m` → incoming（`m = i⁻`；`_C11SC2`，P6F3 私有同名引理的独立副本）。 -/
theorem deriv_of_stage_C11SC2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : i.castSucc = m) (v : ℝ) (Ctime : ℝ≥0)
    (x : (H.stage i.castSucc).Carrier) (z : (H.stage m).Carrier) (hz : HEq z x)
    (h : |derivWithin (fun t => metricScalarAt (H.stageMetric m t) z) (Iic v) v| ≤
      Ctime * metricScalarAt (H.stageMetric m v) z ^ 2) :
    |derivWithin (fun w => (H.event i).incoming.flow.scalar w x) (Iic v) v| ≤
      Ctime * (H.event i).incoming.flow.scalar v x ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hz
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

/-- **selection `hgood` ⇒ slab 内时间导数界（`_C11SC2`，阈值 `Cg·R`，PROVED）**：
`witness_of_hgood_slab_Cg_P6LS3` 的同一 slab 桥，取 `HasSpatialCanonicalTimeControl` 的**时间分量**：
slab `j` 内部时刻 `τ`（`aSeed ≤ τ ≤ σ`、`σ − L²/R ≤ τ`）、`d_τ(O_j, x) ≤ d_σ(O_σ, y) + L/√R`、
`Cg·R ≤ R(τ, x)` ⇒ `|∂ₜ⁻ R(·, x)|(τ) ≤ Ctime′ R(τ, x)²`（incoming flow 形）。 -/
theorem deriv_of_hgood_slab_Cg_C11SC2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) (R L : ℝ)
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
    (j : Fin H.eventCount) (τ : ℝ) (hτ1 : H.time j.castSucc < τ) (hτ2 : τ < H.time j.succ)
    (haτ : (aSeed : ℝ) ≤ τ) (hτσ : τ ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn)
    (x : (H.stage j.castSucc).Carrier)
    (hd : riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))
    (hR : Cg * R ≤ (H.event j).incoming.flow.scalar τ x) :
    |derivWithin (fun w => (H.event j).incoming.flow.scalar w x) (Iic τ) τ| ≤
      Ctime' * (H.event j).incoming.flow.scalar τ x ^ 2 := by
  have h0 : (0 : ℝ) ≤ τ := (H.time_nonneg _).trans hτ1.le
  let τI : Icc (0 : ℝ) H.horizon := ⟨τ, h0, hτσ.trans σ.2.2⟩
  have hact : H.activeStage τI = j.castSucc := H.activeStage_eq_of_slab_P6L3 j τI hτ1.le hτ2
  have hav : aSeed ≤ τI := haτ
  have hvs : τI ≤ σ := hτσ
  let xm : (H.stage (H.activeStage τI)).Carrier :=
    cast (congrArg (fun m => (H.stage m).Carrier) hact.symm) x
  have hxm : HEq xm x := cast_heq _ _
  have hs := point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
    (H.activeStage_mono (hvs.trans hsT)) h1 h2
  have hdm : riemannianEDistOf (H.stageMetric (H.activeStage τI) τI)
      (seedTrace.point (H.activeStage τI) (H.activeStage_mono hav)
        (H.activeStage_mono (hvs.trans hsT))) xm ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) :=
    (edist_stage_eq_P6L2 j hact τ _ xm _ x hs hxm).trans_le hd
  have hRm : Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage τI) τI) xm :=
    hR.trans_eq (scalar_stage_eq_P6L2 j hact τ xm x hxm).symm
  have hctl := (hgood τI hav hvs hLτ xm hdm hRm).2 (by rw [hact]; exact hτ1)
    (hτ2.trans_le (H.time_le_horizon_at _))
  exact deriv_of_stage_C11SC2 H j hact.symm τ Ctime' x xm hxm hctl

end ObservedHistory

section WindowScalLocal

/-- **U 端窗口标量界的局域导数版（`_C11SC2`，PROVED）**。结论 = `windowScal_of_pickedTop_C11SC` 逐字
（`B_s(x, 1/√(Cq))` 上 `R(s, ·) ≤ Cq`）。前提：hgood（区域 `L/√R`、阈值 `Cg·R`）、`Cg·R ≤ Λq`、
`Ctime′ Λ β ≤ 1/2`、`6Λ ≤ C`、`2Λ ≤ ρ² C`、`Lc + 2ρ/√(2Λ) ≤ L`（`ρ = localPropagationRadius C₂′`）、
`R ≤ q`、hpick 在 `x`（`R(v, x) ≤ Λq`）、时间域，与 **first-exit 停止**：`[s, v]` 上
`d_r(O, x) ≤ d_σ + Lc/√R`（`seed_closure_firstExit_stopped_C11SC2` 内部提供，不是 hstop）。
无 `DerivativeBoundBefore`、无 `qcan`、无 Hamilton–Ivey。 -/
theorem windowScal_of_pickedTop_local_C11SC2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
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
    {v q Λ β C : ℝ} (hv2 : v < H.time j.succ) (hq : 0 < q) (hRq : R ≤ q) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R ≤ Λ * q) (hbud : (Ctime' : ℝ) * Λ * β ≤ 1 / 2) (hΛC : 6 * Λ ≤ C)
    (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L) (hLc0 : 0 ≤ Lc)
    (hvσ : v ≤ σ) (x : (H.stage j.castSucc).Carrier)
    (hxv : (H.event j).incoming.flow.scalar v x ≤ Λ * q)
    (s : ℝ) (hs1 : v - β / q ≤ s) (hsv : s ≤ v) (hs0 : H.time j.castSucc < s)
    (haS : (aSeed : ℝ) ≤ s) (hσL : (σ : ℝ) - L ^ 2 / R ≤ s)
    (hGx : ∀ r ∈ Icc s v,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric r)
          (seedTrace.point j.castSucc h1 h2) x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R))
    (z : (H.stage j.castSucc).Carrier)
    (hz : riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z <
      ENNReal.ofReal (1 / Real.sqrt (C * q))) :
    (H.event j).incoming.flow.scalar s z ≤ C * q := by
  set dσ := riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
    (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y
    with hdσ
  set ρ := localPropagationRadius C2' with hρdef
  have hρ0 : 0 < ρ := localPropagationRadius_pos hC2
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hΛq : 0 < Λ * q := mul_pos hΛ hq
  have hQ0 : 0 < 2 * (Λ * q) := by linarith
  have hs2Λ : 0 < Real.sqrt (2 * Λ) := Real.sqrt_pos.2 (by linarith)
  -- 半径：`2ρ/√(2Λq) ≤ 2ρ/(√(2Λ)√R)`
  have hsplit : Real.sqrt (2 * (Λ * q)) = Real.sqrt (2 * Λ) * Real.sqrt q := by
    rw [← mul_assoc, Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * Λ)]
  have hradR : 2 * (ρ / Real.sqrt (2 * (Λ * q))) ≤
      2 * (ρ / Real.sqrt (2 * Λ)) / Real.sqrt R := by
    rw [hsplit]
    have h := div_le_div_of_nonneg_left hρ0.le (mul_pos hs2Λ hsR)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRq) hs2Λ.le)
    have he : 2 * (ρ / (Real.sqrt (2 * Λ) * Real.sqrt R)) =
        2 * (ρ / Real.sqrt (2 * Λ)) / Real.sqrt R := by
      field_simp
    linarith
  have hLcL' : Lc / Real.sqrt R + 2 * (ρ / Real.sqrt (2 * (Λ * q))) ≤ L / Real.sqrt R := by
    have h := div_le_div_of_nonneg_right hρL hsR.le
    rw [add_div] at h
    linarith
  have hLcL : Lc / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 ≤ 2 * (ρ / Real.sqrt (2 * (Λ * q))) := by positivity
    linarith
  -- (1) worldline ceiling：`[s, v]` 上 `R(·, x) ≤ 2Λq`
  have hqvs : q * (v - s) ≤ β := by
    have hvs : v - s ≤ β / q := by linarith
    have h := mul_le_mul_of_nonneg_left hvs hq.le
    rwa [mul_div_cancel₀ _ hq.ne'] at h
  have hwl : ∀ r ∈ Icc s v, (H.event j).incoming.flow.scalar r x ≤ 2 * (Λ * q) :=
    H.scalar_le_two_mul_of_localDeriv_C11SC2 j hΛq hs0.le hsv hv2 x (fun r hr hMr =>
      ObservedHistory.deriv_of_hgood_slab_Cg_C11SC2 H haT hsT has seedTrace y R L hgood j r
        (hs0.trans hr.1) (hr.2.trans hv2) (haS.trans hr.1.le) (hr.2.le.trans hvσ)
        (hσL.trans hr.1.le) h1 h2 x
        ((hGx r ⟨hr.1.le, hr.2.le⟩).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL)))
        (hCgΛ.trans hMr.le)) hxv (by
      calc (Ctime' : ℝ) * (Λ * q) * (v - s) = Ctime' * Λ * (q * (v - s)) := by ring
        _ ≤ Ctime' * Λ * β := mul_le_mul_of_nonneg_left hqvs (by positivity)
        _ ≤ 1 / 2 := hbud)
  have hxs : (H.event j).incoming.flow.scalar s x ≤ 2 * (Λ * q) := hwl s ⟨le_rfl, hsv⟩
  -- (2) 时刻 `s` 的局部传播（hgood 空间分量）
  let U : Set (H.stage j.castSucc).Carrier := {w | riemannianEDistOf
    ((H.event j).incoming.flow.base.metric s) (seedTrace.point j.castSucc h1 h2) w ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R)}
  have hU : riemannianBallOf ((H.event j).incoming.flow.base.metric s) x
      (2 * (ρ / Real.sqrt (2 * (Λ * q)))) ⊆ U := by
    intro w hwb
    change riemannianEDistOf _ _ w ≤ _
    calc _ ≤ riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
          (seedTrace.point j.castSucc h1 h2) x +
          riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x w :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (dσ + ENNReal.ofReal (Lc / Real.sqrt R)) +
          ENNReal.ofReal (2 * (ρ / Real.sqrt (2 * (Λ * q)))) :=
          add_le_add (hGx s ⟨le_rfl, hsv⟩) hwb.le
      _ = dσ + ENNReal.ofReal (Lc / Real.sqrt R + 2 * (ρ / Real.sqrt (2 * (Λ * q)))) := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL')
  have hball : ∀ w : (H.stage j.castSucc).Carrier, w ∈ riemannianClosedBallOf
      ((H.event j).incoming.flow.base.metric s) x (ρ / Real.sqrt (2 * (Λ * q))) →
      (H.event j).incoming.flow.scalar s w ≤ 3 * (2 * (Λ * q)):= fun w0 hw0 =>
    scalar_le_on_ball_of_gradient_bound_P6L (H.event j).incoming.flow hC2 hQ0 U hU
    (fun w hwU hw ξ => by
      have hRw : Cg * R ≤ (H.event j).incoming.flow.scalar s w := by linarith
      have hg := ObservedHistory.gradient_of_hgood_slab_Cg_P6LS3 (Ctime' := Ctime') hC2 H haT hsT
        has seedTrace y R L hgood j s hs0 (hsv.trans_lt hv2) haS (hsv.trans hvσ) hσL h1 h2 w hwU
        hRw ξ
      rw [Real.coe_toNNReal _ hC2] at hg
      have hpos : 0 ≤ (H.event j).incoming.flow.scalar s w := by linarith
      have hterm : 0 ≤ C2' * (H.event j).incoming.flow.scalar s w *
          Real.sqrt ((H.event j).incoming.flow.scalar s w) *
          Real.sqrt (((H.event j).incoming.flow.base.metric s).inner w ξ ξ) := by positivity
      have hring : 2 * C2' * ((H.event j).incoming.flow.scalar s w *
          Real.sqrt ((H.event j).incoming.flow.scalar s w)) *
          Real.sqrt (((H.event j).incoming.flow.base.metric s).inner w ξ ξ) =
          2 * (C2' * (H.event j).incoming.flow.scalar s w *
          Real.sqrt ((H.event j).incoming.flow.scalar s w) *
          Real.sqrt (((H.event j).incoming.flow.base.metric s).inner w ξ ξ)) := by ring
      rw [hring]
      linarith) hxs hw0
  -- (3) `1/√(Cq) ≤ ρ/√(2Λq)` 且 `6Λq ≤ Cq`
  have hC0 : 0 < C := by linarith
  have hCq : 0 < C * q := mul_pos hC0 hq
  have hℓ : 1 / Real.sqrt (C * q) ≤ ρ / Real.sqrt (2 * (Λ * q)) := by
    have hkey : Real.sqrt (2 * (Λ * q)) ≤ Real.sqrt (C * q) * ρ := by
      have hle : 2 * (Λ * q) ≤ ρ ^ 2 * (C * q) := by
        have h := mul_le_mul_of_nonneg_right hρC hq.le
        calc 2 * (Λ * q) = 2 * Λ * q := by ring
          _ ≤ ρ ^ 2 * C * q := h
          _ = ρ ^ 2 * (C * q) := by ring
      have h1' : Real.sqrt (2 * (Λ * q)) ≤ Real.sqrt (ρ ^ 2 * (C * q)) := Real.sqrt_le_sqrt hle
      rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ0.le] at h1'
      linarith
    have h2' : Real.sqrt (2 * (Λ * q)) / ρ ≤ Real.sqrt (C * q) := (div_le_iff₀ hρ0).2 hkey
    have h3 := one_div_le_one_div_of_le (div_pos (Real.sqrt_pos.2 hQ0) hρ0) h2'
    rwa [one_div_div] at h3
  have hzb := hball z (hz.le.trans (ENNReal.ofReal_le_ofReal hℓ))
  have h6 := mul_le_mul_of_nonneg_right hΛC hq.le
  linarith

end WindowScalLocal

section StoppedFirstExit

/-- **stopped first-exit 距离引理（单 slab，`_C11SC2`，PROVED）**：`firstExit_distance_P6M4` 的 stopped
形——`hRic` 只在 `[s, t]` 上 `d(p, q) < X` 已成立时要（P6M4 是逐点 `d_s < X`）。核 =
`firstExit_window_CXJD`；链 = `edist_le_add_of_slab_ricci_P6M4`（I.8.3(b)）；左延拓 =
`edist_lt_near_left_P6L4`。 -/
theorem ObservedHistory.firstExit_distance_stopped_C11SC2 (H : ObservedHistory.{u})
    (e : Fin H.eventCount) {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t)
    (ha : H.time e.castSucc < a) (ht : t < H.time e.succ) (p q : (H.stage e.castSucc).Carrier)
    {X : ℝ≥0∞}
    (hmargin : riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
      ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hRic : ∀ s ∈ Ioo a t,
      (∀ s' ∈ Icc s t,
        riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X) →
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event e).incoming.flow.base.metric s) q z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event e).incoming.flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event e).incoming.flow.base.metric s).inner z ξ ξ) :
    ∀ s ∈ Icc a t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
      riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) :=
  firstExit_window_CXJD
    (f := fun s => riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q)
    hat (div_pos (by norm_num) hℓ).le hmargin
    (fun s hs hG => H.edist_le_add_of_slab_ricci_P6M4 e hℓ hs.2 (ha.trans_le hs.1) ht p q
      (fun r hr z ξ hz => hRic r ⟨hs.1.trans_lt hr.1, hr.2⟩
        (fun s' hs' => hG s' ⟨hr.1.trans_le hs'.1, hs'.2⟩) z ξ hz))
    (fun s hs hG => by
      obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.event e).incoming.flow
        (H.event e).incoming.equation hs.1
        (fun r hr => ⟨ha.trans_le hr.1, lt_of_le_of_lt (hr.2.trans hs.2) ht⟩) p q
        (hG s ⟨le_rfl, hs.2⟩)
      exact ⟨s₁, ⟨has₁, hs₁⟩, hnear⟩)

/-- **单 history seed closure 的 stopped 版（首出时刻，`_C11SC2`，PROVED）**：`seed_closure_firstExit_P6L4`
逐字，唯一改动 = U 端标量界 `hscal` 只在 **`[s, v]` 上已 seed-Good**（`d_{s′}(O, x) < d_σ + L/√R`，
`s′ ∈ [s, v]`）的时刻 `s` 要（P6L4 是逐点 `d_s(O, x) ≤ …`）；首出时刻改用
`firstExit_distance_stopped_C11SC2`。证明体逐字。 -/
theorem ObservedHistory.seed_closure_firstExit_stopped_C11SC2 (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (w x : (H.stage j.castSucc).Carrier)
    {dσ : ℝ≥0∞} {A R Q L C Rad B τ v : ℝ} (hdσ : dσ = ENNReal.ofReal A) (hA : 0 ≤ A)
    (hR : 0 < R) (hRQ : R ≤ Q) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max B 0 ≤ L)
    (hwv : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hxw : x ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt Q))
    (hτB : v - B / Q ≤ τ) (hτv : τ ≤ v) (hτ1 : H.time j.castSucc < τ)
    (hv2 : v < H.time j.succ) (haτ : (aSeed : ℝ) ≤ τ) (hvT : v ≤ Tn) (hQτ : 1 ≤ Q * τ)
    (hscal : ∀ s : ℝ, v - B / Q ≤ s → s ≤ v → H.time j.castSucc < s →
      (∀ s' ∈ Icc s v, riemannianEDistOf ((H.event j).incoming.flow.base.metric s')
          (seedTrace.point j.castSucc h1 h2) x < dσ + ENNReal.ofReal (L / Real.sqrt R)) →
      ∀ z : (H.stage j.castSucc).Carrier,
        riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z <
          ENNReal.ofReal (1 / Real.sqrt (C * Q)) →
        (H.event j).incoming.flow.scalar s z ≤ C * Q) :
    riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  set K := max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hQ : 0 < Q := hR.trans_le hRQ
  have hC : 0 ≤ C := by linarith
  have h3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCK : C ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have hm : C ≤ max C (2 * Real.exp 4) := le_max_left _ _
    nlinarith
  have hr : 0 < r := hsmall.1
  have hQr : 2500 * K ≤ Q * r ^ 2 := hRr.trans (mul_le_mul_of_nonneg_right hRQ (sq_nonneg r))
  obtain ⟨hℓr, hKr, hKℓ, -⟩ := seq_scale_bounds_C11G hK1 hQ hr hQr
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hℓ : 0 < 1 / Real.sqrt K / Real.sqrt Q := by positivity
  have hℓCQ : 1 / Real.sqrt K / Real.sqrt Q ≤ 1 / Real.sqrt (C * Q) := by
    have hCQ : Real.sqrt (C * Q) ≤ Real.sqrt K * Real.sqrt Q := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCK hQ.le)
    rw [div_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hCQ
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K * Q :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le
  have hRad0 : 0 ≤ max Rad 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 16 * Real.sqrt K * max B 0 := by positivity
    linarith
  -- 漂移与初始余量
  have hdrift := drift_le_P6L4 (by linarith : (0 : ℝ) < K) hR hRQ hτB
  have hdr0 : 0 ≤ 8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ) :=
    mul_nonneg (by positivity) (by linarith)
  have hrad' : Rad / Real.sqrt Q ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le).trans
      (div_le_div_of_nonneg_left hRad0 hsR (Real.sqrt_le_sqrt hRQ))
  have hwx : riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x <
      ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    lt_of_lt_of_le hxw (ENNReal.ofReal_le_ofReal hrad')
  have hwv' : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤ ENNReal.ofReal (A + L / 2 / Real.sqrt R) := by
    rw [ENNReal.ofReal_add hA (by positivity), ← hdσ]
    exact hwv
  have hd2 : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) w +
      riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x <
      ENNReal.ofReal (A + L / 2 / Real.sqrt R) + ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwv') hwv' hwx
  have hd3 : ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
        ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
        ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hdr0, hdσ, ← ENNReal.ofReal_add hA (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R +
        8 * Real.sqrt K * max B 0 / Real.sqrt R =
        (L / 2 + max Rad 0 + 8 * Real.sqrt K * max B 0) / Real.sqrt R := by ring
    have hle : (L / 2 + max Rad 0 + 8 * Real.sqrt K * max B 0) / Real.sqrt R ≤
        L / Real.sqrt R := div_le_div_of_nonneg_right (by linarith) hsR.le
    linarith
  have hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x +
      ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) <
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    calc riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
          (seedTrace.point j.castSucc h1 h2) x +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) ≤
        (riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
            (seedTrace.point j.castSucc h1 h2) w +
          riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl
      _ < ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
            ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hd2
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := hd3
  -- 首出时刻（stopped）
  have hfe := H.firstExit_distance_stopped_C11SC2 j hℓ hτv hτ1 hv2
    (seedTrace.point j.castSucc h1 h2) x hmargin
    (fun s hs hG => H.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin j
      h1 h2 x hQ hℓ hKℓ hℓr hKr hC hKC (hτ1.trans hs.1) (hs.2.trans hv2)
      (haτ.trans hs.1.le) (hs.2.le.trans hvT)
      (hQτ.trans (mul_le_mul_of_nonneg_left hs.1.le hQ.le))
      (fun z hz => hscal s (hτB.trans hs.1.le) hs.2.le (hτ1.trans hs.1) hG z
        (hz.trans_le (ENNReal.ofReal_le_ofReal hℓCQ)))) τ ⟨le_rfl, hτv⟩
  exact (lt_of_le_of_lt hfe hmargin).le

end StoppedFirstExit

section SeedClosureLocal

/-- hpick 半径单调（`_C11SC2`）：`Rad ≤ A` ⇒ `PickedBallTop_C11PB Λ A ⇒ PickedBallTop_C11PB Λ Rad`。 -/
theorem PickedBallTop_C11PB.mono_C11SC2 {Λ A Rad : ℝ} {K : RetainedCoreHistory.{u}}
    {j : Fin K.eventCount} {v : ℝ} {w : (K.stage j.castSucc).Carrier} (hRA : Rad ≤ A)
    (h : PickedBallTop_C11PB Λ A K j v w) : PickedBallTop_C11PB Λ Rad K j v w := fun x hx =>
  h x (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right hRA (Real.sqrt_nonneg _))))

/-- **G1a：picked-ball 窗口 seed closure（无阈值 hseedAll），局域导数版（`_C11SC2`，PROVISIONAL：binder =
hpick）**。结论 = `pickedBallWindowSeedAll_of_firstExit_C11SC` 逐字（`O = seedTrace.point j⁻`、
`D = d_σ(O_σ, y) + L/√R`）。相对旧版：删去 `hder`（slab 全域 `DerivativeBoundBefore`）、`hqcan`、`hrad`
（`e^{9 Kr β}` 加厚）；新增 hgood（区域 `L/√R`、阈值 `Cg·R`）+ `Cg·R ≤ Λq` + `6Λ ≤ C` + `2Λ ≤ ρ² C` +
`Lc + 2ρ/√(2Λ) ≤ L`（closure 预算 `Lc`）+ 时间域 `v ≤ σ`、`σ − L²/R ≤ v − β/q`；hpick 半径 `Rad`
（大半径 `A` 用 `PickedBallTop_C11PB.mono_C11SC2`）；`hwv` 预算 `Lc/2`。 -/
theorem pickedBallWindowSeedAll_of_firstExit_local_C11SC2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg : ℝ} (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
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
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn)
    (v : ℝ) (hv2 : v < K.time j.succ) (w : (K.stage j.castSucc).Carrier) {β Rad Λ C : ℝ}
    (hRq : R ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R ≤ Λ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime' : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C) (hΛC : 6 * Λ ≤ C)
    (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤
        Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hav : (aSeed : ℝ) ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hvσ : v ≤ σ)
    (hσL : (σ : ℝ) - L ^ 2 / R ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hlate : 1 ≤ R * (v - β / (K.toHistory.event j).incoming.flow.scalar v w))
    (hwv : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (Lc / 2 / Real.sqrt R))
    (htop : PickedBallTop_C11PB Λ Rad K j v w) :
    PickedBallWindowSeedAll_C11PB β Rad K j v w (seedTrace.point j.castSucc h1 h2)
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R)) := by
  intro x hx τ hwin hτv hτ1
  have hq : 0 < (K.toHistory.event j).incoming.flow.scalar v w := hR.trans_le hRq
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hLc0 : 0 ≤ Lc := by
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        max β 0 := mul_nonneg (by positivity) (le_max_right _ _)
    have h0' : 0 ≤ max Rad 0 := le_max_right _ _
    linarith
  have hLcL : Lc / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) := by
      have := localPropagationRadius_pos hC2
      positivity
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
    (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
      (K.toHistory.activeStage_mono hsT)) y with hdσdef
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
  have hcl := K.toHistory.seed_closure_firstExit_stopped_C11SC2 haT hsmall hclock seedTrace ha₀
    hpin j h1 h2 w x hdσ ENNReal.toReal_nonneg hR hRq hC1 hRr hL hwv hx hwin hτv hτ1 hv2
    (hav.trans hwin) (hvσ.trans hsT) (hlate' τ hwin)
    (fun s hs1 hsv hs0 hG z hz => windowScal_of_pickedTop_local_C11SC2 hC2 K.toHistory haT hsT
      has seedTrace y hR hgood j h1 h2 hv2 hq hRq hΛ hCgΛ hbud hΛC hρC hρL hLc0 hvσ x
      (htop x hx) s hs1 hsv hs0 (hav.trans hs1) (hσL.trans hs1) (fun r hr => (hG r hr).le) z hz)
  exact hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL))

/-- **G1：picked-ball 窗口 seed closure hseed，局域导数版（`_C11SC2`，PROVISIONAL：binder = hpick）**：
G1a 的同一组输入 ⇒ PICKBALL G4 `PickedBallWindowSeed_C11PB` 逐字（阈值 `qthr` 任意，`.toWindowSeed`）。 -/
theorem pickedBallWindowSeed_of_firstExit_local_C11SC2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg : ℝ} (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
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
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn)
    (v : ℝ) (hv2 : v < K.time j.succ) (w : (K.stage j.castSucc).Carrier) {β Rad qthr Λ C : ℝ}
    (hRq : R ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R ≤ Λ * (K.toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctime' : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C) (hΛC : 6 * Λ ≤ C)
    (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤
        Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hav : (aSeed : ℝ) ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hvσ : v ≤ σ)
    (hσL : (σ : ℝ) - L ^ 2 / R ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (hlate : 1 ≤ R * (v - β / (K.toHistory.event j).incoming.flow.scalar v w))
    (hwv : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (Lc / 2 / Real.sqrt R))
    (htop : PickedBallTop_C11PB Λ Rad K j v w) :
    PickedBallWindowSeed_C11PB β Rad qthr K j v w (seedTrace.point j.castSucc h1 h2)
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R)) :=
  (pickedBallWindowSeedAll_of_firstExit_local_C11SC2 hC2 K haT hsT has hsmall hclock seedTrace
    ha₀ hpin y hR hgood j h1 h2 v hv2 w hRq hΛ hCgΛ hbud hC1 hΛC hρC hRr hL hρL hav hvσ hσL
    hlate hwv htop).toWindowSeed

end SeedClosureLocal

section ConsumerG2

/-- **G2 consumer（`_C11SC2`）：picked-ball hgrad ⇐ hgood + G1（局域导数版）**。PICKBALL G4
`pickedBallGrad_of_hgood_C11PB` 的 binder `hseed`（`D = d_σ(O_σ, y) + L/√R_n`，阈值 `Cg R_n`）由
`pickedBallWindowSeed_of_firstExit_local_C11SC2` 在选点处供给；**同一** `HgoodCg_C11SH`（index `n`）同时付 G1 的
时间导数 / 空间梯度与 G4 的 witness。无 `DerivativeBoundBefore`、无 `qcan`。 -/
theorem pickedBallGrad_of_firstExit_local_C11SC2 {Cg β : ℝ} {Cgrad : ℝ≥0}
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
    (hC20 : 0 ≤ C2) (hC2 : C2 ≤ (Cgrad : ℝ)) (n : ℕ) {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage t) t)
        (a₀ + t) x)
    (j : Fin (K n).eventCount) (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (v : ℝ) (hv2 : v < (K n).time j.succ) (w : ((K n).stage j.castSucc).Carrier)
    {Lc Rad Λ C : ℝ} (hR : 0 < R n)
    (hRq : R n ≤ ((K n).toHistory.event j).incoming.flow.scalar v w) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R n ≤ Λ * ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hbud : (Ctg : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C) (hΛC : 6 * Λ ≤ C)
    (hρC : 2 * Λ ≤ localPropagationRadius C2 ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤
        Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) ≤ L n)
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
          ENNReal.ofReal (Lc / 2 / Real.sqrt (R n)))
    (htop : PickedBallTop_C11PB Λ Rad (K n) j v w) :
    PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) j v w :=
  pickedBallGrad_of_hgood_C11PB K hgood hC2 n j v hv2 h1 h2 w hav hvs hvL
    (pickedBallWindowSeed_of_firstExit_local_C11SC2 hC20 (K n) (haT n) (hsT n) (has n) hsmall
      hclock (seedTrace n) ha₀ hpin (y n) hR (hgood n) j h1 h2 v hv2 w hRq hΛ hCgΛ hbud hC1 hΛC
      hρC hRr hL hρL hav hvs hvL hlate hwv htop)

end ConsumerG2

section RelationPICKT1

/-!
### G3：与 PICKT1 `PickedCenterWindowSeed_C11PT` 的关系（只写 example，不开新分析）

`PickedCenterWindowSeed_C11PT`（`P6PickedCenterProducerC11PT.lean:103`）= 中心尺度 `R_n`、共同窗口
`[v − θ/R_n, v]`、区域球 `B_v(tr x₁, Dc/√R_n)` 的窗口 seed closure。本文件的两条核引理
（`seed_closure_firstExit_stopped_C11SC2`、`windowScal_of_pickedTop_local_C11SC2`）对尺度 `Q`/`q` **泛型**，
取 `Q := R_n`、球心 `wc := tr.point j′⁻`、`Rad := Dc`、`B := θ` 即得下面的 example：
**单 slice 步**——slice 时刻 `v` 上区域球内 `R(v, ·) ≤ Λ R_n`（逐点，不要加厚、不要全域导数）+ hgood +
K0 + HI + 中心 ExitGuard（PICKT1 §1 的 `hdistQC` L/4 余量 + 三角不等式）+ `Ctime′ Λ θ ≤ 1/2`
⇒ 该 slice 的窗口 closure（`PickedCenterWindowSeed_C11PT` 在固定 `(j′, v, x₁, tr)` 处的体，且对窗口内
全部 `v′`、无曲率阈值）。
**结论（回答 D-9 / R-C11-18 待选路线）**：G1 在 driver 中心尺度给出的是路线 (i)（时间方向 bootstrap）的
**归纳步**，不是 base case：slice 时刻界 `R(v, ·) ≤ Λ R_n`（"hpick @ 中心尺度"）**不由** 12.1 Step 1 供给
（Step 1 只给"无更坏坏点"，不给曲率极大性；PICKT1 §3），在 `v = σ` 处它恰是 T1 非 CWP 分支在中心尺度的
结论。故路线 (i) 仍缺 base case（最早 slice / first-failure 连续性论证），SEEDCL2 只把归纳步的输入从
"Ω 上全域导数 + 加厚球顶"降成"区域球上逐点 slice 界"。路线 (ii)（变尺度窗口）不经过此 example。
-/

example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ} (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
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
    (j : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn)
    (v : ℝ) (hv2 : v < K.time j.succ) (wc : (K.stage j.castSucc).Carrier) {θ Dc Λ C : ℝ}
    (hΛ : 0 < Λ) (hCgΛ : Cg * Rn ≤ Λ * Rn) (hbud : (Ctime' : ℝ) * Λ * θ ≤ 1 / 2)
    (hC1 : 1 ≤ C) (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ Rn * r ^ 2)
    (hL : 2 * max Dc 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max θ 0 ≤
        Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hav : (aSeed : ℝ) ≤ v - θ / Rn) (hvσ : v ≤ σ) (hσL : (σ : ℝ) - L ^ 2 / Rn ≤ v - θ / Rn)
    (hlate : 1 ≤ Rn * (v - θ / Rn))
    (hwv : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) wc ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (Lc / 2 / Real.sqrt Rn))
    (hslice : ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) wc
      (Dc / Real.sqrt Rn), (K.toHistory.event j).incoming.flow.scalar v x ≤ Λ * Rn)
    (x : (K.stage j.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) wc
      (Dc / Real.sqrt Rn))
    (v' : ℝ) (hwin : v - θ / Rn ≤ v') (hv'v : v' ≤ v) (hv'1 : K.time j.castSucc < v') :
    riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v')
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt Rn) := by
  have hsR : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hR
  have hLc0 : 0 ≤ Lc := by
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        max θ 0 := mul_nonneg (by positivity) (le_max_right _ _)
    have h0' : 0 ≤ max Dc 0 := le_max_right _ _
    linarith
  have hLcL : Lc / Real.sqrt Rn ≤ L / Real.sqrt Rn := by
    have : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) := by
      have := localPropagationRadius_pos hC2
      positivity
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
    (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
      (K.toHistory.activeStage_mono hsT)) y with hdσdef
  rcases eq_or_ne dσ ⊤ with hT | hT
  · rw [hT, top_add]
    exact le_top
  have hdσ : dσ = ENNReal.ofReal dσ.toReal := (ENNReal.ofReal_toReal hT).symm
  have hlate' : ∀ s : ℝ, v - θ / Rn ≤ s → 1 ≤ Rn * s := fun s hs =>
    hlate.trans (mul_le_mul_of_nonneg_left hs hR.le)
  have hcl := K.toHistory.seed_closure_firstExit_stopped_C11SC2 haT hsmall hclock seedTrace ha₀
    hpin j h1 h2 wc x hdσ ENNReal.toReal_nonneg hR le_rfl hC1 hRr hL hwv hx hwin hv'v hv'1 hv2
    (hav.trans hwin) (hvσ.trans hsT) (hlate' v' hwin)
    (fun s hs1 hsv hs0 hG z hz => windowScal_of_pickedTop_local_C11SC2 hC2 K.toHistory haT hsT
      has seedTrace y hR hgood j h1 h2 hv2 hR le_rfl hΛ hCgΛ hbud hΛC hρC hρL hLc0 hvσ x
      (hslice x hx) s hs1 hsv hs0 (hav.trans hs1) (hσL.trans hs1) (fun r hr => (hG r hr).le) z hz)
  exact hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL))

end RelationPICKT1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

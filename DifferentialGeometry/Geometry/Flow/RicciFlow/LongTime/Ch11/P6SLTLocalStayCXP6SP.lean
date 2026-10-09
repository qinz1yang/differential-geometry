import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabCeilingCXJD

/-!
# c⋆ 版 `hstayLoc` ⇐ CXJD 跨 slab first-exit（逐点 `Cball`）（O-CH11-SLTPROD G3，后缀 `_P6SP`）

G1 的 binder `hstayLoc`（前 slab 坏点尺度 trace stay，距离形）在**固定 `c⋆ := 1/(2·max(Ctime′, 1))`** 档的来源：
树内 `ObservedHistory.hstop_of_firstExit_CXJD`（`P6J10CrossSlabCeilingCXJD:27`）已是**跨 slab** trace stay
（`∀ v ∈ [a, σ]`，`d_v(seed(v), A(v)) ≤ d_σ(O, y) + L/√R`；surgery crossing 由 `hprotC` 保护前提处理，
`hprotC_of_ceiling_CXJD` 可从 ceiling + scale 分离产出）。它要 `R_σ(z) ≤ Cball·R` 与深度
`σ − a ≤ T/R`、`2·Ctime′·Qb·T ≤ 1`、`Qb ≥ max(Cball, Cg, 1)`。
* **逐点 `Cball := R_σ(z)/R`**：`hz` 平凡（等号）；`Qb := max(R_σ(z)/R, Cg, 1)` ⇒ `Qb·R = max(Cg·R, R_σ(z))`
  （`Cg ≥ 1`），`T := c⋆/Qb` ⇒ `2·Ctime′·Qb·T = Ctime′/max(Ctime′, 1) ≤ 1`，深度条件
  `σ − a ≤ T/R ⇔ (σ − a)·max(Cg·R, R_σ(z)) ≤ c⋆` = `hslabsLoc` 的固定 `c⋆` guard。
* **循环在哪里断**（R-C11-19）：旧链 anchor `hslabsSel` ⇐ `hderivL_of_hgood_firstExit_P6JW` ⇐ `hstopE` ⇐
  CXJD (c) **端点球控制**（`∀ z ∈ B(y, D/√R)`，`R(z) ≤ Cball·R`，`Cball` 是**与 z 无关的常数**）= anchor 自身结论 ⇒ 循环。
  本文件对**每个 z 单独**取 `Cball := R_σ(z)/R`（依赖 z，可以 ≫ 1），`hz` 不再是球界而是恒等式；代价全部进深度
  `c⋆/max(Cg·R, R_σ(z))`——正是局部合同允许的坏点尺度深度。故不经 anchor 球界，循环不出现。
* **∀ `c` 版仍不可得**：`hstep` 把深度锁在一次 ODE 的 `T ≤ 1/(2·Ctime′·Qb)`（即 `c ≤ c⋆`）；任意 `c` 需多步
  ceiling 拼接（每步 `R ≤ 2^k·M`、深度递减），不在本文件。
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

/-- **逐点实例（`_P6SP`，PROVED ⇐ CXJD 结构输入）**：`hstop_of_firstExit_CXJD` 取 `Cball := R_σ(z)/R`、
`Qb := max(R_σ(z)/R, Cg, 1)`、`T := c⋆/Qb`（`c⋆ = 1/(2·max(Ctime′, 1))`）；`hz` / `hQb` / `hstep` /
`hdepth` 全部由 c⋆ guard `(σ − a)·max(Cg·R, R_σ(z)) ≤ c⋆` 与 `1 ≤ Cg` 给出。结论 = CXJD 逐字（整窗
`[a, σ]` 跨 slab trace stay）。剩余输入 = CXJD 结构输入（K0 seed、HI、hgood、records / hOld / hcan /
hacc / hDm、`hprotC`、`hRa`、`hdσ`）+ 数值（`ℓ`、`K`、`hKC`、`hℓρ`、`hρL`、`hnum`，以 `Qb`、`T` 表述）。 -/
theorem ObservedHistory.stay_cstar_of_firstExit_P6SP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσlast : H.activeStage σ < Fin.last H.eventCount)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hRa : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (hQbdef : Qb = max (max (metricScalarAt (H.stageMetric (H.activeStage σ) σ) z / R) Cg) 1)
    (hTdef : T = 1 / (2 * max (Ctime' : ℝ) 1) / Qb)
    (hguard : ((σ : ℝ) - a) *
        max (Cg * R) (metricScalarAt (H.stageMetric (H.activeStage σ) σ) z) ≤
      1 / (2 * max (Ctime' : ℝ) 1))
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hOld : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage σ) (he : T₀ ≤ H.time e.succ),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), H.time e.succ ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hzy : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (hdσ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
            (H.activeStage_mono ((hvt.trans le_rfl).trans hσT)))
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / Real.sqrt R) := by
  generalize hRz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z = Rz at hQbdef hguard
  have hCgR : R ≤ Cg * R := by nlinarith
  have hQbM : Qb * R ≤ max (Cg * R) Rz := by
    have hle : Qb ≤ max (Cg * R) Rz / R := by
      rw [hQbdef]
      refine max_le (max_le ?_ ?_) ?_
      · exact div_le_div_of_nonneg_right (le_max_right _ _) hR.le
      · rw [le_div_iff₀ hR]
        exact le_max_left _ _
      · rw [le_div_iff₀ hR, one_mul]
        exact hCgR.trans (le_max_left _ _)
    calc Qb * R ≤ max (Cg * R) Rz / R * R := mul_le_mul_of_nonneg_right hle hR.le
      _ = max (Cg * R) Rz := div_mul_cancel₀ _ hR.ne'
  have hQb1 : (1 : ℝ) ≤ Qb := by
    rw [hQbdef]
    exact le_max_right _ _
  have hQbpos : 0 < Qb := by linarith
  have hm1 : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hdepth : (σ : ℝ) - a ≤ T / R := by
    rw [hTdef, div_div, le_div_iff₀ (mul_pos hQbpos hR)]
    have hsa : 0 ≤ (σ : ℝ) - a := sub_nonneg.mpr (show (a : ℝ) ≤ σ from haσ)
    exact (mul_le_mul_of_nonneg_left hQbM hsa).trans hguard
  have hstep : 2 * (Ctime' : ℝ) * Qb * T ≤ 1 := by
    have hT : 2 * (Ctime' : ℝ) * Qb * T = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [hT, div_le_one hm1]
    exact le_max_left _ _
  have hQb : max (max (Rz / R) Cg) 1 ≤ Qb := le_of_eq hQbdef.symm
  have hz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Rz / R * R := by
    rw [div_mul_cancel₀ _ hR.ne', hRz]
  exact hstop_of_firstExit_CXJD hC2 H haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb
    hstep haS haσ hσlast haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hacc
    hDm hprotC hzy hdσ hnum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

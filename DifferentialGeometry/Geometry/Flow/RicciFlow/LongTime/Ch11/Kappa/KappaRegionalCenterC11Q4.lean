import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalC11Q3

/-!
# 区域 κ 的中心绑定（O-CH11-KAPPA3 G5，后缀 `_C11Q4`；R-C11-5 D-8 / D-10）

KAPPA2 的 `regionalKappa_of_window_C11Q3`（合同形 `RegionalKappa_C11Q3` 被 R-C11-5 接受）把区域 `U` 的
距离约束直接写成 "`U` 的点离种子 trace 点 `< A r`"。R-C11-5 D-8 要求**中心绑定显式**：
* 种子中心 `O_τ = seedTrace.point (activeStage τ)`（原始种子 `(t₀, p, r)` 的 trace）**≠** 坏点 trace 中心
  `c`（P6 切片二分里 `U_v = B_v(c_v, Rad/√R)` 的中心）；
* `U` 先放进 `B_τ(c, ρU)`（`hUc`；`τ = v` 时就是 `U` 的定义，其余 `τ` 是窗口内的度量畸变估计），再经
  **`hdistV`**（`d_τ(O_τ, c) + ρU ≤ A r`）放进 `B_τ(O_τ, A r)`（三角不等式，`edist_lt_of_center_C11Q4` /
  `ball_subset_of_center_C11Q4`），然后用 window κ（它本来量化 `B_τ(O_τ, A r)` 内任意中心）；
* 跨 stage 用 `U` 带识别：`U ⊆ (K.stage j.castSucc).Carrier`，切片点 `zz`、`cc` 经 `HEq` 认同
  （开 slab 内 `stageAt τ` 的 carrier 由 `type_eq_of_heq` 给出）；
* 尺度：window κ 只覆盖 `0 < b < r/100`（`nr := 0` 只去下界），K-seq 固定 `ρ_nc = r_n/200`
  （`regionalKappa_of_window_center_half_C11Q4`）。
口径（R-C11-5 D-10）：κ 只依赖 `A₊`，与 `v, n, D, L, B` 无关；**eventual tail 可依赖 `B + L²`**（footprint
深度），κ 不依赖。`LocalKappaWideAt_C11Q`（wide supply）**不是**区域 κ 的单纯实例化（需 seed shift + 自己的
小抛物曲率 / 体积 / accuracy，`κ(A, L)` 量词），不要直接当 regional 用。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **`U ⊆ B(O, R)` ⇐ `hdistV`（逐点）**：`d(c, z) < ρU` 且 `d(O, c) + ρU ≤ R` ⇒ `d(O, z) < R`。 -/
theorem edist_lt_of_center_C11Q4 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {O c z : M}
    {ρU R : ℝ} (hz : riemannianEDistOf g c z < ENNReal.ofReal ρU)
    (hc : riemannianEDistOf g O c + ENNReal.ofReal ρU ≤ ENNReal.ofReal R) :
    riemannianEDistOf g O z < ENNReal.ofReal R := by
  have hfin : riemannianEDistOf g O c ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hc)
  calc
    riemannianEDistOf g O z ≤ riemannianEDistOf g O c + riemannianEDistOf g c z :=
      riemannianEDistOf_triangle g O c z
    _ < riemannianEDistOf g O c + ENNReal.ofReal ρU := ENNReal.add_lt_add_left hfin hz
    _ ≤ ENNReal.ofReal R := hc

/-- **`U ⊆ B(O, R)` ⇐ `hdistV`（球形）**：`B(c, ρU) ⊆ B(O, R)` 当 `d(O, c) + ρU ≤ R`。 -/
theorem ball_subset_of_center_C11Q4 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {O c : M}
    {ρU R : ℝ} (hc : riemannianEDistOf g O c + ENNReal.ofReal ρU ≤ ENNReal.ofReal R) :
    riemannianBallOf g c ρU ⊆ riemannianBallOf g O R :=
  fun _ hz => edist_lt_of_center_C11Q4 g hz hc

/-- **区域 κ，中心分开绑定**（R-C11-5 D-8）：window 形 `LocalKappaWindowAt_P6B F (fun _ => 0) A κ` 给晚期
阈值 `T`；对 `T ≤ t₀` 的种子 `(t₀, p, r)`、trace（中心 `O_τ`），stage `j.castSucc` 的坏点中心 `c` 与区域
`U`，若 `[a, t] ⊆ [t₀ − r²/2, t₀]`、`ρ < r/100`，且在开 slab 的每个 `τ ∈ [a, t]`：
`hUc`：`U ⊆ B_τ(c, ρU)`（经 `HEq` 识别）；`hdistV`：`d_τ(O_τ, c) + ρU ≤ A r`，
则 `RegionalKappa_C11Q3 (F.tower.history n) j U a t ρ κ`。 -/
theorem regionalKappa_of_window_center_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A κ : ℝ} (hκ : 0 ≤ κ)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) A κ) :
    ∃ T : ℝ, 0 < T ∧ ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t₀ : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t₀).Carrier) (r : ℝ),
      T ≤ (t₀ : ℝ) → 2 * r ^ 2 < (t₀ : ℝ) → hasSmallParabolicCurvature H t₀ p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t₀) t₀) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t₀), (aSeed : ℝ) = (t₀ : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t₀)
        (H.activeStage_mono haT) p,
      ∀ (j : Fin (F.tower.history n).eventCount)
        (c : ((F.tower.history n).stage j.castSucc).Carrier)
        (U : Set ((F.tower.history n).stage j.castSucc).Carrier) (a t ρ ρU : ℝ),
        (t₀ : ℝ) - r ^ 2 / 2 ≤ a → t ≤ (t₀ : ℝ) → ρ < r / 100 →
        (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (F.tower.history n).time j.castSucc < τ → (τ : ℝ) < (F.tower.history n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : (H.stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf (H.stageMetric (H.activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (F.tower.history n).time j.castSucc < τ → (τ : ℝ) < (F.tower.history n).time j.succ →
          ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ t₀), ∀ cc : (H.stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
                (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav)
                  (H.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (A * r)) →
        RegionalKappa_C11Q3 (F.tower.history n) j U a t ρ κ := by
  obtain ⟨T, hT, hK⟩ := hW
  refine ⟨T, hT, ?_⟩
  intro n H t₀ p r hTt hr hsmall hvol aSeed haT hclock seedTrace j c U a t ρ ρU ha ht hρ hUc
    hdistV τ haτ hτt hs1 hs2 z hz zz hzz b hb hbρ hball
  have hr0 : 0 < r := hsmall.1
  have hav : aSeed ≤ τ := by
    change (aSeed : ℝ) ≤ (τ : ℝ)
    rw [hclock]
    nlinarith
  have hvt : τ ≤ t₀ := by
    change (τ : ℝ) ≤ (t₀ : ℝ)
    linarith
  have hcc : HEq (cast (type_eq_of_heq hzz).symm c) c := cast_heq _ _
  have hx := edist_lt_of_center_C11Q4 (H.stageMetric (H.activeStage τ) τ)
    (hUc τ haτ hτt hs1 hs2 z hz zz _ hzz hcc) (hdistV τ haτ hτt hs1 hs2 hav hvt _ hcc)
  have h := hK n t₀ p r hTt hr hsmall hvol aSeed haT hclock seedTrace τ hav hvt (by linarith)
    zz hx b (by simpa using hb.le) (hbρ.trans_lt hρ) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **K-seq 尺度 `ρ_nc = r/200`**（R-C11-5 D-8：window κ 只覆盖 `b < r/100`）：上一定理在 `ρ = r/200`。 -/
theorem regionalKappa_of_window_center_half_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A κ : ℝ} (hκ : 0 ≤ κ)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) A κ) :
    ∃ T : ℝ, 0 < T ∧ ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t₀ : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t₀).Carrier) (r : ℝ),
      T ≤ (t₀ : ℝ) → 2 * r ^ 2 < (t₀ : ℝ) → hasSmallParabolicCurvature H t₀ p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t₀) t₀) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t₀), (aSeed : ℝ) = (t₀ : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t₀)
        (H.activeStage_mono haT) p,
      ∀ (j : Fin (F.tower.history n).eventCount)
        (c : ((F.tower.history n).stage j.castSucc).Carrier)
        (U : Set ((F.tower.history n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (t₀ : ℝ) - r ^ 2 / 2 ≤ a → t ≤ (t₀ : ℝ) →
        (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (F.tower.history n).time j.castSucc < τ → (τ : ℝ) < (F.tower.history n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : (H.stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf (H.stageMetric (H.activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (F.tower.history n).time j.castSucc < τ → (τ : ℝ) < (F.tower.history n).time j.succ →
          ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ t₀), ∀ cc : (H.stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
                (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav)
                  (H.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (A * r)) →
        RegionalKappa_C11Q3 (F.tower.history n) j U a t (r / 200) κ := by
  obtain ⟨T, hT, hK⟩ := regionalKappa_of_window_center_C11Q4 hκ hW
  refine ⟨T, hT, ?_⟩
  intro n H t₀ p r hTt hr hsmall hvol aSeed haT hclock seedTrace j c U a t ρU ha ht hUc hdistV
  have hr0 : 0 < r := hsmall.1
  exact hK n t₀ p r hTt hr hsmall hvol aSeed haT hclock seedTrace j c U a t (r / 200) ρU ha ht
    (by linarith) hUc hdistV

/-- **consumer（G5）**：中心分开绑定的区域 κ（`ρ = r/200`）原样喂 G3 桥
`tested_noncollapse_eventPrefix_P6M`（prefix 历史上的 SLT `hnc` 形），在 `U = B_v(c, ρU)` 时 `τ = v` 的
`hUc` 就是 `U` 的定义。 -/
example (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (U : Set (K.stage j.castSucc).Carrier) {a t r κ : ℝ}
    (h : RegionalKappa_C11Q3 K j U a t (r / 200) κ)
    (hend : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) =
      (K.prefixAt j.castSucc).horizon) :
    ∀ (T : ℝ) (hT : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) < T)
      (hTs : T < K.time j.succ), T ≤ t → a ≤ T →
        let B := (K.prefixAt j.castSucc).extendHorizon T (hend ▸ hT.le)
          ((K.toHistory.event j).incoming.closedPrefix T hT hTs) (K.event_initial j)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (K.prefixAt j.castSucc).horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ r / 200 →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b) :=
  K.tested_noncollapse_eventPrefix_P6M j U h hend

end GC.LongTime.Ch11

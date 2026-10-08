import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorThirdKappaP6AN3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedC11PB

/-!
# ANCHOR 第四轮 G1：top 梯度半 ⇐ hgood 的 witness `gradient` 字段（O-CH11-ANCHOR4，后缀 `_P6AN4`）

ANCHOR3 G4 的 `topAnchorInputs_of_hgood_hkappa_P6AN3` 用旧全域背景 `hgradG`（event `j` incoming slab 的
`GradientBoundBefore Cgrad qg (t n)`）付 top 版 `hgradPB`。**唯一用点**：top 点 `v = t n`、中心 `w = yG n`、
球 `B_t(yG, Rad/√R_n)`（`Rad` 任意，ShortSLT 给）、窗口 `v′ ∈ (time j⁻, t) ∩ [t − β/R_n, t)`、阈值 `Cg·R_n`。
本文件把它换成 hgood 的局域来源：
* `SpatialCanonicalWitness.gradient` 是 **witness 点本身** 的逐点界 `|dR(x)| ≤ C₂ R(x)^{3/2}`；hgood
  （`HgoodCg_C11SH`）在其区域（`d_v(seed(v), z) ≤ d_σ(seed(σ), y) + L/√R_n`、`R(v, z) ≥ Cg·R_n`、
  `v ∈ [aSeed, σ] ∩ [σ − L²/R_n, σ]`）每点给一个 witness ⇒ 梯度在 hgood 区域**逐点**成立。窗口球点要先
  **定位**进 hgood 区域：这就是 binder **hseedTop**（下）。
* `pickedBallWindowSeed_top_of_window_P6AN4`（PROVED，桥）：hseedTop 的 activeStage 形（`Kh` 层，度量
  `stageMetric (activeStage σ) s`，与 `hscalW` 的 ExitGuard 同形）⇒ PICKBALL
  `PickedBallWindowSeed_C11PB` 在 top 点（`v := t n`、`w := yG n`、seed 点 `seedTrace.point (j n)⁻`）。
* `hgradL_of_hgood_witness_P6AN4`（G1 主定理，PROVED ⇐ hgood + hseedTop 在 `n` 处）：结论 =
  `pickedBallGrad_of_gradientBound_P6AN3` 的输出**逐字**
  （`PickedBallGrad_C11PB β Rad (Cg·R_n) Cgrad (K n) (j n) (t n) (yG n)`），`C₂ ≤ Cgrad`；
  证明 = PICKBALL G4 `pickedBallGrad_of_hgood_C11PB` 在 top 点实例化。
  序列版 `hgradL_seq_of_hgood_witness_P6AN4`（时间域 `aSeed ≤ t − β/R` ⇐ `hwin β`，`σ − L²/R ≤ t − β/R` ⇐
  `L → ∞`）= ANCHOR3 `hgradPB` 槽逐字。
* 组合 `topAnchorInputs_of_hgood_local_P6AN4` 与全链 `hdistW_eventSlab_of_hgood_local_P6AN4`：
  `GradientBoundBefore` / `hgradG` / `qg` 全部消去，换成 `hC2 : C2g ≤ Cgrad` + **hseedTop**。

**hseedTop（PROVISIONAL binder；单列 BLOCKED：两条已知来源都循环）**：
`∀ Rad, ∀ᶠ n, ∀ x ∈ B_σ(y, Rad/√R_n), ∀ s ∈ [σ − β/R_n, σ)`（`time (activeStage σ) < s`）、
`Cg·R_n < R(s, x)` ⇒ `d_s(seed(σ⁻), x) ≤ d_σ(seed(σ), y) + L/√R_n`（窗口 seed-distance closure，带阈值守卫）。
1. 它是 `hdistW` 槽（链自身结论）在 `(D := Rad, T := β)`、同 stage 的限制（再加阈值守卫，更弱）⇒ 用链结论付 = 循环。
2. CXJD `hstop_of_firstExit_CXJD`（first-exit seed closure）要端点 top 球 ceiling `R(σ, x) ≤ Q_b·R_n`
   （`x ∈ B_σ(y, Rad/√R_n)`）= 半径 `Rad` 的 `hanchor0`，而 `hanchor0` 是 ShortSLT 的输出，ShortSLT 又吃本梯度 ⇒ 循环。
3. SEEDCL2 `pickedBallWindowSeed_of_firstExit_local_C11SC2`（22:08 交付，内部 stopped first-exit，产
   `PickedBallWindowSeed_C11PB` 逐字）由 hpick `PickedBallTop_C11PB Λ Rad` 门控；在 top 点（`v = σ`、`w = y`）
   hpick = top 球 `B_t(y, Rad/√R_n)` 上 `R ≤ Λ R_n` = 半径 `Rad` 的 `hanchor0` ⇒ 同 2 循环
   （ANCHOR3 G3 发现的同一个点）。
三条共同缺口 = **top 切片在半径 `Rad` 处的 BCBD**（`hanchor0`）先于窗口梯度。
**非循环 repair target**（owner KSW / 外审 R-C11-18）：`ShortSLT_C11KS` 的 U 侧前提（witness / 导数 / 梯度，
`∀ x ∈ U, ∀ v ∈ [t − θ/R, t)`）加 ExitGuard / ceiling guard（只在 `[v, t]` 上轨迹留在 hgood 区域、或 `R ≤ Λ·R`
的点要求），让 first-exit 在 KSW 证明内部完成；等价的半径归纳形：U 侧数据只在 top 球 BCBD 已成立的半径
`ρ < ρ₀` 内要求（此时 SEEDCL2 的 hpick 门控在半径 `ρ` 处可付）。届时 hseedTop 由 KSW 内部 continuity 付，
本文件结论形不变。
非循环（本文件层面）：前提中无 `hdistW` 槽 / `HU` / `hgapJ` / `hclosG` / `CanonicalLateCore` / `hspine` /
`GradientBoundBefore`（审计做传递依赖名字扫描）。不声称闭合。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section GradLocal

/-- **桥（`_P6AN4`，PROVED）**：hseedTop 在 `n` 处的 activeStage 形（度量 `stageMetric (activeStage σ) s`、
球 `B_σ(y, Rad/√R_n)`、开窗 `[σ − β/R_n, σ)`、阈值守卫 `Cg·R_n < R`）⇒ PICKBALL
`PickedBallWindowSeed_C11PB β Rad (Cg·R_n)` 在 top 点（`v := t n`、`w := yG n`、seed 点
`seedTrace.point (j n)⁻`）。`activeStage σ = (j n)⁻`（`activeStage_eq_castSucc_C11PB`）经一般化 `k` +
`subst` 换掉，`stageMetric_castSucc_apply` 把 stage 度量换成 event incoming 度量，`y ≅ yG`、`R_n = R(t, yG)`。 -/
theorem pickedBallWindowSeed_top_of_window_P6AN4 {Cg β Rad : ℝ}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (n : ℕ) (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc)
    (h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (hW :
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    PickedBallWindowSeed_C11PB β Rad (Cg * R n) (K n) (j n) (t n) (yG n)
      ((seedTrace n).point (j n).castSucc h1 h2)
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n))) := by
  have hv1 : (K n).time (j n).castSucc < σ n := by
    rw [hσ n]
    exact hjt n
  have hv2 : ((σ n : ℝ)) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact := (K n).activeStage_eq_castSucc_C11PB (j n) (σ n) hv1 hv2
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' yk : ((K n).toHistory.stage k).Carrier),
      HEq (y n) yk →
      x' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
      ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n → (K n).toHistory.time k < s →
      Cg * R n < metricScalarAt ((K n).toHistory.stageMetric k s) x' →
      riemannianEDistOf ((K n).toHistory.stageMetric k s) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x' yk hy hx s hs1 hs2 hs3 hRs
    obtain rfl := eq_of_heq hy
    exact hW x' hx s hs1 hs2 hs3 hRs
  intro x hx v' hv' hwin hRx
  have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (j n).castSucc (σ n)) (yG n)
      (Rad / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply, hσ n, hRn n]
    exact hx
  have hs1 : (σ n : ℝ) - β / R n ≤ v' := by
    rw [hσ n, hRn n]
    exact hwin
  have hs2 : v' < σ n := by
    rw [hσ n]
    exact hv'.2
  have hRs : Cg * R n < metricScalarAt ((K n).toHistory.stageMetric (j n).castSucc v') x := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hRx
  have hres := key (j n).castSucc hact h1 h2 x (yG n) (hyG n) hx' v' hs1 hs2 hv'.1 hRs
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  exact hres

/-- **G1 `hgradL_of_hgood_witness_P6AN4`（`_P6AN4`，PROVED ⇐ hgood + hseedTop 在 `n` 处）**：
ANCHOR3 `hgradG` 槽的局域替换。结论 = `pickedBallGrad_of_gradientBound_P6AN3` 的输出逐字
（`qthr := Cg·R_n`、`v := t n`、
`w := yG n`）。来源：hgood 的 `SpatialCanonicalWitness.gradient`（witness 点逐点界）经 PICKBALL G4
`pickedBallGrad_of_hgood_C11PB`；窗口球点进 hgood 区域由 hseedTop
（经 `pickedBallWindowSeed_top_of_window_P6AN4`）；
时间域 `aSeed ≤ σ − β/R_n`（`hav`）、`σ − L²/R_n ≤ σ − β/R_n`（`hvL`）、`t ≤ σ`（`hσ`）。 -/
theorem hgradL_of_hgood_witness_P6AN4 {Cg β Rad : ℝ} {Cgrad : ℝ≥0}
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
    (hC2 : C2 ≤ (Cgrad : ℝ))
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (n : ℕ) (hav : (aSeed n : ℝ) ≤ σ n - β / R n)
    (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n - β / R n)
    (hW :
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) (j n) (t n) (yG n) := by
  have hv1 : (K n).time (j n).castSucc < σ n := by
    rw [hσ n]
    exact hjt n
  have hv2 : ((σ n : ℝ)) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact := (K n).activeStage_eq_castSucc_C11PB (j n) (σ n) hv1 hv2
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc :=
    hact ▸ (K n).toHistory.activeStage_mono (has n)
  have h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n) :=
    hact ▸ (K n).toHistory.activeStage_mono (hsT n)
  have hseed := pickedBallWindowSeed_top_of_window_P6AN4 K (haT := haT) (hsT := hsT) (has := has)
    hjt htj hσ hyG hRn n h1 h2 hW
  have hav' : (aSeed n : ℝ) ≤ t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
      (yG n) := by
    rw [← hRn n, ← hσ n]
    exact hav
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤
      t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
    rw [← hRn n, ← hσ n]
    exact hvL
  exact pickedBallGrad_of_hgood_C11PB K hgood hC2 n (j n) (t n) (htj n) h1 h2 (yG n) hav'
    (hσ n).ge hvL' hseed

/-- **G1 序列版（`_P6AN4`，PROVED ⇐ hgood + hseedTop）**：结论 = ANCHOR3 `hgradPB` 槽逐字
（`∀ Rad, ∀ᶠ n, PickedBallGrad_C11PB β Rad (Cg·R_n) Cgrad (K n) (j n) (t n) (yG n)`）。时间域：`hwin β`
给 `aSeed ≤ σ − β/R_n`；`L ≥ max β 1` 给 `β ≤ L²`（`L → ∞`）。 -/
theorem hgradL_seq_of_hgood_witness_P6AN4 {Cg β : ℝ} {Cgrad : ℝ≥0}
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
    (hC2 : C2 ≤ (Cgrad : ℝ))
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop)
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) (j n) (t n) (yG n) := by
  intro Rad
  filter_upwards [hseedTop Rad, hwin β hβ, hL.eventually_ge_atTop (max β 1)] with n hW ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans hLn
  have hβL : β ≤ L n ^ 2 := by nlinarith [le_max_left β 1]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  exact hgradL_of_hgood_witness_P6AN4 K hgood hC2 hjt htj hσ hyG hRn n ha (by linarith) hW

end GradLocal

section LocalChain

/-- **`topAnchorInputs_of_hgood_local_P6AN4`（G1 组合，PROVISIONAL：binder = hseedTop（BLOCKED，见文件头）+
旧全域导数 `hslab / hderG`（J10GEN 迁移义务）+ P6CD 层 supplies（含 `hkappa`）+ hgood；
**无** `GradientBoundBefore`）**：
= `topAnchorInputs_of_hgood_hkappa_P6AN3`，只把 `hgradPB` 的来源从
`pickedBallGrad_of_gradientBound_P6AN3 … hgradG` 换成
 `hgradL_seq_of_hgood_witness_P6AN4`（hgood witness 的 `gradient` 字段 + hseedTop），`Cgrad ≥ C2`。 -/
theorem topAnchorInputs_of_hgood_local_P6AN4 {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    {Cg : ℝ} (hCg : 0 < Cg)
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {ε C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hC2 : C2 ≤ (Cgrad : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact topAnchorInputs_of_hgood_P6AN3 hβ hjt htj hcan hqcan hpar hscale hθcap hphi hpinch hslab
    hderG hqR hnot hT₀ hRt hCg hgood hσ hyG hRn hL hε hκ hradii
    (hgradL_seq_of_hgood_witness_P6AN4 K hgood hC2 hjt htj hσ hyG hRn hRpos hβ0 hwin hL hseedTop)
    (pickedBallKappa_top_seq_of_hkappa_P6AN3 hjt htj hσ hyG hRn hRpos hκ.le hkappa)

/-- **`hdistW_eventSlab_of_hgood_local_P6AN4`（G1 全链，PROVISIONAL：binder = hseedTop（BLOCKED：两条已知来源
循环，repair = guarded ShortSLT，见文件头）+ `hbcadC` + P6CD 层 supplies（含 `hkappa / hseed / hwitC`）+ hgood +
旧全域导数背景 `hslab / hderG`（J10GEN 迁移义务））**：= `hdistW_eventSlab_of_hgood_P6AN3`，其中
`∀ {qg Cgrad}, qg ≤ Cg·R → GradientBoundBefore Cgrad qg t →` 换成
`∀ {Cgrad}, C2g ≤ Cgrad → hseedTop →`
（`Kh` 层 activeStage 形，`hscalW` ExitGuard 同度量）。**`GradientBoundBefore` 不再出现**。结论 = `hdistW` 槽逐字
（event 支）。 -/
theorem hdistW_eventSlab_of_hgood_local_P6AN4 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      (∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (Kh n).time ((Kh n).activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn aSeed haT
    hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood Cgrad hC2 hseedTop hL hsmall hclock
    hRr hwin a₁ ha₁ hpin
  subst hKh
  have hin := topAnchorInputs_of_hgood_local_P6AN4 hβ hβ2 hjt htj hcan hqcan hpar hscale hθcap hphi
    hpinch hslab hderG hqR hnot hT₀ hRt hCg hgood hσ hyG hRn hL hεg hκ hradii hC2 hwin hseedTop
    hkappa
  exact hscalW_eventSlab_to_hdistW_P6AN3 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan hδF hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin (fun n => (K n).toHistory) rfl σ y
    R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC Tn aSeed haT hsT has pT
    seedTrace L r hL hsmall hclock hRr hwin ha₁ hpin


end LocalChain

/-- consumer（G1，`_P6AN4`）：全链 `hdistW_eventSlab_of_hgood_local_P6AN4` 在 `Cgrad := C2g.toNNReal` 处
（`hC2 := Real.le_coe_toNNReal`）——梯度常数直接取 hgood witness 的 `C₂`，无独立梯度背景。 -/
example {C2g : ℝ} : C2g ≤ ((Real.toNNReal C2g : ℝ≥0) : ℝ) := Real.le_coe_toNNReal C2g

/-- consumer（G1，`_P6AN4`）：G1 序列版即 ANCHOR3 `topAnchorInputs_of_hgood_P6AN3` 的 `hgradPB` 槽：喂进去得到
`TopAnchorInputs_P6AN2`（κ 半仍由调用方给 `hκPB`）。 -/
example := @hgradL_seq_of_hgood_witness_P6AN4.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

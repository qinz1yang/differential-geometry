import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowContractC11SH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AlphaHalfMarginC11AL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.HdistCondAnySeedC11G3

/-!
# SHALLOW 接线两小件（S-CH11-SHALLOW-W，后缀 `_C11SW`）

设计 `docs/geometrization/chapter8/design-C11-shallow-20261007.md`（§3 I1 切片层、§5 Cg ∈ {4, 8}），
骨架 `Ch11/P6ShallowContractC11SH.lean`。**不证浅窗 SLT**（K-SW 仍 BLOCKED）；端点口径不变（`{A12′}`）。

* **G1（Cg = 8）**：`hgood_secondScale_C11AL` 把阈值 `4 R` 写死（L147）。本文件把证明参数化：
  `secondScale_thresholdCg_C11SW`（`Cg * R ≤ S`）、`hgood_secondScaleCg_C11SW`
  （`HgoodCg_C11SH Cg ⇒ SecondScaleCg_C11SH Cg`，任意 `Cg`）；`hgood_secondScale_Cg8_C11SW` 是 G1 的
  **逐字 Cg = 8 副本**（阈值 `8 * R n`、二次尺度下界 `max 1 (8 / η)`）。骨架 Cg 链在 8 处闭合：
  `secondScaleCg_eight_C11SW`（`HgoodCg 8 ⇒ SecondScaleCg 8`）、`SecondScaleCg_C11SH.mono_C11SW`
  （`Cg ≤ Cg′`）、`secondScaleCg_eight_of_four_C11SW`（P6R2 输出 4 ⇒ `SecondScaleCg 8`，两条路线）；
  consumer `hgood_secondScale_Cg8_of_selection_C11SW`：half-margin selection（`L/2` 版）⇒
  `¬Control` 坏点序列 ∧ `L → ∞` ∧ `HgoodCg 8` ∧ `SecondScaleCg 8`。
* **G2（输入 1 的 slice 部分）**：`SliceLocalization_C11SH` 只是 traced-conditional `hdistC` 加一次三角不等式
  （`Lp + Dd ≤ Ls`，`Dd` 为 `SliceLocalization` 的外层量词）。`sliceLocalization_of_hdistC_C11SW`
  （任意 `Lp, Ls`，`Ls − Lp → ∞`）、`sliceLocalization_of_hdistC_half_C11SW`（`hdistC` 余量 `L/4`，
  即 P6CD `hdistC` binder 逐字，得 `Lsmall := L/2`，`2 Lsmall ≤ L`）；
  `sliceInput1_of_tracedCond_C11SW`：producer `hdistC_of_traced_anySeed_C11G3`（HDISTC，K 层 traced
  region + late-K 数据）⇒ `SliceLocalization_C11SH … (L/2)`。producer 的前提原样保留为显式 binder
  （PROVISIONAL：late-K 数据 `recordsK / hcanK / hsepWK / hT₀ / HI` 与 K0 种子 `hsmall / hclock / hRr`，
  owner = late-K supply 车道 `Dist/LateRecordsSupplyC11G` 与 selection 的 K0 种子）。
  `hhalf_of_room_C11SW / hRr_of_selection_C11SW`：producer 的 `hhalf` / `hRr` binder 可由 selection
  输出（room、`hRQ`、`hdiv`）推出，故真正 PROVISIONAL 的只剩 K0 种子 `hsmall / htime`、slab 位置
  `hjt / htj / hσt`、HI `hpin` 与 late-K records 组。
  consumer `hgood_slice_of_localization_C11SW`：`SliceLocalization` + `HgoodCg Cg` ⇒ 切片上离 trace 点
  `< Dd/√R_n`、`R ≥ Cg R_n` 的每个点 `HasSpatialCanonicalTimeControl`（I1 → hgood 域）。
* 非循环：只用 `hdistC` 链（traced region + late-K 数据），不含 `hscalU / hclosG / hclosC / hUVC /
  CanonicalLateCore / hspine`（审计文件对 producer 的传递依赖做名字扫描）。第二层（坏点短窗 closure）
  与 K-SW 不在本文件。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

section CgSlot

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

/-- 二次尺度阈值（`Cg` 版，`_C11SW`）：`0 < η`、`0 ≤ R`、`max 1 (Cg/η) · R ≤ q`、`η q ≤ S` ⇒
`Cg R ≤ S`。= `secondScale_threshold_C11AL` 把 `4` 参数化为 `Cg`。 -/
theorem secondScale_thresholdCg_C11SW {Cg R q η S : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hq : max 1 (Cg / η) * R ≤ q) (hS : η * q ≤ S) : Cg * R ≤ S := by
  have h1 : Cg / η * R ≤ q := (mul_le_mul_of_nonneg_right (le_max_right _ _) hR).trans hq
  have h2 : η * (Cg / η * R) ≤ η * q := mul_le_mul_of_nonneg_left h1 hη.le
  have h3 : η * (Cg / η * R) = Cg * R := by field_simp
  linarith

variable {Kh : ℕ → ObservedHistory.{u}} {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
    ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((Kh n).stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ} {Ctime : ℝ≥0}

/-- **G1 的 `Cg` 参数化版（`_C11SW`）**：`HgoodCg_C11SH Cg ⇒ SecondScaleCg_C11SH Cg`，任意 `Cg : ℝ`。
证明 = `hgood_secondScale_C11AL` 逐行照抄，仅阈值引理换成 `secondScale_thresholdCg_C11SW`；`n` 的门槛
仍只依赖 `(T, K)`。`Cg = 4` 即 G1。 -/
theorem hgood_secondScaleCg_C11SW (Cg : ℝ) (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hgood : HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    SecondScaleCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime := by
  intro T K η hη
  filter_upwards [hL.eventually_ge_atTop (max (max 1 (T + max K 0)) (2 * max K 0))] with n hLn
  intro q hq s has' hsσ x hsT' hx v hav hvs hvK z hz hRz
  have hRn := hR n
  have hRq : R n ≤ q :=
    le_trans (le_mul_of_one_le_left hRn.le (le_max_left _ _)) hq
  have hL1 : 1 ≤ L n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLn
  have hTK : T + max K 0 ≤ L n ^ 2 := by
    have h1 : T + max K 0 ≤ L n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLn
    nlinarith
  have hKL : 2 * max K 0 ≤ L n := le_trans (le_max_right _ _) hLn
  have htime : (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) :=
    secondScale_time_C11AL hRn hRq hTK hsT' hvK
  refine hgood n v hav (hvs.trans hsσ) htime z ?_ (secondScale_thresholdCg_C11SW hη hRn.le hq hRz)
  calc riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
        ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
          ((Kh n).activeStage_mono ((hvs.trans hsσ).trans (hsT n)))) z
      ≤ (riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) + ENNReal.ofReal (K / Real.sqrt q) :=
        hz.trans (add_le_add hx le_rfl)
    _ ≤ riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
        rw [add_assoc]
        exact add_le_add le_rfl (secondScale_margin_C11AL hRn hRq hKL)

/-- **链在 8 处闭合 ①（`_C11SW`）**：`HgoodCg_C11SH 8 ⇒ SecondScaleCg_C11SH 8`（`Cg = 8` 的输入比
`Cg = 4` 弱：阈值 `8 R n`）。 -/
theorem secondScaleCg_eight_C11SW (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (h : HgoodCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    SecondScaleCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime :=
  hgood_secondScaleCg_C11SW 8 hR hL h

/-- **`SecondScaleCg` 关于 `Cg` 单调（`_C11SW`）**：`Cg ≤ Cg′`、`0 ≤ R n` ⇒
`SecondScaleCg_C11SH Cg ⇒ SecondScaleCg_C11SH Cg′`（`max 1 (Cg′/η) R ≤ q` 蕴含
`max 1 (Cg/η) R ≤ q`）。 -/
theorem SecondScaleCg_C11SH.mono_C11SW {Cg Cg' : ℝ} (hCg : Cg ≤ Cg') (hR : ∀ n, 0 ≤ R n)
    (h : SecondScaleCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    SecondScaleCg_C11SH Cg' Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime := by
  intro T K η hη
  filter_upwards [h T K η hη] with n hn
  intro q hq
  exact hn q (le_trans (mul_le_mul_of_nonneg_right
    (max_le_max le_rfl (div_le_div_of_nonneg_right hCg hη.le)) (hR n)) hq)

/-- **链在 8 处闭合 ②（`_C11SW`）**：P6R2 / half-margin selection 的输出（`HgoodCg 4`）⇒
`SecondScaleCg_C11SH 8`。路线 A：`hgoodCg_eight_of_four_C11SH` 再 `secondScaleCg_eight_C11SW`。 -/
theorem secondScaleCg_eight_of_four_C11SW (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (h : HgoodCg_C11SH 4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    SecondScaleCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime :=
  secondScaleCg_eight_C11SW hR hL (hgoodCg_eight_of_four_C11SH (fun n => (hR n).le) h)

/-- **链在 8 处闭合 ③（`_C11SW`）**：路线 B：骨架的 `secondScaleCg_four_C11SH`（= G1）再
`SecondScaleCg_C11SH.mono_C11SW`（4 ⇒ 8）。两条路线结论同一个 Prop。 -/
theorem secondScaleCg_eight_of_four_mono_C11SW (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (h : HgoodCg_C11SH 4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    SecondScaleCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime :=
  SecondScaleCg_C11SH.mono_C11SW (by norm_num) (fun n => (hR n).le)
    (secondScaleCg_four_C11SH hR hL h)

end CgSlot

section Cg8Literal

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

/-- **G1 的逐字 Cg = 8 副本（`_C11SW`）**：`hgood_secondScale_C11AL` 的陈述，只把 `4 * R n` 换成
`8 * R n`、`max 1 (4 / η)` 换成 `max 1 (8 / η)`。证明 = 参数化版 `hgood_secondScaleCg_C11SW 8`
（`HgoodCg_C11SH 8` 是 `hgood` 合取项的定义展开）。 -/
theorem hgood_secondScale_Cg8_C11SW (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        8 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    ∀ T K η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ q : ℝ, max 1 (8 / η) * R n ≤ q →
      ∀ (s : Icc (0 : ℝ) (Kh n).horizon) (has' : aSeed n ≤ s) (hsσ : s ≤ σ n)
        (x : ((Kh n).stageAt s).Carrier),
        (σ n : ℝ) - T / R n ≤ (s : ℝ) →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
            ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
              ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s),
        (s : ℝ) - K / q ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono ((hvs.trans hsσ).trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
              ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
                ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) x +
            ENNReal.ofReal (K / Real.sqrt q) →
        η * q ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z :=
  hgood_secondScaleCg_C11SW (Kh := Kh) (Tn := Tn) (aSeed := aSeed) (σ := σ) (haT := haT)
    (hsT := hsT) (has := has) (pT := pT) (seedTrace := seedTrace) (y := y) (R := R) (L := L)
    (eps := eps) (C1 := C1) (C2 := C2) (Ctime := Ctime) 8 hR hL hgood

end Cg8Literal

section Consumer

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **G1 consumer（`_C11SW`）**：half-margin selection（`selection_of_bad_sequence_retained_half_C11AL`，
`L/2` 版，前提逐字）⇒ 存在 selection `(σ, y, R, L)`：坏点 `¬Control(σ, y)`、`L → ∞`，且
`HgoodCg_C11SH 8` 与 `SecondScaleCg_C11SH 8` 成立（hgood 由 `4` 经 `hgoodCg_eight_of_four_C11SH` 得 `8`；
二次尺度控制由 `secondScaleCg_eight_C11SW`）。喂 `P6ShallowContractC11SH` 的 Cg 合同。 -/
theorem hgood_secondScale_Cg8_of_selection_C11SW {Kh : ℕ → ObservedHistory.{u}}
    (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ),
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ n) (y n)) ∧
      Tendsto L atTop atTop ∧
      HgoodCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1' C2' Ctime' ∧
      SecondScaleCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1' C2' Ctime' := by
  obtain ⟨σ, y, R, hsT, has, L, ⟨-, hRpos, -, -, hL, hsel, hgood, -⟩, -⟩ :=
    selection_of_bad_sequence_retained_half_C11AL q hC1 hC2 hCtime hanti hcanonical hderivative Tn
      pT r A hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  have h4 : HgoodCg_C11SH 4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1' C2' Ctime' :=
    hgood
  have h8 := hgoodCg_eight_of_four_C11SH (fun n => (hRpos n).le) h4
  exact ⟨σ, y, R, hsT, has, L, hsel, hL, h8, secondScaleCg_eight_C11SW hRpos hL h8⟩

end Consumer

section SliceWire

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open Perelman.CanonicalNeighborhood.FiniteHorn

/-- 余量算术（`_C11SW`）：`d(O, w) ≤ d(O, p) + d(p, w)`、`d(O, p) ≤ dσ + Lp/s`、`d(p, w) ≤ Dd/s`、
`Lp + Dd ≤ Ls` ⇒ `d(O, w) ≤ dσ + Ls/s`（`ENNReal` 层，无流形依赖）。 -/
theorem ennreal_margin_C11SW {dO dp dw dσ : ℝ≥0∞} {Lp Dd Ls s : ℝ} (hLp : 0 ≤ Lp) (hDd : 0 ≤ Dd)
    (hs : 0 ≤ s) (hgap : Lp + Dd ≤ Ls) (htri : dO ≤ dp + dw)
    (hp : dp ≤ dσ + ENNReal.ofReal (Lp / s)) (hw : dw ≤ ENNReal.ofReal (Dd / s)) :
    dO ≤ dσ + ENNReal.ofReal (Ls / s) := by
  calc dO ≤ dp + dw := htri
    _ ≤ (dσ + ENNReal.ofReal (Lp / s)) + ENNReal.ofReal (Dd / s) := add_le_add hp hw
    _ = dσ + ENNReal.ofReal (Lp / s + Dd / s) := by
        rw [add_assoc, ENNReal.ofReal_add (div_nonneg hLp hs) (div_nonneg hDd hs)]
    _ ≤ dσ + ENNReal.ofReal (Ls / s) := by
        refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
        rw [← add_div]
        exact div_le_div_of_nonneg_right hgap hs

/-- **producer binder `hhalf` ⇐ selection 的 room（`_C11SW`）**：`Tn − r²/2 ≤ σ − L²/R`（half-margin
selection 的第三个输出）与 `0 < R` 给出 producer 的半深度 binder `Tn − r²/2 ≤ σ`。 -/
theorem hhalf_of_room_C11SW {Tn σ R r L : ℕ → ℝ} (hR : ∀ n, 0 < R n)
    (hroom : ∀ n, Tn n - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) :
    ∀ n, Tn n - r n ^ 2 / 2 ≤ σ n := fun n => by
  have h : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hR n).le
  linarith [hroom n]

/-- **producer binder `hRr` ⇐ selection（`_C11SW`）**：`R₀ r² → ∞`（selection 的 `hdiv`）与
`R₀ ≤ R`（selection 的 `hRQ`）给出 `R r² → ∞`。 -/
theorem hRr_of_selection_C11SW {xs R r : ℕ → ℝ} (hRQ : ∀ n, xs n ≤ R n)
    (hdiv : Tendsto (fun n => xs n * r n ^ 2) atTop atTop) :
    Tendsto (fun n => R n * r n ^ 2) atTop atTop :=
  tendsto_atTop_mono (fun n => mul_le_mul_of_nonneg_right (hRQ n) (sq_nonneg _)) hdiv

variable {Kh : ℕ → ObservedHistory.{u}} {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
    ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((Kh n).stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ} {Ctime : ℝ≥0}

/-- **输入 1 的 slice 部分 ⇐ traced-conditional `hdistC`（`_C11SW`，PROVED）**：`hdistC` = P6CD /
HDISTC 的 `hdistC` binder（traced `(2D, T, Kc)` 沿子列 `φ`，余量 `Lp`；`Lp` 一般）。三角不等式
`d_v(O_v, w) ≤ d_v(O_v, tr₁(v)) + d_v(tr₁(v), w)`、`d_v(tr₁(v), w) < Dd/√R`，故余量
`Lsmall := Ls` 只需 `Lp n + Dd ≤ Ls n`（`n` 门槛吸收 `Dd`）。只用 traced region 上的 `hdistC`，不涉及
`hscalU / hclosG / hclosC / hUVC / CanonicalLateCore / hspine`。 -/
theorem sliceLocalization_of_hdistC_C11SW {Lp Ls : ℕ → ℝ} (hR : ∀ᶠ n in atTop, 0 < R n)
    (hLp : Tendsto Lp atTop atTop) (hgap : ∀ c : ℝ, ∀ᶠ n in atTop, Lp n + c ≤ Ls n)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (Lp n / Real.sqrt (R n))) :
    SliceLocalization_C11SH Kh Tn aSeed σ haT hsT has pT seedTrace y R Ls := by
  intro Dd hDd φ hφ σ' hσ' Dw hDw T K hT hK htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hT0 : 0 < T := by linarith
  filter_upwards [hdistC φ hφ Dw T K hDw hT0 hK htr, hφt.eventually hR,
    hφt.eventually (hLp.eventually_ge_atTop 0), hφt.eventually (hgap Dd)]
    with n hn hRn hLpn hgapn
  intro x₁ hx₁ v hav hvt hv tr₁ w hw
  have hvT : (σ n : ℝ) - T / R n ≤ v := by
    have h1 : -σ' / R n ≤ T / R n := div_le_div_of_nonneg_right hT.le (le_of_lt hRn)
    have h2 : -σ' / R n = -(σ' / R n) := neg_div _ _
    rw [hv]
    linarith
  exact ennreal_margin_C11SW hLpn hDd.le (Real.sqrt_nonneg _) hgapn
    (riemannianEDistOf_triangle _ _ _ _) (hn x₁ hx₁ v hav hvt hvT tr₁) hw.le

/-- **同上，`hdistC` 余量 `L/4`（P6CD binder 逐字），`Lsmall := L/2`（`_C11SW`，PROVED）**：
`L → ∞`；`Lsmall → ∞`，`2 · Lsmall ≤ L`（`L_small < L_good`，下游第二层 closure 的余量 `L/2`）。 -/
theorem sliceLocalization_of_hdistC_half_C11SW (hR : ∀ᶠ n in atTop, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) :
    SliceLocalization_C11SH Kh Tn aSeed σ haT hsT has pT seedTrace y R (fun n => L n / 2) := by
  refine sliceLocalization_of_hdistC_C11SW (Lp := fun n => L n / 4) hR
    (hL.atTop_div_const (by norm_num)) (fun c => ?_) hdistC
  filter_upwards [hL.eventually_ge_atTop (4 * c)] with n hn
  show L n / 4 + c ≤ L n / 2
  linarith

/-- **G2 consumer（`_C11SW`）**：`SliceLocalization` + `HgoodCg Cg` ⇒ 切片 `v = σ + σ′/R` 上离 trace 点
`< Dd/√R_n`、`R(v, w) ≥ Cg R_n` 的每个点 `w` 处处 `HasSpatialCanonicalTimeControl`（I1 把坏点放进
`hgood` 的 seed 域；`Ls n ≤ L n`，时间域 `σ − L²/R ≤ v` 由 `T ≤ L²` eventually）。 -/
theorem hgood_slice_of_localization_C11SW {Cg : ℝ} {Ls : ℕ → ℝ} (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop) (hLs : ∀ n, Ls n ≤ L n)
    (hloc : SliceLocalization_C11SH Kh Tn aSeed σ haT hsT has pT seedTrace y R Ls)
    (hgood : HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    ∀ Dd : ℝ, 0 < Dd → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ v : Icc (0 : ℝ) (Kh n).horizon, aSeed n ≤ v → ∀ hvt : v ≤ σ n,
        (v : ℝ) = σ n + σ' / R n →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
      ∀ w : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w →
        (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v w := by
  intro Dd hDd φ hφ σ' hσ' Dw hDw T K hT hK htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  filter_upwards [hloc Dd hDd φ hφ σ' hσ' Dw hDw T K hT hK htr,
    hφt.eventually (hL.eventually_ge_atTop (max T 1))] with n hn hLn
  intro x₁ hx₁ v hav hvt hv tr₁ w hw hCg
  have hRn := hR n
  have hL1 : 1 ≤ L n := le_trans (le_max_right _ _) hLn
  have hTL : T ≤ L n ^ 2 := by
    have h1 : T ≤ L n := le_trans (le_max_left _ _) hLn
    nlinarith
  have htime : (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) := by
    have h1 : T / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hTL hRn.le
    have h2 : -σ' / R n ≤ T / R n := div_le_div_of_nonneg_right hT.le hRn.le
    have h3 : -σ' / R n = -(σ' / R n) := neg_div _ _
    rw [hv]
    linarith
  have hdist := (hn x₁ hx₁ v hav hvt hv tr₁ w hw).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (hLs n) (Real.sqrt_nonneg _))))
  exact hgood n v hav hvt htime w hdist hCg

end SliceWire

end ObservedHistory

section ProducerWire

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

/-- **输入 1 的 slice 部分 ⇐ 既有 traced-conditional 距离 producer（`_C11SW`）**：producer =
`hdistC_of_traced_anySeed_C11G3`（HDISTC：K 层 traced region + late-K 数据 ⇒ `hdistC`，任意 `Tn ≥ σ`
种子）。前提（逐字 = producer 的前提，**显式 binder，PROVISIONAL**）：
* 可由 selection 输出推出（不是缺口）：`hR / hL`（selection 的 `0 < R`、`L → ∞`）、`hclock`（= `haSeed`）、
  `hhalf`（`hhalf_of_room_C11SW`，selection 的 room）、`hRr`（`hRr_of_selection_C11SW`）；
* K0 种子（PROVISIONAL）：`hsmall`（`hasSmallParabolicCurvature (Tn, pT, r)`）、`htime`（`2 r² < Tn`），
  owner = K0 种子 / `P6ANCH2` 车道；slab 位置 `hjt / htj / hσt`（`σ ≤ t` 在事件 slab 内），owner =
  selection 的 K-route 实例化（`P6ANCH2`）；
* HI：`hpin`（owner：late K 数据，`P6S3` binder）；
* late-K records：`recordsK / hcanK / hacc / hm / hDm / hsepWK / hT₀`（owner：
  `Dist/LateRecordsSupplyC11G` 与 `P6ANCH2` records 车道；`hsepWK` 阈值用 `3 / (r/100)²`）。
traced region 前提由 `SliceLocalization` 自己的量词给出（只在 driver 已控的有限 traced region 上）。
结论：`SliceLocalization_C11SH … (fun n => L n / 2)`（`L/4` 喂 producer，`Lsmall := L/2`）。
不含 `hscalU / hclosG / hclosC / hUVC / CanonicalLateCore / hspine`（审计文件对 producer 传递依赖做名字
扫描）。第二层（坏点短窗 closure）不在此。 -/
theorem sliceInput1_of_tracedCond_C11SW :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (_hjt : ∀ n, (K n).time (j n).castSucc < t n) (_htj : ∀ n, t n < (K n).time (j n).succ),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ n, (σ n : ℝ) ≤ t n) →
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) → (∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
    ObservedHistory.SliceLocalization_C11SH Kh Tn aSeed σ haT hsT has pT seedTrace y R
      (fun n => L n / 2) := by
  obtain ⟨ε₀, hε₀, hprod⟩ := hdistC_of_traced_anySeed_C11G3.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hσt hhalf htime hR hL hsmall
    hclock hRr a₀ ha₀ hpin q T₀ recordsK hcanK hacc hm hDm hsepWK hT₀
  refine ObservedHistory.sliceLocalization_of_hdistC_half_C11SW hR hL ?_
  intro φ hφ D T Kc hD hT hKc htr
  exact hprod K j t hjt htj σ y R r (fun n => L n / 4) Tn aSeed haT hsT has pT seedTrace hσt hhalf
    htime hR (hL.atTop_div_const (by norm_num)) hsmall hclock hRr ha₀ hpin q T₀ recordsK hcanK
    hacc hm hDm hsepWK hT₀ φ hφ D T Kc hD hT hKc htr

end ProducerWire


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

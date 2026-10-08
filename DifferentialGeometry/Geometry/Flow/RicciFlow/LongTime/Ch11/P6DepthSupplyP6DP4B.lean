import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HclosGFirstExitP6M4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BcadSliceP6M2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorSecondP6AN2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# 重索引列上的无条件距离槽：`hdistW` 与无条件 `hdistC`（O-CH11-DEPTH4B，后缀 `_P6DP4B`；设计 §7 (i) / §8 期 4 后半）

caller（hPN / kernel 帧）跑完 maximal-depth driver 得 `ψ` 与 `∀ T > 0, DepthExtendable Kh σ y R ψ T` 后，
kernel body 的无条件距离槽在重索引族 `· ∘ ψ` 上的付法（DEPTH3 §5 两行模式）：
* (1) `hdistC_uncond_of_depthExt_P6DP4B`：FinalBody:323 无条件距离槽（= P6M2 / P6S3 `hdistQ` 体逐字，余量 `L/4`）
  ⇐ NotKBody:132 条件形 `hdistC` + `hext`；深度取 `T` 本身，半径 `A := 2·D`。
* (2) `hdistW_of_depthExt_P6DP4B`：NotKBody:149 `hdistW` 体逐字 ⇐ (1) + `hL`（`L/4 ≤ L`；不用同 stage 前提）。
* (1′) / (2′) `ψ := id` 形 + `depthExt_reindex_P6DP4B`（driver 输出 ⇒ 重索引族上的 `DepthExtendable(id)`）。
* 索引条款引理：`hRlt` / `hacc` / `hδF` / `hrad` / `hord` / `hscaleK` / `∀ᶠ` / `Tendsto` 在 `ψ k ≥ k` 下保持
  （复用树内 `natCast_le_strictMono_P6AN2`）。
* G2 example：NotKBody `hdistW` 槽、FinalBody:323 槽、（附）NotKBody 条件 `hdistC` 槽在重索引族上；P6M2 实喂。
与 DEPTH3 E4 / E4F（`hclosG` / `hclosGF`）合起来 = §7 (i) 全部无条件距离槽的 caller 供给形。不写"端点已闭"。
生成器 `build-logs/scratch/O-CH11-DEPTH4B/gen/gen.py`（tracked 源逐字切片 + assert 替换）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **(1) 无条件 `hdistC` 在 driver 子列上（`_P6DP4B`）**：NotKBody:132 条件形 `hdistC`（余量 `L/4`，
traced `(2D, T, Kc)` 沿子列 `φ`）+ driver 输出 `hext : ∀ T > 0, DepthExtendable Kh σ y R ψ T` ⇒
FinalBody:323 无条件距离槽体逐字（= P6M2 / P6S3 的 `hdistQ` 体），只把 `atTop` 换成 `map ψ atTop`。
取法（DEPTH3 §5 两行模式）：深度就取 `T` 本身，半径 `A := 2·D` 喂 `DepthExtendable` 得 `Kc ≥ 0`，
即 `hdistC` 在 `φ := ψ` 处的 traced 前提（`Filter.eventually_map` 为 `Iff.rfl`）。 -/
theorem ObservedHistory.hdistC_uncond_of_depthExt_P6DP4B (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R ψ T) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in map ψ atTop,
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  intro D T hD hT
  obtain ⟨Kc, hKc, hev⟩ := hext T hT (2 * D) (by positivity)
  exact hdistC ψ hψ D T Kc hD hT hKc hev

/-- **(2) NotKBody `hdistW`（∀ D T 同 slab）在 driver 子列上（`_P6DP4B`）**：NotKBody:149 体逐字，
`atTop` → `map ψ atTop`。由 (1) 得到，只做两步：(i) 余量 `L/4 ≤ L`（eventually `0 ≤ L`，⇐ `hL`）；
(ii) 不用前提 `activeStage v = activeStage σ`。(ii) 合法：hdistW 体里这个条件只是**额外前提**
（限制 `v` 在同 slab），(1) 的结论对所有 `v ∈ [σ − T/R, σ]`、不论 stage 都成立，丢掉它是用更强的 ∀ 形
覆盖更弱的结论，不改任何量。 -/
theorem ObservedHistory.hdistW_of_depthExt_P6DP4B (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R ψ T) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in map ψ atTop,
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
  intro D T hD hT
  filter_upwards [ObservedHistory.hdistC_uncond_of_depthExt_P6DP4B Kh Tn aSeed σ haT hsT has pT
      seedTrace y R L hdistC ψ hψ hext D T hD hT,
    (hL.eventually_ge_atTop 0).filter_mono hψ.tendsto_atTop] with n hn hL0
  intro x hx v hav hvs hvT _hst tr
  refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- **(1′) 重索引族上的形（`ψ := id`）**：族本身已是 `· ∘ ψ` 时（`depthExt_reindex_P6DP4B` 把 driver 输出
变成 `DepthExtendable(id)`），结论直接是 FinalBody:323 / P6M2 `hdistQ` 体逐字（`∀ᶠ n in atTop`）。 -/
theorem ObservedHistory.hdistC_uncond_of_depthExt_id_P6DP4B (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R id T) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  intro D T hD hT
  obtain ⟨Kc, hKc, hev⟩ := hext T hT (2 * D) (by positivity)
  exact hdistC id strictMono_id D T Kc hD hT hKc hev

/-- **(2′) `hdistW` 的 `ψ := id` 形**：NotKBody:149 体逐字（`∀ᶠ n in atTop`），由 (1′) 同 (2) 两步。 -/
theorem ObservedHistory.hdistW_of_depthExt_id_P6DP4B (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R id T) :
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
  intro D T hD hT
  filter_upwards [ObservedHistory.hdistC_uncond_of_depthExt_id_P6DP4B Kh Tn aSeed σ haT hsT has pT
      seedTrace y R L hdistC hext D T hD hT, hL.eventually_ge_atTop 0] with n hn hL0
  intro x hx v hav hvs hvT _hst tr
  refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- **driver 输出 ⇒ 重索引族上的 `DepthExtendable(id)`（`_P6DP4B`）**：定义展开（`(Kh ∘ ψ) (id i) = Kh (ψ i)`）。 -/
theorem ObservedHistory.depthExt_reindex_P6DP4B (Kh : ℕ → ObservedHistory.{u})
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ)
    (ψ : ℕ → ℕ) {T : ℝ} (h : ObservedHistory.DepthExtendable Kh σ y R ψ T) :
    ObservedHistory.DepthExtendable (fun i => Kh (ψ i)) (fun i => σ (ψ i)) (fun i => y (ψ i))
      (fun i => R (ψ i)) id T :=
  fun A hA => h A hA

/-! ### 索引条款在 `ψ k ≥ k` 下保持（`natCast_le_strictMono_P6AN2` = `n ≤ ψ n` 的实数形，树内复用） -/

/-- 基本不等式：`i + 1 ≤ ψ i + 1`（实数）。 -/
theorem succ_le_succ_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (i : ℕ) :
    (i : ℝ) + 1 ≤ (ψ i : ℝ) + 1 := by
  have := ObservedHistory.natCast_le_strictMono_P6AN2 hψ i
  linarith

/-- `hRlt` 型：`n + 1 < R n` ⇒ `i + 1 < R (ψ i)`。 -/
theorem succ_lt_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {R : ℕ → ℝ}
    (h : ∀ n : ℕ, (n : ℝ) + 1 < R n) : ∀ i : ℕ, (i : ℝ) + 1 < R (ψ i) := fun i =>
  (succ_le_succ_comp_P6DP4B hψ i).trans_lt (h (ψ i))

/-- `hacc` / `hδF` 型：`a n ≤ 1 / (n + 1)` ⇒ `a (ψ i) ≤ 1 / (i + 1)`。 -/
theorem le_one_div_succ_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {a : ℕ → ℝ}
    (h : ∀ n : ℕ, a n ≤ 1 / ((n : ℝ) + 1)) : ∀ i : ℕ, a (ψ i) ≤ 1 / ((i : ℝ) + 1) := fun i =>
  (h (ψ i)).trans (one_div_le_one_div_of_le (by positivity)
    (succ_le_succ_comp_P6DP4B hψ i))

/-- `hrad` 型：`n + 1 ≤ a n` ⇒ `i + 1 ≤ a (ψ i)`。 -/
theorem succ_le_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {a : ℕ → ℝ}
    (h : ∀ n : ℕ, (n : ℝ) + 1 ≤ a n) : ∀ i : ℕ, (i : ℝ) + 1 ≤ a (ψ i) := fun i =>
  (succ_le_succ_comp_P6DP4B hψ i).trans (h (ψ i))

/-- `hord` 型（ℕ）：`n + 2 ≤ m n` ⇒ `i + 2 ≤ m (ψ i)`。 -/
theorem add_two_le_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {m : ℕ → ℕ}
    (h : ∀ n : ℕ, n + 2 ≤ m n) : ∀ i : ℕ, i + 2 ≤ m (ψ i) := fun i =>
  (Nat.add_le_add_right (hψ.id_le i) 2).trans (h (ψ i))

/-- `hscaleK` 的因子单调：`(i+1)·max(i+1, q) ≤ (ψ i+1)·max(ψ i+1, q)`。 -/
theorem succ_mul_max_le_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (i : ℕ) (q : ℝ) :
    ((i : ℝ) + 1) * max ((i : ℝ) + 1) q ≤ ((ψ i : ℝ) + 1) * max ((ψ i : ℝ) + 1) q := by
  have h1 : (i : ℝ) + 1 ≤ (ψ i : ℝ) + 1 := succ_le_succ_comp_P6DP4B hψ i
  have h0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  exact mul_le_mul h1 (max_le_max h1 le_rfl) (h0.trans (le_max_left _ _)) (h0.trans h1)

/-- `hscaleK` 型：`(n+1)·max(n+1, Q n) ≤ s n` ⇒ `(i+1)·max(i+1, Q (ψ i)) ≤ s (ψ i)`。 -/
theorem scaleK_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {Q s : ℕ → ℝ}
    (h : ∀ n : ℕ, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤ s n) :
    ∀ i : ℕ, ((i : ℝ) + 1) * max ((i : ℝ) + 1) (Q (ψ i)) ≤ s (ψ i) := fun i =>
  (succ_mul_max_le_comp_P6DP4B hψ i (Q (ψ i))).trans (h (ψ i))

/-- `∀ᶠ` 型条款（`hbirthA`、`hdistσ`、`hT₀ B`、`hwin T` 等）沿 `ψ` 搬运。 -/
theorem eventually_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {P : ℕ → Prop}
    (h : ∀ᶠ n in atTop, P n) : ∀ᶠ i in atTop, P (ψ i) :=
  hψ.tendsto_atTop.eventually h

/-- `Tendsto … atTop atTop` 型条款（`hL`、`hρV`、`hRt`）沿 `ψ` 搬运。 -/
theorem tendsto_comp_P6DP4B {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {f : ℕ → ℝ}
    (h : Tendsto f atTop atTop) : Tendsto (fun i => f (ψ i)) atTop atTop :=
  h.comp hψ.tendsto_atTop

/-- **G2 (a) NotKBody `hdistW` 槽在重索引族上**：NotKBody:149 体逐字写成对族数据的 λ，作用在
`(Kh, Tn, aSeed, σ, …, R, L) ∘ ψ` 上（期 5 把 body 用到重索引序列时 `hdistW` 槽的付法），由 (2) 直接付。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R ψ T) :
    (fun (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
        (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
        (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) =>
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
            ENNReal.ofReal (L n / Real.sqrt (R n)))
      (fun i => Kh (ψ i)) (fun i => Tn (ψ i)) (fun i => aSeed (ψ i)) (fun i => σ (ψ i))
      (fun i => haT (ψ i)) (fun i => hsT (ψ i)) (fun i => has (ψ i)) (fun i => pT (ψ i))
      (fun i => seedTrace (ψ i)) (fun i => y (ψ i)) (fun i => R (ψ i)) (fun i => L (ψ i)) := by
  beta_reduce
  intro D T hD hT
  exact ObservedHistory.hdistW_of_depthExt_P6DP4B Kh Tn aSeed σ haT hsT has pT seedTrace y R L hL
    hdistC ψ hψ hext D T hD hT

/-- **G2 (b) FinalBody:323 无条件距离槽（= 无条件 `hdistC`）在重索引族上**：由 (1) 直接付。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R ψ T) :
    (fun (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
        (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
        (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) =>
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
      (fun i => Kh (ψ i)) (fun i => Tn (ψ i)) (fun i => aSeed (ψ i)) (fun i => σ (ψ i))
      (fun i => haT (ψ i)) (fun i => hsT (ψ i)) (fun i => has (ψ i)) (fun i => pT (ψ i))
      (fun i => seedTrace (ψ i)) (fun i => y (ψ i)) (fun i => R (ψ i)) (fun i => L (ψ i)) := by
  beta_reduce
  intro D T hD hT
  exact ObservedHistory.hdistC_uncond_of_depthExt_P6DP4B Kh Tn aSeed σ haT hsT has pT seedTrace y R
    L hdistC ψ hψ hext D T hD hT

/-- **G2 (c)（附）NotKBody 条件形 `hdistC` 槽在重索引族上**：原 `hdistC` 取子列 `ψ ∘ φ`；不需要
`DepthExtendable`（条件形对子列遗传）。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    (fun (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
        (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
        (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) =>
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
      (fun i => Kh (ψ i)) (fun i => Tn (ψ i)) (fun i => aSeed (ψ i)) (fun i => σ (ψ i))
      (fun i => haT (ψ i)) (fun i => hsT (ψ i)) (fun i => has (ψ i)) (fun i => pT (ψ i))
      (fun i => seedTrace (ψ i)) (fun i => y (ψ i)) (fun i => R (ψ i)) (fun i => L (ψ i)) := by
  beta_reduce
  intro φ hφ D T Kc hD hT hKc htr
  exact hdistC (ψ ∘ φ) (hψ.comp hφ) D T Kc hD hT hKc htr

/-- **G2 (d) P6M2 实喂**：`hbcad_of_slice_data_P6M2` 的无条件 `hdistQ`（体 = FinalBody:323 逐字）由
(1′) 付；族取重索引族时 `hext` = `depthExt_reindex_P6DP4B` 作用于 driver 输出。其余前提逐字原样。 -/
example
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {D qcan : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)}
    (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscaleK : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale)
    (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount))
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x)
    (hlow0 : ∀ n x, -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n) (hqR : ∀ n, qcan n ≤ R n)
    (hRt : Tendsto (fun n => R n * σ n) atTop atTop)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hext : ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R id T)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hUV : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            4 * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            4 * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                Cgrad * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
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
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  have hdistQ := ObservedHistory.hdistC_uncond_of_depthExt_id_P6DP4B Kh Tn aSeed σ haT hsT has pT
    seedTrace y R L hdistC hext
  exact ObservedHistory.hbcad_of_slice_data_P6M2 hεle hκ hphi htj hrecK hqcan hpar hscaleK hpinchK0
    hslabK ha₀ hHI0 hlow0 Kh hKh σ y R hσ hRpos hqR hRt Tn aSeed haT hsT has pT seedTrace L hL hwin
    hdistQ ρV hρV hUV

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6B

/-!
# 种子的半深度回推（带 trace 数据的版本；S-CH11-HDISTC G1，后缀 `_C11G3`）

树内 `earlier_seed_on_half_depth_P6B`（`P6SeedShiftP6B`）：种子 `(p, T, r)` 在 `v ∈ [T − r²/2, T]` 给出以种子
trace 点 `O_v` 为中心、半径 `R = r/100` 的种子（`hasSmallParabolicCurvature` + 体积 `A⁻¹e⁻⁵⁷/512` + `2R² < v`）。
K-route 的消费端（`hdist` / `hgeom` 的 `seedTrace`、`aSeed` 时钟 `aSeed = Tn − r²`）要的是**完整的种子数据**：
新时钟 `a' = v − R²` 与新的 backward trace（`a'` → `v`，终点 `O_v`）。本文件补这两样：
* `earlier_seed_on_half_depth_C11G3`：新种子 `(v, O_v, R = r/100)` + 新时钟 `a' = v − R²`（`aSeed ≤ a'`）
  + 新 trace `seedTrace'`（`restrictFirst` 再 `restrictLast` 原 trace，**逐点相等**）+ P6B 的三条结论；
* `earlier_seed_small_on_half_depth_C11G3`：不要体积前提的版本（`A := 0`，`A⁻¹ = 0` 使体积前提平凡）——
  hgeom / hdist 的 K0 只吃 `hasSmallParabolicCurvature`，不要体积。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **半深度种子回推，带新时钟与新 trace（`_C11G3`）**：种子 `(p, T, r)`（时钟 `aSeed = T − r²`、
`2r² < T`、体积 `≥ A⁻¹ r³`、种子 trace）在 `v ∈ [T − r²/2, T]`（`aSeed ≤ v`）给出：新时钟 `a' = v − (r/100)²`
（`aSeed ≤ a' ≤ v`）、新 trace（`a'` → `v`，终点 `O_v := seedTrace.point v`，逐点等于原 trace）、
新种子 `hasSmallParabolicCurvature H v O_v (r/100)`、体积 `≥ (A⁻¹ e⁻⁵⁷/512)(r/100)³`、`2(r/100)² < v`。 -/
theorem earlier_seed_on_half_depth_C11G3
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r A : ℝ)
    (htime : 2 * r ^ 2 < (T : ℝ)) (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage T) T) p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    ∃ (a' : Icc (0 : ℝ) H.horizon) (haa' : aSeed ≤ a') (hav' : a' ≤ v)
      (seedTrace' : BackwardPointTrace H (H.activeStage a') (H.activeStage v)
        (H.activeStage_mono hav') O),
      (a' : ℝ) = (v : ℝ) - R ^ 2 ∧
      hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        ballVolume (H.stageMetric (H.activeStage v) v) O R ∧
      2 * R ^ 2 < (v : ℝ) ∧
      ∀ (u : Icc (0 : ℝ) H.horizon) (hau : a' ≤ u) (huv : u ≤ v),
        seedTrace'.point (H.activeStage u) (H.activeStage_mono hau) (H.activeStage_mono huv) =
          seedTrace.point (H.activeStage u) (H.activeStage_mono (haa'.trans hau))
            (H.activeStage_mono (huv.trans hvT)) := by
  intro O R
  have h : hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        ballVolume (H.stageMetric (H.activeStage v) v) O R ∧ 2 * R ^ 2 < (v : ℝ) :=
    earlier_seed_on_half_depth_P6B haT p r A htime hclock hseed hvolume seedTrace v hav hvT hv
  obtain ⟨hsmall, hvol, hR2⟩ := h
  have hr : 0 < r := hseed.1
  have hRsq : R ^ 2 = r ^ 2 / 10000 := by
    dsimp only [R]
    ring
  have hv0 : 0 ≤ (v : ℝ) - R ^ 2 := by
    have := sq_nonneg R
    linarith
  let a' : Icc (0 : ℝ) H.horizon :=
    ⟨(v : ℝ) - R ^ 2, hv0, (sub_le_self _ (sq_nonneg R)).trans v.2.2⟩
  have haa' : aSeed ≤ a' := by
    change (aSeed : ℝ) ≤ (v : ℝ) - R ^ 2
    rw [hclock, hRsq]
    nlinarith [sq_nonneg r]
  have hav' : a' ≤ v := sub_le_self _ (sq_nonneg R)
  exact ⟨a', haa', hav', (seedTrace.restrictFirst (H.activeStage_mono haa')
      (H.activeStage_mono (hav'.trans hvT))).restrictLast (H.activeStage_mono hav')
      (H.activeStage_mono hvT), rfl, hsmall, hvol, hR2, fun u hau huv => rfl⟩

/-- **体积无关版（`_C11G3`）**：`hasSmallParabolicCurvature` 种子的半深度回推（新时钟 / 新 trace / 种子
`(O_v, r/100)` / `2(r/100)² < v`），不要体积前提（取 `A := 0`，`0⁻¹ = 0` 使体积前提平凡）。 -/
theorem earlier_seed_small_on_half_depth_C11G3
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r : ℝ)
    (htime : 2 * r ^ 2 < (T : ℝ)) (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    ∃ (a' : Icc (0 : ℝ) H.horizon) (haa' : aSeed ≤ a') (hav' : a' ≤ v)
      (seedTrace' : BackwardPointTrace H (H.activeStage a') (H.activeStage v)
        (H.activeStage_mono hav') O),
      (a' : ℝ) = (v : ℝ) - R ^ 2 ∧ hasSmallParabolicCurvature H v O R ∧
      2 * R ^ 2 < (v : ℝ) ∧
      ∀ (u : Icc (0 : ℝ) H.horizon) (hau : a' ≤ u) (huv : u ≤ v),
        seedTrace'.point (H.activeStage u) (H.activeStage_mono hau) (H.activeStage_mono huv) =
          seedTrace.point (H.activeStage u) (H.activeStage_mono (haa'.trans hau))
            (H.activeStage_mono (huv.trans hvT)) := by
  intro O R
  obtain ⟨a', haa', hav', tr, hclk, hsmall, -, hR2, hpt⟩ :=
    earlier_seed_on_half_depth_C11G3 haT p r 0 htime hclock hseed (by simp) seedTrace v hav hvT hv
  exact ⟨a', haa', hav', tr, hclk, hsmall, hR2, hpt⟩

end GC.LongTime.Ch11

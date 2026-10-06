import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckMiddleSphereNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSliceBandNK

/-!
# Route W, c4 的 consumer：surgery 前 slice 的 IMS06′（S-W-NECK G5，后缀 `_NK`）

HT-L（左侧 K）需要的 IMS06′：对 `s ∈ [τ₀ - d, τ₀)`，slice `(H.stage i.castSucc).Carrier`、度量
`B.sliceMetric_NK s` 里，开盘内光滑、`q(∂D)` 与 band 闭包不交的盘 `q`（IMS05′ 作显式参数）
不碰 neck 的中间球面 `{height = 0}`。用 G5 的 `slice_band_estimates_half_NK` 实例化 G4 主定理
`not_mem_middle_sphere_of_stability_bound_NK`。
-/

set_option autoImplicit false

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

/-- **surgery 前 slice 的 IMS06′**。 -/
theorem not_mem_middle_sphere_of_slice_NK (B : IncomingBackwardNeck H i neck r)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      ∀ q : C(closedDisk, (H.stage i.castSucc).Carrier),
        DiskSmoothInterior (E := ThreeSpace) q →
        (∀ θ : loopCircle, diskTrace q θ ∉
          closure {p : (H.stage i.castSucc).Carrier |
            p ∈ Set.range B.sliceChart_NK ∧ |B.sliceHeight_NK p| < 20}) →
        (∀ (z₀ : ℂ) (ρ : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < ρ →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
            diskEDist_NK (B.sliceMetric_NK s) q z₀ z ≤ ENNReal.ofReal ρ} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (B.sliceMetric_NK s) q z₀ z = ENNReal.ofReal ρ) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (B.sliceMetric_NK s) q z₀ z ≤ ENNReal.ofReal ρ →
            ∀ᶠ w in 𝓝 z, 1 / 2 ≤
              metricScalarAt (B.sliceMetric_NK s) (diskExtension q w)) →
          ρ ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) →
        ∀ ζ : closedDisk, ¬ (q ζ ∈ Set.range B.sliceChart_NK ∧ B.sliceHeight_NK (q ζ) = 0) := by
  obtain ⟨d, hd, h⟩ := B.slice_band_estimates_half_NK hk hδ
  refine ⟨d, hd, fun s hs1 hs2 q hq htrace hIMS05 => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h s hs1 hs2
  exact not_mem_middle_sphere_of_stability_bound_NK (B.sliceMetric_NK s) hq h1
    (h2.of_le (by exact_mod_cast le_top)) h3 h5 h4 htrace hIMS05

end GC.LongTime

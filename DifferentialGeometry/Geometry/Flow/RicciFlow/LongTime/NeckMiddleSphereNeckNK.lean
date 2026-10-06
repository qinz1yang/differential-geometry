import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckMiddleSphereNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBandEstimatesNK

/-!
# Route W, IMS06′ 对 `NormalizedNeck` 的实例（S-W-NECK G4 的 consumer，后缀 `_NK`）

G2 的 `NormalizedNeck.band_estimates_NK` 给出 G4 对 `(N, Z, g)` 的全部假设，所以对一个
`k ≥ 2`、`δ ≤ 1/8646` 的 `NormalizedNeck`，IMS06′ 的结论（design §B.4 的形状）：
`q` 不碰 neck 的中间球面 `{x ∈ range chart | height x = 0}`。度量取 scalar-one 归一化
`scaleMetric N.scale h`；IMS05′（`σ = 1/2`）仍是显式参数。
-/

set_option autoImplicit false

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

omit [SigmaCompactSpace M] in
/-- **IMS06′ for a `NormalizedNeck`**：`q` 在开盘内光滑、`q(∂D)` 与 band `{|z| < 20}` 的闭包不交，
IMS05′（σ = 1/2，显式参数）⇒ `q` 不碰中间球面 `{height = 0}`。 -/
theorem not_mem_middle_sphere_of_normalizedNeck_NK (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    (hδ : δ ≤ 1 / 8646) {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := ThreeSpace) q)
    (htrace : ∀ θ : loopCircle, diskTrace q θ ∉
      closure {p : M | p ∈ Set.range (N.chart : neckBuffer δ → M) ∧ |N.height_NK p| < 20})
    (hIMS05 : ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK (scaleMetric N.scale N.scale_pos h) q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1,
        diskEDist_NK (scaleMetric N.scale N.scale_pos h) q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        diskEDist_NK (scaleMetric N.scale N.scale_pos h) q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, 1 / 2 ≤
          metricScalarAt (scaleMetric N.scale N.scale_pos h) (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) :
    ∀ ζ : closedDisk, ¬ (q ζ ∈ Set.range (N.chart : neckBuffer δ → M) ∧
      N.height_NK (q ζ) = 0) := by
  obtain ⟨hopen, hsm, hcl, hR, hdz⟩ := N.band_estimates_NK hk hδ
  exact not_mem_middle_sphere_of_stability_bound_NK (scaleMetric N.scale N.scale_pos h) hq
    hopen (hsm.of_le (by exact_mod_cast le_top)) hcl hdz hR htrace hIMS05

end GC.LongTime

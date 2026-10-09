import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.DiskDistGeoMinBridgeIM6
import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.StabilityRadiusSphereGM

/-!
# c3 收缩：IMS05′ 曲面层（O-W-GEO-MIN，已交付）接到 `d_q`（O-W-IMS06 G5，后缀 `_IM6`）

O-W-GEO-MIN `radius_le_of_sphere_GM`（给定 `u`）+ 本车道 G4 的 d-接口桥接 ⇒ S-W-NECK G4 的 `hIMS05`。
G1/G4 的整块前提 `hlam`/`hGM` 收缩为 **`hU`**：只剩 c3 的 (2)(3)——在包含闭内蕴球
`B̄ = {z ∈ ball | d_q(z₀, z) ≤ r}` 的开集 `Ω ⊆ ball` 上，正光滑 `u`（S-W-EIG G2 的第一特征函数）、
连续势 `qq`、`μ ≥ 0`，满足 B̄ 上 `qq ≥ σ/2`（(2)：Gauss 方程，S-W-STAB G3 的 `VJ = K_Σ − q̃ ≤ K_Σ − R/2`）
与 B̄ 上 `Δ₀u = lam (K_Σ − qq − μ) u`（`K_Σ = −Δ log lam / (2 lam)`）。`lam` 的光滑性与正性、
`d` 的连续性与线段界都已在 G4 证出（`himm`：K16b 的内部浸入）。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **c3（收缩版）**：开盘内光滑、共形、浸入的盘 `q` + `hU`（`u`、`qq`、`μ` 的存在，B̄ 上
`qq ≥ σ/2` 与特征方程）⇒ S-W-NECK G4 的 `hIMS05`（`σ` 版，`d_q = diskEDist_NK g q z₀`）。 -/
theorem ims05_radius_bound_of_eigen_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    (himm : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {σ : ℝ} (hσ : 0 < σ)
    (hU : ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      ∃ (Ω : Set ℂ) (u qq : ℂ → ℝ) (μ : ℝ), IsOpen Ω ∧ Ω ⊆ Metric.ball (0 : ℂ) 1 ∧
        {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} ⊆ Ω ∧
        ContDiffOn ℝ ∞ u Ω ∧ (∀ z ∈ Ω, 0 < u z) ∧ ContinuousOn qq Ω ∧ 0 ≤ μ ∧
        (∀ z ∈ Ω, (diskEDist_NK g q z₀ z).toReal ≤ r → σ / 2 ≤ qq z) ∧
        ∀ z ∈ Ω, (diskEDist_NK g q z₀ z).toReal ≤ r →
          Laplacian.laplacian u z = diskConformalFactor_IM6 g q z *
            (-Laplacian.laplacian (fun p => Real.log (diskConformalFactor_IM6 g q p)) z /
              (2 * diskConformalFactor_IM6 g q z) - qq z - μ) * u z) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  intro z₀ r h₀ hr hK _ hR
  obtain ⟨Ω, u, qq, μ, hΩ, hΩb, hBΩ, hu, hu0, hqq, hμ, hqσ, hpde⟩ := hU z₀ r h₀ hr hK hR
  have hiff : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      (diskEDist_NK g q z₀ z).toReal ≤ r ↔ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r :=
    fun z hz => (ENNReal.le_ofReal_iff_toReal_le (diskEDist_ne_top_IM6 g hq h₀ hz) hr.le).symm
  have hself : diskEDist_NK g q z₀ z₀ = 0 := diskEDist_self_NK g q h₀
  have hz₀Ω : z₀ ∈ Ω := hBΩ ⟨h₀, by rw [hself]; exact zero_le⟩
  have hset : {z : ℂ | z ∈ Ω ∧ (diskEDist_NK g q z₀ z).toReal ≤ r} =
      {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} := by
    ext z
    constructor
    · rintro ⟨hzΩ, hd⟩
      exact ⟨hΩb hzΩ, (hiff z (hΩb hzΩ)).mp hd⟩
    · rintro ⟨hzb, hd⟩
      exact ⟨hBΩ ⟨hzb, hd⟩, (hiff z hzb).mpr hd⟩
  refine radius_le_of_sphere_GM hΩ ((contDiffOn_diskConformalFactor_IM6 g hq).mono hΩb) hu
    (fun z hz => diskConformalFactor_pos_IM6 g (himm z (hΩb hz))) hu0 hqq hσ hμ
    ((continuousOn_diskEDist_toReal_IM6 g hq h₀).mono hΩb)
    (fun x y hxy => diskEDist_toReal_le_add_IM6 g hq hconf h₀ (hxy.trans hΩb)) hz₀Ω ?_ hr
    (hset ▸ hK) hqσ hpde
  rw [hself]
  rfl

end GC.LongTime

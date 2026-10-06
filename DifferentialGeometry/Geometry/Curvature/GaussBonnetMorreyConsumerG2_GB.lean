import DifferentialGeometry.Geometry.Curvature.GaussBonnetMorrey_GB

set_option autoImplicit false

/-!
# G2 consumer（S-A10-GAUSS，后缀 `_GB`）

用 `IsMorreyDisk.two_pi_le_integral_sectionalDensity_add_boundary_of_area_pos_GB` 的小定理：
`−∫ sec·a ≤ −2π + ∫ k_g dℓ`（IMS09 里 `−∫(R/2 + sec)` 的 sec 部分，G3 直接用这个方向）。
-/

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem IsMorreyDisk.neg_integral_sectionalDensity_le_GB
    [CompactSpace M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ₀ : freeLoop M} {u : C(closedDisk, M)}
    (hM : IsMorreyDisk g γ₀ u) {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (hA : 0 < riemannianDiskArea g u)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    -(∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) ≤
      -(2 * Real.pi) + ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity g U γ φ θ := by
  have h := hM.two_pi_le_integral_sectionalDensity_add_boundary_of_area_pos_GB hU hA hγ hi hφ hm
    htrace
  linarith

end DifferentialGeometry.Geometry

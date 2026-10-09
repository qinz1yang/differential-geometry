import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamNormalCompetitorWS
import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaSmoothAT
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryRegularity

/-!
# S-W-STAB G1 consumer：`IsMorreyDisk` 版 `area_variation_nonneg_WS`

`hmin` 不再是参数：Morrey disk `u` 的面积等于 `morreyLeastAreaS g W γ`
（`IsMorreyDisk.area_eq_morreyLeastAreaS`，S-A08-ATTAIN G1″），而 `morreyLeastAreaS_le` 给出
光滑竞争者类里的 `≤`。`hExt : SmoothDiskExtension u U` 由 `IsMorreyDisk.exists_smooth_extension` 提供。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Morrey disk 沿 `N`（regular part）上 `φ ∈ C_c^∞(N)` 的 parametrized 法向 geodesic 变分：
面积的二阶变分非负（密度二阶导在 `K = tsupport φ` 上的积分 `≥ 0`，一阶 `= 0`）。 -/
theorem IsMorreyDisk.area_variation_nonneg_WS [T3Space M] (hdim : Module.finrank ℝ E = 3)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hi : ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ (F : ℝ × ℂ → M) (V : Set (ℝ × ℂ)), IsOpen V ∧ (∀ z ∈ N, ((0 : ℝ), z) ∈ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V ∧ (∀ z ∈ N, F (0, z) = U z) ∧
      (∫ z in Subtype.val '' tsupport φ,
        deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z) 0 = 0) ∧
      0 ≤ ∫ z in Subtype.val '' tsupport φ,
        deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0 := by
  have hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W →
        riemannianDiskArea g u ≤ riemannianDiskArea g v := by
    intro v hv hw hWv
    rw [hu.area_eq_morreyLeastAreaS hdim hγ hW]
    exact morreyLeastAreaS_le g hv hw hWv
  obtain ⟨F, V, hV, h0V, hF, hF0, -, -, -, -, -, h3, h4⟩ :=
    DifferentialGeometry.Geometry.area_variation_nonneg_WS hdim g W γ hExt hW hu.trace hmin
      N hNball hi hint ν hν φ hφ hφc
  exact ⟨F, V, hV, h0V, hF, hF0, h3, h4⟩

end DifferentialGeometry.Geometry

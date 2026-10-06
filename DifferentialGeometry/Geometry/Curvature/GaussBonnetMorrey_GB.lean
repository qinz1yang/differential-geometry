import DifferentialGeometry.Geometry.Curvature.DiskCurvatureInequality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

set_option autoImplicit false

/-!
# IMS09：Morrey 盘的 Gauss–Bonnet 不等式（车道 S-A10-GAUSS，G2，后缀 `_GB`）

树里的 `SmoothDiskExtension.curvature_inequality`（`Curvature/DiskCurvatureInequality.lean:31`）给出
`2π ≤ ∫ sec(TΣ)·a + ∫ diskMapTraceBoundaryDensity`（含 branch points；右端的 `sec·a` 已经吸收了
Gauss 不等式 `K_Σ·a ≤ sec·a`）。这里把它包成 Morrey 盘（`IsMorreyDisk`，A08/IMS03 的盘类）版本：
共形 / 调和由 `IsMorreyDisk.conformal_of_extension_closedBall` /
`IsMorreyDisk.tension_eq_zero_of_extension` 提供，并给 `0 < Area ⇒ 非常值` 的小引理。

**与简报的偏差**：简报里的名字 `integral_gaussCurvature_add_boundary_eq_two_pi_GB` 是等式；
对有 branch point 的 Morrey 盘等式不成立（`= 2π(1+Σm) ≥ 2π`），IMS09 只用 `≥`，所以这里是
`two_pi_le_…`。
-/

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- 面积 `> 0` ⇒ 盘不是常值（`curvature_inequality` 的 `hnon`）。 -/
theorem not_exists_const_of_riemannianDiskArea_pos_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)}
    (hA : 0 < riemannianDiskArea g u) : ¬ ∃ c : M, ∀ z : closedDisk, u z = c := by
  rintro ⟨c, hc⟩
  have hu : (u : closedDisk → M) = fun _ => c := funext hc
  rw [hu, riemannianDiskArea_const] at hA
  exact lt_irrefl 0 hA

/-- **IMS09 的 Gauss–Bonnet 部分（Morrey 盘版）**：`IsMorreyDisk g γ₀ u` 带光滑延拓 `U`，
非常值，边界 trace `U ∘ circleMap 0 1 = γ ∘ φ`（`γ` 光滑浸入曲线，`φ` 光滑单调）⇒
`2π ≤ ∫_D sec(TΣ)·a dz + ∫_{−π}^{π} k_g·√a dθ`（`diskMapTraceBoundaryDensity = k_g dℓ`）。 -/
theorem IsMorreyDisk.two_pi_le_integral_sectionalDensity_add_boundary_GB
    [CompactSpace M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ₀ : freeLoop M} {u : C(closedDisk, M)}
    (hM : IsMorreyDisk g γ₀ u) {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    2 * Real.pi ≤
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) +
      (∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity g U γ φ θ) :=
  hU.curvature_inequality g (hM.conformal_of_extension_closedBall hU)
    (fun q hq => hM.tension_eq_zero_of_extension hU q hq) hnon hγ hi hφ hm htrace

/-- 同上，`hnon` 换成 `0 < Area`（A08 的正性输出）。 -/
theorem IsMorreyDisk.two_pi_le_integral_sectionalDensity_add_boundary_of_area_pos_GB
    [CompactSpace M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ₀ : freeLoop M} {u : C(closedDisk, M)}
    (hM : IsMorreyDisk g γ₀ u) {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (hA : 0 < riemannianDiskArea g u)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    2 * Real.pi ≤
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) +
      (∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity g U γ φ θ) :=
  hM.two_pi_le_integral_sectionalDensity_add_boundary_GB hU
    (not_exists_const_of_riemannianDiskArea_pos_GB g hA) hγ hi hφ hm htrace

end DifferentialGeometry.Geometry

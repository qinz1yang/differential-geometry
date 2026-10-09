import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskFirstVariation
import DifferentialGeometry.Geometry.Metric.Family.Stationary

/-!
# G2（S-A10-DERIV）：`Ā(t) = Area_{G t}(Φ_t ∘ u)` 的 two-parameter derivative

固定 minimal disk `u`（conformal + harmonic w.r.t. `G t₀`），metric family `G`
（`MetricFamilySmoothOn D G`）与 isotopy family `Φ : ℝ → M ≃ₘ M`（jointly smooth，
`Φ t₀ = refl`）。已跟踪的 `SmoothDiskExtension.hasDerivAt_area_isotopy_flux`
（`DiskFirstVariation.lean`）已经给出 **joint** 导数
`metricTerm − fluxTerm`，所以这里不需要从两个单参数定理做 chain rule；本文件把结论
重新包装成 IMS09 的形状，并证明两个 partial derivative 的分解：

* `∂_G`：`t ↦ Area_{G t}(u)`（固定盘，metric variation 项 `m`），
* `∂_Φ`：`s ↦ Area_{G t₀}(Φ_s ∘ u)`（固定度量，isometric flux 项 `−f`），
* total：`t ↦ Area_{G t}(Φ_t ∘ u)` 的导数 `m − f`。

没有新 def / structure；`M` 紧、`E` 有限维（与已跟踪定理相同）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

/-- G2 主定理（two-parameter `HasDerivAt`）：`m` 为 metric variation 项
`∫_{closedBall} diskMapMetricVariationDensity G t₀ U`，`f` 为 boundary flux 项
`∫ θ, ⟨W, ν_in⟩ √λ`（`W` 为 `Φ` 在 `t₀` 的 velocity）。三个导数：固定盘的度量偏导、
固定度量的等距偏导、以及联合导数 `m − f`。 -/
theorem SmoothDiskExtension.hasDerivAt_area_two_parameter_DV
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension (G t₀) U z = 0) :
    let W := fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t₀ 1
    let b := fun θ => (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
        Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))
    let m := ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z
    let f := ∫ θ in -Real.pi..Real.pi, b θ
    HasDerivAt (fun t => riemannianDiskArea (G t) u) m t₀ ∧
      HasDerivAt (fun s => riemannianDiskArea (G t₀)
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(M, M)).comp u)) (-f) t₀ ∧
      HasDerivAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) (m - f) t₀ := by
  intro W b m f
  have h1 := (hu.hasDerivAt_area_metric hG ht₀ hconf).2
  have h3 := (hu.hasDerivAt_area_isotopy_flux hG ht₀ hT hT₀ hΦ hΦ₀ hconf hharm).2.2
  have hi : t₀ ∈ Ioo (t₀ - 1) (t₀ + 1) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - 1) (t₀ + 1) t₀ hi
  have hD' : D'.regular ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds hi
  have h2 := (hu.hasDerivAt_area_isotopy_flux (D := D') (G := fun _ => G t₀)
    (metricFamilySmoothOn_stationary (G t₀) D') hD' hT hT₀ hΦ hΦ₀ hconf hharm).2.2
  have hzero : (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapMetricVariationDensity (fun _ => G t₀) t₀ U z) = 0 := by
    simp [diskMapMetricVariationDensity]
  rw [hzero, zero_sub] at h2
  exact ⟨h1, h2, h3⟩

/-- 一般分析引理：`HasDerivAt f d t₀` 且 `d < b` ⇒ 右邻域上 `f s < f t₀ + b (s - t₀)`。 -/
theorem eventually_right_lt_of_hasDerivAt_lt_DV {f : ℝ → ℝ} {d b t₀ : ℝ}
    (hf : HasDerivAt f d t₀) (hdb : d < b) :
    ∀ᶠ s in 𝓝[>] t₀, f s < f t₀ + b * (s - t₀) := by
  have hlo := (hasDerivAt_iff_isLittleO.mp hf).def (show 0 < (b - d) / 2 by linarith)
  filter_upwards [nhdsWithin_le_nhds hlo, self_mem_nhdsWithin] with s hs hts
  have hts' : t₀ < s := hts
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_of_pos (sub_pos.mpr hts')] at hs
  have := (abs_le.mp hs).2
  nlinarith [sub_pos.mpr hts']

/-- G2 的 consumer：若 `m - f < b`，则 `Ā s = Area_{G s}(Φ_s ∘ u)` 在 `t₀` 右邻域上
有一阶上界 `Ā s < Ā t₀ + b (s - t₀)`（用到 G2 的 joint derivative 结论）。 -/
theorem SmoothDiskExtension.area_two_parameter_right_upper_DV
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension (G t₀) U z = 0) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∀ᶠ s in 𝓝[>] t₀, riemannianDiskArea (G s)
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(M, M)).comp u) <
      riemannianDiskArea (G t₀) ((⟨Φ t₀, (Φ t₀).contMDiff.continuous⟩ : C(M, M)).comp u) +
        b * (s - t₀) :=
  eventually_right_lt_of_hasDerivAt_lt_DV
    (hu.hasDerivAt_area_two_parameter_DV hG ht₀ hT hT₀ hΦ hΦ₀ hconf hharm).2.2 hb

end DifferentialGeometry.Geometry

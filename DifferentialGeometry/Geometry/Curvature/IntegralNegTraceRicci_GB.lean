import DifferentialGeometry.Geometry.Curvature.NegTraceRicci_GB
import DifferentialGeometry.Geometry.Curvature.GaussBonnetMorrey_GB

set_option autoImplicit false

/-!
# IMS09：极小盘上 `∫(−tr_Σ Ric) dA ≤ 3A/(4(t+c)) − 2π + ∫_∂Σ k_g dℓ`（车道 S-A10-GAUSS，G3，后缀 `_GB`）

合成 G1（`diskMap_neg_ricci_trace_eq_GB`：`−tr_Σ Ric·a = −(sec·a + R·a/2)`）、
G2（Gauss–Bonnet 不等式 `2π ≤ ∫ sec·a + ∫ k_g dℓ`）与 scalar lower bound `ρ ≤ R`：

* `integral_neg_trace_ricci_le_GB`：Ric 形式，`∫_D −(Ric(U_x,U_x)+Ric(U_y,U_y)) dz ≤
  −(ρ/2)·Area − 2π + ∫ diskMapTraceBoundaryDensity`。
* `integral_metricVariationDensity_le_GB` / `…_le_scalarShift_GB`：把积分的被积函数换成
  S-A10-DERIV 的 metricTerm 的密度 `diskMapMetricVariationDensity G t U z`（`∂_t g = −2 Ric`，
  `hderiv` 作显式参数，与 Ch.9 `TransportedAreaVariation` 同形），`ρ = −3/(2(t+c))` 时右端
  `= 3·Area/(4(t+c)) − 2π + ∫ k_g dℓ`。
* `IsMorreyDisk.…` 版本：共形 / 调和由 `IsMorreyDisk` 提供。

没有新增假设：`hdim`（`finrank E = 3`）、`curvature_inequality` 原有的 `hnon`/`htrace`/`γ`/`φ`，以及
`hρ`（scalar lower bound，来自 `AnalyticSurgeryProfile.scalar_lower`）、`hderiv`（Ricci flow 方程）。
-/

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

/-- **IMS09 的积分不等式（Ric 形式）**：dim 3，`u` 带光滑延拓 `U`（共形、调和、非常值、精确 trace
`U ∘ circleMap 0 1 = γ ∘ φ`），`ρ ≤ R(U z)` 在闭盘上 ⇒
`∫_D −(Ric(U_x,U_x)+Ric(U_y,U_y)) dz ≤ −(ρ/2)·Area − 2π + ∫_{−π}^{π} k_g·√a dθ`。 -/
theorem integral_neg_trace_ricci_le_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hdim : Module.finrank ℝ E = 3)
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U q = 0)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {ρ : ℝ} (hρ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ρ ≤ metricScalarAt (I := 𝓘(ℝ, E)) g (U z)) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
        -(ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
          ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z Complex.I)
            (diskMapPartial U z Complex.I))) ≤
      -(ρ / 2) * riemannianDiskArea g u - 2 * Real.pi +
        ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity g U γ φ θ := by
  have hgb := hu.curvature_inequality g hconf hharm hnon hγ hi hφ hm htrace
  obtain ⟨hUeq, N, hN, hDN, hUN⟩ := hu
  have hD : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
  have hsd : IntegrableOn (diskMapSectionalDensity g U) (Metric.closedBall (0 : ℂ) 1) :=
    integrableOn_diskMapSectionalDensity g hN hUN hD hDN hconf
  have hRc : Continuous (fun x : M => metricScalarAt (I := 𝓘(ℝ, E)) g x) :=
    (metricScalar_smooth (I := 𝓘(ℝ, E)) (M := M) g).continuous
  have hUc : ContinuousOn U N := hUN.continuousOn
  have hac : ContinuousOn (diskMapConformalCoefficient g U) N :=
    (contDiffOn_diskMapConformalCoefficient g hN hUN).continuousOn
  have hRa : IntegrableOn (fun z => metricScalarAt (I := 𝓘(ℝ, E)) g (U z) *
      diskMapConformalCoefficient g U z) (Metric.closedBall (0 : ℂ) 1) :=
    ((hRc.comp_continuousOn (hUc.mono hDN)).mul (hac.mono hDN)).integrableOn_compact hD
  have haint : IntegrableOn (diskMapConformalCoefficient g U) (Metric.closedBall (0 : ℂ) 1) :=
    (hac.mono hDN).integrableOn_compact hD
  have hArea : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapConformalCoefficient g U z) =
      riemannianDiskArea g u := by
    rw [riemannianDiskArea_eq_of_extension g u U hUeq, riemannianArea]
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    exact ((hconf z hz).areaDensity_eq_energy.trans (hconf z hz).coefficient_eq_energy.symm).symm
  have hT : (∫ z in Metric.closedBall (0 : ℂ) 1,
        -(ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
          ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z Complex.I)
            (diskMapPartial U z Complex.I))) =
      -((∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) +
        (∫ z in Metric.closedBall (0 : ℂ) 1, metricScalarAt (I := 𝓘(ℝ, E)) g (U z) *
          diskMapConformalCoefficient g U z) / 2) := by
    rw [setIntegral_congr_fun measurableSet_closedBall
      (fun z hz => diskMap_neg_ricci_trace_eq_GB g hdim (hconf z hz)) (g := fun z =>
        -(diskMapSectionalDensity g U z + metricScalarAt (I := 𝓘(ℝ, E)) g (U z) *
          diskMapConformalCoefficient g U z / 2))]
    rw [integral_neg, integral_add hsd (hRa.div_const 2), integral_div]
  have hmono : (∫ z in Metric.closedBall (0 : ℂ) 1, ρ * diskMapConformalCoefficient g U z) ≤
      ∫ z in Metric.closedBall (0 : ℂ) 1, metricScalarAt (I := 𝓘(ℝ, E)) g (U z) *
        diskMapConformalCoefficient g U z :=
    setIntegral_mono_on (haint.const_mul ρ) hRa measurableSet_closedBall
      (fun z hz => mul_le_mul_of_nonneg_right (hρ z hz) (diskMapConformalCoefficient_nonneg g U z))
  rw [integral_const_mul, hArea] at hmono
  rw [hT]
  linarith

/-- Ric 形式的最终版：`ρ = −3/(2(t+c))`，
`∫_D −tr_Σ Ric ≤ 3·Area/(4(t+c)) − 2π + ∫ k_g dℓ`（静态度量 `g`）。 -/
theorem integral_neg_trace_ricci_le_scalarShift_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {t c : ℝ} (hdim : Module.finrank ℝ E = 3)
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U q = 0)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    (hR : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) g (U z)) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
        -(ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
          ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z Complex.I)
            (diskMapPartial U z Complex.I))) ≤
      3 * riemannianDiskArea g u / (4 * (t + c)) - 2 * Real.pi +
        ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity g U γ φ θ := by
  have h := integral_neg_trace_ricci_le_GB g hdim hu hconf hharm hnon hγ hi hφ hm htrace hR
  have hcalc : -(-3 / (2 * (t + c)) / 2) * riemannianDiskArea g u =
      3 * riemannianDiskArea g u / (4 * (t + c)) := by
    by_cases hs : t + c = 0
    · simp [hs]
    · field_simp
      ring
  rw [hcalc] at h
  exact h

/-- **S-A10-DERIV 的 metricTerm 形式**：度量族 `G`（`∂_t G = −2 Ric(G t)` 在盘像点，`hderiv`），
被积函数是 `diskMapMetricVariationDensity G t U z`（`= ½(∂_t|U_x|² + ∂_t|U_y|²)`）：
`∫_D (metric variation density) ≤ −(ρ/2)·Area_{G t} − 2π + ∫ k_g dℓ`。 -/
theorem integral_metricVariationDensity_le_GB
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M) {t : ℝ} (hdim : Module.finrank ℝ E = 3)
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (G t) (U z) X Y) t)
    (hconf : ∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t) U q)
    (hharm : ∀ q ∈ Metric.ball (0 : ℂ) 1, diskMapTension (G t) U q = 0)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {ρ : ℝ}
    (hρ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ρ ≤ metricScalarAt (I := 𝓘(ℝ, E)) (G t) (U z)) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t U z) ≤
      -(ρ / 2) * riemannianDiskArea (G t) u - 2 * Real.pi +
        ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity (G t) U γ φ θ := by
  have h := integral_neg_trace_ricci_le_GB (G t) hdim hu hconf hharm hnon hγ hi hφ hm htrace hρ
  rw [setIntegral_congr_fun measurableSet_closedBall (fun z hz =>
    diskMapMetricVariationDensity_eq_neg_ricciTrace_of_hasDerivAt
      (Ric := fun y X Y => ricciTensor (I := 𝓘(ℝ, E)) (G t) y X Y) (hderiv z hz))]
  exact h

/-- **IMS09 的最终形式**：`ρ = −3/(2(t+c))`（`AnalyticSurgeryProfile.scalar_lower` 的 `c = scalarShift`），
`∫_D (metric variation density) ≤ 3·Area/(4(t+c)) − 2π + ∫ k_g dℓ`。 -/
theorem integral_metricVariationDensity_le_scalarShift_GB
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M) {t c : ℝ} (hdim : Module.finrank ℝ E = 3)
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (G t) (U z) X Y) t)
    (hconf : ∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t) U q)
    (hharm : ∀ q ∈ Metric.ball (0 : ℂ) 1, diskMapTension (G t) U q = 0)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    (hR : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) (G t) (U z)) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t U z) ≤
      3 * riemannianDiskArea (G t) u / (4 * (t + c)) - 2 * Real.pi +
        ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity (G t) U γ φ θ := by
  have h := integral_metricVariationDensity_le_GB G hdim hu hderiv hconf hharm hnon hγ hi hφ hm
    htrace hR
  have hcalc : -(-3 / (2 * (t + c)) / 2) * riemannianDiskArea (G t) u =
      3 * riemannianDiskArea (G t) u / (4 * (t + c)) := by
    by_cases hs : t + c = 0
    · simp [hs]
    · field_simp
      ring
  rw [hcalc] at h
  exact h

/-- Morrey 盘版：共形 / 调和来自 `IsMorreyDisk`，`hnon` 换成 `0 < Area`。 -/
theorem IsMorreyDisk.integral_metricVariationDensity_le_scalarShift_GB
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M) {t c : ℝ} (hdim : Module.finrank ℝ E = 3)
    {γ₀ : freeLoop M} {u : C(closedDisk, M)} (hM : IsMorreyDisk (G t) γ₀ u)
    {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (hA : 0 < riemannianDiskArea (G t) u)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (G t) (U z) X Y) t)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    (hR : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) (G t) (U z)) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t U z) ≤
      3 * riemannianDiskArea (G t) u / (4 * (t + c)) - 2 * Real.pi +
        ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity (G t) U γ φ θ :=
  DifferentialGeometry.Geometry.integral_metricVariationDensity_le_scalarShift_GB G hdim hU
    hderiv (hM.conformal_of_extension_closedBall hU) (hM.tension_eq_zero_of_extension hU)
    (not_exists_const_of_riemannianDiskArea_pos_GB (G t) hA) hγ hi hφ hm htrace hR

end DifferentialGeometry.Geometry

import DifferentialGeometry.Geometry.Curvature.IntegralNegTraceRicci_GB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility

set_option autoImplicit false

/-!
# G3 consumer（S-A10-GAUSS，后缀 `_GB`）

`AnalyticSurgeryProfile.scalar_lower`（`R ≥ −3/(2(t+scalarShift))` on `postStage F.observation t`）
直接喂给 `integral_neg_trace_ricci_le_scalarShift_GB`，得到 IMS09 的积分不等式
`∫_D −tr_Σ Ric ≤ 3·Area/(4(t+c)) − 2π + ∫ k_g dℓ`（度量 `postMetric F.observation t`）。
`postStage` 的 Carrier 是 compact（`OrientedThreeStage.compact`），`ThreeSpace` 的 `finrank = 3`，
所以 `CompactSpace M`、`hdim` 都是树里现成的；精确 trace `htrace` 与 `hnon` 留作显式参数
（由 A08 / Morrey disk 的 weak Jordan trace 经 reparametrization 提供）。
-/

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology ContDiff Bundle Manifold

namespace GC.LongTime

universe u

theorem AnalyticSurgeryProfile.integral_neg_trace_ricci_le_postMetric_GB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (H : AnalyticSurgeryProfile F δ) {t : ℝ} (ht : 0 ≤ t)
    {uD : C(closedDisk, (postStage F.observation t).Carrier)}
    {U : ℂ → (postStage F.observation t).Carrier}
    (hu : SmoothDiskExtension (E := ThreeSpace) uD U)
    (hconf : ∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (postMetric F.observation t) U q)
    (hharm : ∀ q ∈ Metric.ball (0 : ℂ) 1, diskMapTension (postMetric F.observation t) U q = 0)
    (hnon : ¬ ∃ c : (postStage F.observation t).Carrier, ∀ z : closedDisk, uD z = c)
    {γ : ℝ → (postStage F.observation t).Carrier}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ThreeSpace) ∞ γ)
    (hi : ∀ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ThreeSpace) γ s (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
        -(ricciTensor (I := 𝓘(ℝ, ThreeSpace)) (postMetric F.observation t) (U z)
            (diskMapPartial U z 1) (diskMapPartial U z 1) +
          ricciTensor (I := 𝓘(ℝ, ThreeSpace)) (postMetric F.observation t) (U z)
            (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I))) ≤
      3 * riemannianDiskArea (postMetric F.observation t) uD / (4 * (t + H.scalarShift)) -
        2 * Real.pi +
        ∫ θ in -Real.pi..Real.pi,
          diskMapTraceBoundaryDensity (postMetric F.observation t) U γ φ θ :=
  integral_neg_trace_ricci_le_scalarShift_GB (postMetric F.observation t)
    (by simp) hu hconf hharm hnon hγ hi hφ hm htrace
    (fun z _ => H.scalar_lower t ht (U z))

section MetricTermAlignment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 型对齐：S-A10-DERIV 用的 `hasDerivAt_integral_riemannianAreaDensity_metricFamily` 里的被积函数 `K`
（`mfderiv` 形式）与 `diskMapMetricVariationDensity`（`diskMapPartial` 形式）定义上相等，
所以 `integral_metricVariationDensity_le_GB` 的左端就是那个定理的 `∫ K`。 -/
example (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M) (t : ℝ) (U : ℂ → M) (z : ℂ) :
    ((deriv (fun r : ℝ => (G r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ))) t) +
        (deriv (fun r : ℝ => (G r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I)) t)) / 2 =
      diskMapMetricVariationDensity G t U z :=
  rfl

end MetricTermAlignment

end GC.LongTime

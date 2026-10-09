import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation
import DifferentialGeometry.Geometry.Metric.FamilyTimeBound
import DifferentialGeometry.Geometry.Measure.Area.MetricDensityError
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Mathlib.Analysis.Calculus.ParametricIntegral
import DifferentialGeometry.Analysis.Integration.Integral.ParametricDerivative



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem hasDerivAt_integral_diskMapAreaDensity_metric
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) t₀ := by
  let B := Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B := isCompact_closedBall _ _
  have hJ (t : ℝ) : ContinuousOn (riemannianAreaDensity (G t) U) s :=
    continuousOn_riemannianAreaDensity (G t) hs (hU.of_le (by simp))
  have hJ0 : IntegrableOn (riemannianAreaDensity (G t₀) U) B :=
    ((hJ t₀).mono hDs).integrableOn_compact hB
  have hder : ContinuousOn (diskMapMetricVariationDensity G t₀ U) B :=
    (contDiffOn_diskMapMetricVariationDensity hG ht₀ hs hU).continuousOn.mono hDs
  obtain ⟨r, K, hr, hK, _, hbounds, hLip⟩ := exists_metricFamily_quadratic_time_bounds hG ht₀
  let bound : ℂ → ℝ := fun z => 4 * K * riemannianAreaDensity (G t₀) U z
  have hbound : IntegrableOn bound B := hJ0.const_mul (4 * K)
  have hloc : ∀ z : ℂ,
      LipschitzOnWith (Real.nnabs (bound z)) (fun t => riemannianAreaDensity (G t) U z) (Metric.ball t₀ r) := by
    intro z
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs'
    have h := riemannianAreaDensity_metric_time_error (G t₀)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2) hK
      (fun t ht x v => (hbounds t ht x v).1) (fun t ht x v => (hbounds t ht x v).2)
      hLip ht hs' U z
    have hn : 0 ≤ bound z := mul_nonneg (mul_nonneg (by norm_num) hK)
      (riemannianAreaDensity_nonneg (G t₀) U z)
    have hecoef : K * 2 / (1 / 2 : ℝ) = 4 * K := by ring
    rw [hecoef] at h
    change |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G s) U z| ≤
      |bound z| * |t - s|
    rw [abs_of_nonneg hn]
    exact h
  exact hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict B)
    (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapMetricVariationDensity G t₀ U) (bound := bound)
    (Metric.ball_mem_nhds t₀ hr)
    (Eventually.of_forall (fun t => ((hJ t).mono hDs).aestronglyMeasurable hB.measurableSet))
    hJ0 (hder.aestronglyMeasurable hB.measurableSet)
    (Eventually.of_forall hloc) hbound
    ((ae_restrict_mem hB.measurableSet).mono
      (fun z hz => hasDerivAt_diskMapAreaDensity_metric hG ht₀ (hconf z hz)))



theorem SmoothDiskExtension.hasDerivAt_area_metric
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t) u)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  have h := hasDerivAt_integral_diskMapAreaDensity_metric hG ht₀ hs hU hDs hconf
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) := by
    funext t
    exact riemannianDiskArea_eq_of_extension (G t) u U heq
  rw [he]
  exact h.2

end DifferentialGeometry.Geometry

end

section

noncomputable section

open Set Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]

theorem hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (Icc a b ×ˢ univ))
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    IntegrableOn (diskMapMetricVariationWithinDensity G (Icc a b) t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivWithinAt
        (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z)
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationWithinDensity G (Icc a b) t₀ U z) (Icc a b) t₀ := by
  let B := Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B := isCompact_closedBall _ _
  have hJ (t : ℝ) : ContinuousOn (riemannianAreaDensity (G t) U) s :=
    continuousOn_riemannianAreaDensity (G t) hs (hU.of_le (by simp))
  have hJ0 : IntegrableOn (riemannianAreaDensity (G t₀) U) B :=
    ((hJ t₀).mono hDs).integrableOn_compact hB
  have hder : ContinuousOn (diskMapMetricVariationWithinDensity G (Icc a b) t₀ U) B :=
    (contDiffOn_diskMapMetricVariationWithinDensity hab ht₀ hG hs hU).continuousOn.mono hDs
  obtain ⟨r, K, hr, hK, hbounds, hLip⟩ := exists_quadratic_time_bounds_on_Icc hab ht₀ hG
  let bound : ℂ → ℝ := fun z => 4 * K * riemannianAreaDensity (G t₀) U z
  have hbound : IntegrableOn bound B := hJ0.const_mul (4 * K)
  have hloc : ∀ z : ℂ, LipschitzOnWith (Real.nnabs (bound z))
      (fun t => riemannianAreaDensity (G t) U z) (Icc a b ∩ Metric.ball t₀ r) := by
    intro z
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    have h := riemannianAreaDensity_metric_time_error (G t₀)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2) hK
      (fun t ht x v => (hbounds t ht x v).1) (fun t ht x v => (hbounds t ht x v).2)
      (fun t ht u hu x v => hLip t ht.1 u hu.1 x v) ht hu U z
    have hn : 0 ≤ bound z := mul_nonneg (mul_nonneg (by norm_num) hK)
      (riemannianAreaDensity_nonneg (G t₀) U z)
    have hecoef : K * 2 / (1 / 2 : ℝ) = 4 * K := by ring
    rw [hecoef] at h
    change |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G u) U z| ≤
      |bound z| * |t - u|
    rw [abs_of_nonneg hn]
    exact h
  exact Analysis.Calculus.hasDerivWithinAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict B) (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapMetricVariationWithinDensity G (Icc a b) t₀ U) (bound := bound)
    (uniqueDiffOn_Icc hab t₀ ht₀).accPt
    (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hr)))
    ⟨ht₀, Metric.mem_ball_self hr⟩
    (Eventually.of_forall (fun t => ((hJ t).mono hDs).aestronglyMeasurable hB.measurableSet))
    hJ0 (hder.aestronglyMeasurable hB.measurableSet)
    (Eventually.of_forall hloc) hbound
    ((ae_restrict_mem hB.measurableSet).mono
      (fun z hz => hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc hab ht₀ hG (hconf z hz)))


theorem SmoothDiskExtension.hasDerivWithinAt_area_metric_on_Icc
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (Icc a b ×ˢ univ))
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    IntegrableOn (diskMapMetricVariationWithinDensity G (Icc a b) t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivWithinAt (fun t => riemannianDiskArea (G t) u)
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationWithinDensity G (Icc a b) t₀ U z) (Icc a b) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  have h := hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc hab ht₀ hG hs hU hDs hconf
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) := by
    funext t
    exact riemannianDiskArea_eq_of_extension (G t) u U heq
  rw [he]
  exact h.2

end DifferentialGeometry.Geometry

end

end

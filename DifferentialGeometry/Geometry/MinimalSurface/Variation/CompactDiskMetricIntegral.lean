import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Measure.Area.LocalMetricComparison
import DifferentialGeometry.Geometry.Metric.Family.CompactTimeBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open Set Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

private theorem hasDerivAt_integral_diskMapAreaDensity_metric_of_compact_image
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
  have himage : IsCompact (U '' B) := hB.image_of_continuousOn (hU.continuousOn.mono hDs)
  have hJ (t : ℝ) : ContinuousOn (riemannianAreaDensity (G t) U) s :=
    continuousOn_riemannianAreaDensity (G t) hs (hU.of_le (by simp))
  have hJ0 : IntegrableOn (riemannianAreaDensity (G t₀) U) B :=
    ((hJ t₀).mono hDs).integrableOn_compact hB
  have hder : ContinuousOn (diskMapMetricVariationDensity G t₀ U) B :=
    (contDiffOn_diskMapMetricVariationDensity hG ht₀ hs hU).continuousOn.mono hDs
  obtain ⟨r, C, hr, hC, _, hbounds, hLip⟩ :=
    exists_metricFamily_quadratic_time_bounds_on_compact hG ht₀ himage
  let bound : ℂ → ℝ := fun z => 4 * C * riemannianAreaDensity (G t₀) U z
  have hbound : IntegrableOn bound B := hJ0.const_mul (4 * C)
  have hloc : ∀ z ∈ B,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun t => riemannianAreaDensity (G t) U z) (Metric.ball t₀ r) := by
    intro z hz
    have hzimage : U z ∈ U '' B := mem_image_of_mem U hz
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht q hq
    have hδ : 0 ≤ 2 * C * |t - q| := by positivity
    have hrel : ∀ v : TangentSpace 𝓘(ℝ, E) (U z),
        |(G t).inner (U z) v v - (G q).inner (U z) v v| ≤
          (2 * C * |t - q|) * (G q).inner (U z) v v := by
      intro v
      calc
        |(G t).inner (U z) v v - (G q).inner (U z) v v| ≤
            C * |t - q| * (G t₀).inner (U z) v v := hLip t ht q hq (U z) hzimage v
        _ = (2 * C * |t - q|) * ((1 / 2 : ℝ) * (G t₀).inner (U z) v v) := by ring
        _ ≤ (2 * C * |t - q|) * (G q).inner (U z) v v :=
          mul_le_mul_of_nonneg_left (hbounds q hq (U z) hzimage v).1 hδ
    have herr := riemannianAreaDensity_metric_relative_error_at (G q) (G t)
      (u := U) (z := z) hδ hrel
    have harea := riemannianAreaDensity_metric_upper_at (G t₀) (G q)
      (u := U) (z := z) (by norm_num : (0 : ℝ) < 2)
      (fun v => (hbounds q hq (U z) hzimage v).2)
    have hmajor : |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G q) U z| ≤
        bound z * |t - q| := by
      calc
        _ ≤ (2 * C * |t - q|) * riemannianAreaDensity (G q) U z := herr
        _ ≤ (2 * C * |t - q|) * (2 * riemannianAreaDensity (G t₀) U z) :=
          mul_le_mul_of_nonneg_left harea hδ
        _ = bound z * |t - q| := by dsimp only [bound]; ring
    have hn : 0 ≤ bound z := mul_nonneg (mul_nonneg (by norm_num) hC)
      (riemannianAreaDensity_nonneg (G t₀) U z)
    change |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G q) U z| ≤
      |bound z| * |t - q|
    simpa only [abs_of_nonneg hn] using hmajor
  exact hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict B)
    (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapMetricVariationDensity G t₀ U) (bound := bound)
    (Metric.ball_mem_nhds t₀ hr)
    (Eventually.of_forall (fun t => ((hJ t).mono hDs).aestronglyMeasurable hB.measurableSet))
    hJ0 (hder.aestronglyMeasurable hB.measurableSet)
    ((ae_restrict_mem hB.measurableSet).mono (fun z hz => hloc z hz)) hbound
    ((ae_restrict_mem hB.measurableSet).mono
      (fun z hz => hasDerivAt_diskMapAreaDensity_metric hG ht₀ (hconf z hz)))

/-- First metric variation of the actual area of a smoothly extended disk.
Compactness of the disk image suffices; the ambient manifold need not be compact.
Conformality is an explicit property of the supplied parametrization at contact. -/
theorem SmoothDiskExtension.hasDerivAt_riemannianDiskArea_metric
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t) u)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  obtain ⟨hInt, hderiv⟩ :=
    hasDerivAt_integral_diskMapAreaDensity_metric_of_compact_image hG ht₀ hs hU hDs hconf
  refine ⟨hInt, ?_⟩
  have he : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) := by
    funext t
    exact riemannianDiskArea_eq_of_extension (G t) u U heq
  rw [he]
  exact hderiv

end DifferentialGeometry.Geometry

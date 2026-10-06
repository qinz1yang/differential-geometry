import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskFirstVariation
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

open Set Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

/-- Differentiate the actual area of a fixed map on a measurable subset of a
compact parameter domain. Immersion is needed only almost everywhere; no
regularity of the differential across a seam is required. The baseline area
density is integrable, and all time domination is derived from the compact image. -/
theorem hasDerivAt_riemannianArea_metric_of_ae_immersion
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {U : ℂ → M} (hU : Continuous U) {s K : Set ℂ}
    (hs : MeasurableSet s) (hK : IsCompact K) (hsK : s ⊆ K)
    (hJ₀ : IntegrableOn (riemannianAreaDensity (G t₀) U) s)
    (hi : ∀ᵐ z ∂volume.restrict s,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    IntegrableOn (diskMapGramMetricVariationDensity G t₀ U) s ∧
      HasDerivAt (fun t => riemannianArea (G t) U s)
        (∫ z in s, diskMapGramMetricVariationDensity G t₀ U z) t₀ := by
  have hdiff : ∀ᵐ z ∂volume.restrict s,
      HasDerivAt (fun t => riemannianAreaDensity (G t) U z)
        (diskMapGramMetricVariationDensity G t₀ U z) t₀ :=
    hi.mono (fun z hz => hasDerivAt_diskMapAreaDensity_metric_of_immersion hG ht₀ hz)
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (riemannianAreaDensity (G t) U) (volume.restrict s) :=
    (measurable_riemannianAreaDensity (G t) hU).aestronglyMeasurable
  have hQmeas : AEStronglyMeasurable
      (diskMapGramMetricVariationDensity G t₀ U) (volume.restrict s) := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
      (f := fun h z => h⁻¹ •
        (riemannianAreaDensity (G (t₀ + h)) U z - riemannianAreaDensity (G t₀) U z))
    · intro h
      exact ((hmeas (t₀ + h)).sub (hmeas t₀)).const_smul (h⁻¹ : ℝ)
    · exact hdiff.mono (fun z hz => hz.tendsto_slope_zero_right)
  have himage : IsCompact (U '' K) := hK.image hU
  obtain ⟨r, C, hr, hC, _, hbounds, hLip⟩ :=
    exists_metricFamily_quadratic_time_bounds_on_compact hG ht₀ himage
  let bound : ℂ → ℝ := fun z => 4 * C * riemannianAreaDensity (G t₀) U z
  have hbound : IntegrableOn bound s := hJ₀.const_mul (4 * C)
  have hloc : ∀ z ∈ s,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun t => riemannianAreaDensity (G t) U z) (Metric.ball t₀ r) := by
    intro z hz
    have hzimage : U z ∈ U '' K := mem_image_of_mem U (hsK hz)
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
  exact hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict s)
    (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapGramMetricVariationDensity G t₀ U) (bound := bound)
    (Metric.ball_mem_nhds t₀ hr) (Eventually.of_forall hmeas) hJ₀ hQmeas
    ((ae_restrict_mem hs).mono (fun z hz => hloc z hz)) hbound hdiff

end DifferentialGeometry.Geometry

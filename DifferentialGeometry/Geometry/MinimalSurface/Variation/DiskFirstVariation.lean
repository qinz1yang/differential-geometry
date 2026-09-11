import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskIsotopyDensity



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem SmoothDiskExtension.hasDerivAt_area_isotopy_flux
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
    IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      IntervalIntegrable b volume (-Real.pi) Real.pi ∧
      HasDerivAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
        ((∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
          ∫ θ in -Real.pi..Real.pi, b θ) t₀ := by
  dsimp only
  obtain ⟨s, hs, hDs, hU⟩ := hu.2
  let W : ∀ q, TangentSpace 𝓘(ℝ, E) (U q) :=
    fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t₀ 1
  have hW := contMDiffOn_isotopyDiskVelocity hT hT₀ hΦ hΦ₀ hs hU
  have hmetric := (hu.hasDerivAt_area_metric hG ht₀ hconf).1
  have hdiv := integrableOn_diskMapSectionDivergence (G t₀) hs hU hDs hharm hW
  have hboundary := continuous_diskMapSectionInwardFlux (G t₀) hs hU
    (Metric.sphere_subset_closedBall.trans hDs)
    (fun z hz => hconf z (Metric.sphere_subset_closedBall hz)) hW
  have hflux := integral_diskMapSectionDivergence (G t₀) hs hU hDs hconf hharm hW
  have heq :
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskMapMetricVariationDensity (fun r => Diffeomorph.pullbackMetric (G r) (Φ r)) t₀ U z) =
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
        ∫ θ in -Real.pi..Real.pi,
          (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
            (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
              Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ)) := by
    calc
      _ = ∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationDensity G t₀ U z + diskMapSectionDivergence (G t₀) U W z := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro z hz
        exact diskMapMetricVariationDensity_pullback hG ht₀ hT hT₀ hΦ hΦ₀ hs hU (hDs hz)
      _ = _ := by
        rw [integral_add hmetric hdiv, hflux]
        rfl
  have hd := (hu.hasDerivAt_area_isotopy hG ht₀ hT hT₀ hΦ hΦ₀ hconf).2
  rw [heq] at hd
  exact ⟨hmetric, hboundary.intervalIntegrable _ _, hd⟩

end DifferentialGeometry.Geometry

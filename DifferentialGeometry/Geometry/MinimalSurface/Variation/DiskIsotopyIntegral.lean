import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricIntegral
import DifferentialGeometry.Geometry.Metric.ParameterPullbackFamily
import DifferentialGeometry.Geometry.Measure.Area.Pullback



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem SmoothDiskExtension.hasDerivAt_area_isotopy
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    let H := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
    IntegrableOn (diskMapMetricVariationDensity H t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity H t₀ U z) t₀ := by
  let H := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hT.mem_nhds hT₀) ht₀)
  have hi : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - r) (t₀ + r) t₀ hi
  have hsub : D'.carrier ⊆ T ∩ D.regular := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change t₀ - r < t ∧ t < t₀ + r at ht
    constructor <;> linarith [ht.1, ht.2]
  have hH : MetricFamilySmoothOn D' H :=
    metricFamilySmoothOn_parameterPullback hG hT hΦ D' rfl hsub
  have hH₀ : H t₀ = G t₀ := by
    simp only [H, hΦ₀, Diffeomorph.pullbackMetric_refl]
  have hc : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (H t₀) U z := by
    rwa [hH₀]
  have h := hu.hasDerivAt_area_metric hH (isOpen_Ioo.mem_nhds hi) hc
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (H t) u) =
      (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) := by
    funext t
    exact hu.area_pullback (G t) (Φ t)
  rw [he] at h
  exact h.2

end DifferentialGeometry.Geometry

import DifferentialGeometry.Geometry.Metric.WarpedProduct.Exponential
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity.LinearChange
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpace.Instances

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exponential_metric_congruence
    (g : SmoothRiemannianMetric I M) (κ : ℝ) (p : M × EuclideanHalfSpace 1)
    (v w : TangentSpace (I.prod (𝓡∂ 1)) p) :
    (g.exponentialWarpedEnd κ).inner p v w =
      (g.exponentialWarpedEnd 0).inner p
        ((Real.exp (-κ * p.2.val 0) • v.1, v.2) : E × EuclideanSpace ℝ (Fin 1))
        ((Real.exp (-κ * p.2.val 0) • w.1, w.2) : E × EuclideanSpace ℝ (Fin 1)) := by
  erw [SmoothRiemannianMetric.exponentialWarpedEnd_inner,
    SmoothRiemannianMetric.exponentialWarpedEnd_inner]
  have he : Real.exp (-κ * p.2.val 0) ^ 2 = Real.exp (-2 * κ * p.2.val 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hscale (a : ℝ) (u z : TangentSpace I p.1) :
      g.inner p.1 (a • u) (a • z) = a ^ 2 * g.inner p.1 u z := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
  erw [hscale]
  rw [he]


private theorem exponential_density_pow [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (κ : ℝ) (p : M × EuclideanHalfSpace 1) :
    riemannianVolumeDensity (g.exponentialWarpedEnd 0) (g.exponentialWarpedEnd κ) p =
      Real.exp (-κ * p.2.val 0) ^ Module.finrank ℝ E := by
  let L : TangentSpace (I.prod (𝓡∂ 1)) p →ₗ[ℝ] TangentSpace (I.prod (𝓡∂ 1)) p :=
    (Real.exp (-κ * p.2.val 0) • (LinearMap.id : E →ₗ[ℝ] E)).prodMap
      (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
  have hL (v w : TangentSpace (I.prod (𝓡∂ 1)) p) :
      (g.exponentialWarpedEnd κ).inner p v w =
        (g.exponentialWarpedEnd 0).inner p (L v) (L w) :=
    exponential_metric_congruence g κ p v w
  rw [riemannianVolumeDensity_eq_abs_det_of_inner_eq _ _ p L hL]
  have hd : LinearMap.det L = Real.exp (-κ * p.2.val 0) ^ Module.finrank ℝ E := by
    dsimp [L]
    erw [LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id]
    ring
  rw [hd, abs_of_pos (pow_pos (Real.exp_pos _) _)]

theorem riemannianVolumeDensity_exponentialWarpedEnd [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (κ : ℝ) (p : M × EuclideanHalfSpace 1) :
    riemannianVolumeDensity (g.exponentialWarpedEnd 0) (g.exponentialWarpedEnd κ) p =
      Real.exp (-(Module.finrank ℝ E : ℝ) * κ * p.2.val 0) := by
  rw [exponential_density_pow, ← Real.exp_nat_mul]
  congr 1
  ring

theorem riemannianVolumeMeasure_exponentialWarpedEnd [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (κ : ℝ) :
    riemannianVolumeMeasure (I.prod (𝓡∂ 1)) (M × EuclideanHalfSpace 1)
        (g.exponentialWarpedEnd κ) =
      (riemannianVolumeMeasure (I.prod (𝓡∂ 1)) (M × EuclideanHalfSpace 1)
        (g.exponentialWarpedEnd 0)).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-(Module.finrank ℝ E : ℝ) * κ * p.2.val 0))) := by
  rw [riemannianVolumeMeasure_eq_withDensity (g.exponentialWarpedEnd 0)
    (g.exponentialWarpedEnd κ)]
  congr 1
  funext p
  rw [riemannianVolumeDensity_exponentialWarpedEnd]

end DifferentialGeometry.Integral.Measure

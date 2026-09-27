import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedRay
import DifferentialGeometry.Geometry.Comparison.Busemann.Cylinder.CylinderMinimizingLine

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
namespace DifferentialGeometry.Geometry.Metric

private abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Cyl3 := Sphere3 × ℝ
private abbrev ICyl3 := (𝓡 2).prod 𝓘(ℝ)

private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_line_and_calibrated_rays_on_cylinder
    (g : SmoothRiemannianMetric ICyl3 Cyl3) (hcomplete : RiemannianMetricComplete g) :
    ∃ gamma : ℝ → Cyl3,
      ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ gamma ∧ IsGeodesic g gamma ∧ (gamma 0).2 = 0 ∧
      (∀ s t : ℝ, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) ∧
      ∀ x : Cyl3, ∃ sigma : ℝ → Cyl3,
        ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ sigma ∧ IsGeodesic g sigma ∧ sigma 0 = x ∧
        (∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
          riemannianEDistOf g (sigma s) (sigma t) = ENNReal.ofReal |s - t|) ∧
        let bplus : Cyl3 → ℝ := fun y ↦ ⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t
        ∀ s : ℝ, 0 ≤ s → bplus (sigma s) = bplus x - s := by
  have hsphereConnected : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace Cyl3 := inferInstance
  obtain ⟨gamma, hsmooth, hgeo, hzero, hline⟩ := exists_minimizing_line_on_cylinder g hcomplete
  exact ⟨gamma, hsmooth, hgeo, hzero, hline,
    fun x ↦ exists_calibrated_ray_of_complete_metric g hcomplete gamma hline x⟩

end DifferentialGeometry.Geometry.Metric

end

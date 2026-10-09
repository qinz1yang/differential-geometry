import DifferentialGeometry.Analysis.InnerProductSpace.HemispherePacking
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentDirections
import DifferentialGeometry.Geometry.Comparison.AngularObstruction

set_option autoImplicit false

open Set Metric

namespace Metric.TangentCone

theorem angularObstruction_of_pointed_isometry
    {X E : Type*} [MetricSpace X] {p : X} [HasAnglesAt p]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module.Finite ℝ E]
    (e : TangentCone p ≃ᵢ E) (he : e EuclideanCone.tip = 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθpi : θ ≤ Real.pi / 2) :
    AngularObstruction (SpaceOfDirections p) (Module.finrank ℝ E) θ := by
  rintro ⟨ξ, ζ, hζ, hξ⟩
  have hcard := InnerProductGeometry.card_le_finrank_of_angle_separation
    (fun i => (unitVector e he (ζ i)).val) (unitVector e he ξ).val
    (unitVector e he ξ).property (fun i => (unitVector e he (ζ i)).property) hθ hθpi
    (fun i => by rw [angle_unitVector]; exact hξ i)
    (fun i j hij => by rw [angle_unitVector]; exact hζ i j hij)
  rw [Fintype.card_fin] at hcard
  omega

end Metric.TangentCone

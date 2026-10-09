import DifferentialGeometry.Geometry.Geodesic.Naturality.CoordinateChange
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientTransition

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.MetricKoszul

theorem fderiv_tangent_lift_metricSpray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E}
    (hc : ContDiffOn ℝ 1 c V)
    (hcsymm : ∀ x ∈ V, ∀ u v : E, c x u v = c x v u)
    (hcco : ∀ x ∈ V, IsCoercive (c x))
    (hφ : ContDiffOn ℝ 2 φ U) (hφUV : Set.MapsTo φ U V)
    (hφinv : ∀ x ∈ U, (fderiv ℝ φ x).IsInvertible)
    (hpull : ∀ x ∈ U, ∀ u v : E,
      b x u v = c (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v))
    {z : E × E} (hz : z.1 ∈ U) :
    fderiv ℝ (fun p : E × E => (φ p.1, fderiv ℝ φ p.1 p.2)) z (metricSpray b z) =
      metricSpray c (φ z.1, fderiv ℝ φ z.1 z.2) := by
  apply Geometry.Connection.fderiv_tangent_lift_geodesic_spray
    (A := fun x => raisedKoszulOp (b x) (fderiv ℝ b x))
    (C := fun x => raisedKoszulOp (c x) (fderiv ℝ c x))
    (hφ.contDiffAt (hU.mem_nhds hz))
  intro v
  rw [Analysis.fderiv_fderiv_eq_raisedKoszulOp_of_pullback
    hU hV hc hcsymm hcco hφ hφUV hφinv hpull hz v v]
  exact sub_add_cancel _ _

end DifferentialGeometry.MetricKoszul

import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.PositiveCoreOrientation
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem exists_positive_sphere_smoothSelfAttachment (P : S3) :
    ∃ (c d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold)
      (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)),
      ∃ s : SmoothSelfAttachment c d hcd boundaryAttachment,
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
          sphereTwoTimesCircleLift.toClosedOrientedManifold) := by
  obtain ⟨B, _, c, d, hc, hd, _, hcd⟩ := exists_oriented_stereographic_small_ballCharts P
  obtain ⟨D, hI, h0, h1, hlow, hupp, O, hor, F₀, _⟩ := exists_antipodalSelfAttachment_oriented_model P
  let R := sphereSelfAttachmentManifold P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target O
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let Q := R.pullback H
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph) := Q.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph) := Q.smooth
  let s : SmoothSelfAttachment c d hcd boundaryAttachment := {
    charts := Q.charts
    smooth := Q.smooth
    orientation := Q.orientation
    core_localDiffeomorph := positiveSphereAttachment_core_localDiffeomorph P c d hcd B hc hd D hI h0 h1
    band_localDiffeomorph := positiveSphereAttachment_band_localDiffeomorph P c d hcd B hc hd D hI h0 h1
    lower_localDiffeomorph := positiveSphereAttachment_lower_localDiffeomorph P c d hcd B hc hd D hI h0 h1 hlow
    upper_localDiffeomorph := positiveSphereAttachment_upper_localDiffeomorph P c d hcd B hc hd D hI h0 h1 hupp
    core_preserves_orientation := positiveSphereAttachment_core_preserves_orientation P c d hcd B hc hd D hI h0 h1 O hor }
  let F := (R.pullbackOrientedDiffeomorph H).trans F₀
  exact ⟨c, d, hcd, s, ⟨⟨F.val, F.property⟩⟩⟩

end DifferentialGeometry.Topology

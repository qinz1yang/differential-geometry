import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallPairTransport
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N]
  (c d : BallChart 3 (𝓡 3) M) (c' d' : BallChart 3 (𝓡 3) N)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (F : M ≃ₜ N)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x)
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x)

private theorem chart_image_ball_eq (e : BallChart 3 (𝓡 3) M) (e' : BallChart 3 (𝓡 3) N)
    (he : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (e.chart x) = e'.chart x) :
    F '' (e.chart '' Metric.ball 0 1) = e'.chart '' Metric.ball 0 1 := by
  rw [Set.image_image]
  exact Set.image_congr (fun x hx => he x (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) hx))

def coreHomeomorph : c.DoublePunctured d ≃ₜ c'.DoublePunctured d' :=
  F.subtype (fun x => by
    have himg : F '' (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1) =
        c'.chart '' Metric.ball 0 1 ∪ d'.chart '' Metric.ball 0 1 := by
      rw [Set.image_union, chart_image_ball_eq F c c' hc, chart_image_ball_eq F d d' hd]
    change x ∉ c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1 ↔
      F x ∉ c'.chart '' Metric.ball 0 1 ∪ d'.chart '' Metric.ball 0 1
    rw [← himg, F.injective.mem_set_image])

theorem coreHomeomorph_firstBoundary (z : Sphere (n := 3)) :
    coreHomeomorph c d c' d' F hc hd (c.firstBoundaryMap d hcd z) = c'.firstBoundaryMap d' hcd' z :=
  Subtype.ext (hc z (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.property]; norm_num))

theorem coreHomeomorph_secondBoundary (z : Sphere (n := 3)) :
    coreHomeomorph c d c' d' F hc hd (c.secondBoundaryMap d hcd z) = c'.secondBoundaryMap d' hcd' z :=
  Subtype.ext (hd z (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.property]; norm_num))

variable (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

def homeomorphOfChartTransport : Quotient c d hcd a ≃ₜ Quotient c' d' hcd' a :=
  adjunctionSpaceHomeomorphOfHomeomorph boundaryInclusion (attachingMap c d hcd a)
    boundaryInclusion (attachingMap c' d' hcd' a)
    (Homeomorph.refl _) (Homeomorph.refl _) (coreHomeomorph c d c' d' F hc hd)
    (fun _ => rfl) (by
      rintro ⟨b, z⟩
      cases b
      · exact coreHomeomorph_firstBoundary c d c' d' hcd hcd' F hc hd z
      · exact coreHomeomorph_secondBoundary c d c' d' hcd hcd' F hc hd (a z))

theorem homeomorphOfChartTransport_core (x : c.DoublePunctured d) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (coreInclusion c d hcd a x) =
      coreInclusion c' d' hcd' a (coreHomeomorph c d c' d' F hc hd x) := rfl

theorem homeomorphOfChartTransport_band (x : Band (n := 3)) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (bandInclusion c d hcd a x) =
      bandInclusion c' d' hcd' a x := rfl

private theorem coreHomeomorph_firstRadial (z : Sphere (n := 3)) (r : ℝ) (hr : r ∈ Icc 1 2) :
    coreHomeomorph c d c' d' F hc hd (c.firstRadialMap d hcd z r hr) =
      c'.firstRadialMap d' hcd' z r hr := by
  apply Subtype.ext
  apply hc
  rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
  exact hr.2

private theorem coreHomeomorph_secondRadial (z : Sphere (n := 3)) (r : ℝ) (hr : r ∈ Icc 1 2) :
    coreHomeomorph c d c' d' F hc hd (c.secondRadialMap d hcd z r hr) =
      c'.secondRadialMap d' hcd' z r hr := by
  apply Subtype.ext
  apply hd
  rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
  exact hr.2

theorem homeomorphOfChartTransport_lowerCollar (p : CollarDomain) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (lowerCollar c d hcd a p) =
      lowerCollar c' d' hcd' a p := by
  by_cases ht : p.2.val ≤ 0
  · rw [lowerCollar_of_nonpos c d hcd a p ht, lowerCollar_of_nonpos c' d' hcd' a p ht,
      homeomorphOfChartTransport_core]
    exact congrArg (coreInclusion c' d' hcd' a)
      (coreHomeomorph_firstRadial c d c' d' hcd hcd' F hc hd p.1 (1 - p.2.val) _)
  · rw [lowerCollar_of_pos c d hcd a p (not_le.mp ht), lowerCollar_of_pos c' d' hcd' a p (not_le.mp ht),
      homeomorphOfChartTransport_band]

theorem homeomorphOfChartTransport_upperCollar (p : CollarDomain) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (upperCollar c d hcd a p) =
      upperCollar c' d' hcd' a p := by
  by_cases ht : 0 ≤ p.2.val
  · rw [upperCollar_of_nonneg c d hcd a p ht, upperCollar_of_nonneg c' d' hcd' a p ht,
      homeomorphOfChartTransport_core]
    exact congrArg (coreInclusion c' d' hcd' a)
      (coreHomeomorph_secondRadial c d c' d' hcd hcd' F hc hd (a p.1) (1 + p.2.val) _)
  · rw [upperCollar_of_neg c d hcd a p (not_le.mp ht), upperCollar_of_neg c' d' hcd' a p (not_le.mp ht),
      homeomorphOfChartTransport_band]

end DifferentialGeometry.Topology.SelfAttachment

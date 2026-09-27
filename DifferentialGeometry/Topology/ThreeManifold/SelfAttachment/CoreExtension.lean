import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private def coreDefault : c.DoublePunctured d :=
  c.firstBoundaryMap d hcd (Classical.choice (ConnectedSumQuotient.nonempty_sphere_of_neZero (n := 3)))

def coreExtension (x : M) : Quotient c d hcd a := by
  classical
  exact if hx : x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ then
    coreInclusion c d hcd a ⟨x, hx⟩ else coreInclusion c d hcd a (coreDefault c d hcd)

omit [T2Space M] in
theorem coreExtension_apply (x : c.DoublePunctured d) : coreExtension c d hcd a x.val = coreInclusion c d hcd a x :=
  dif_pos x.property

theorem coreExtension_coreInterior : (fun x : coreInterior c d => coreExtension c d hcd a x.val) =
    coreInteriorInclusion c d hcd a := by
  funext x
  exact coreExtension_apply c d hcd a (coreInteriorToCore c d x)

omit [T2Space M] in
theorem coreExtension_firstBoundary (z : Sphere (n := 3)) :
    coreExtension c d hcd a (c.chart z.val) = coreInclusion c d hcd a (c.firstBoundaryMap d hcd z) :=
  coreExtension_apply c d hcd a (c.firstBoundaryMap d hcd z)

omit [T2Space M] in
theorem coreExtension_secondBoundary (z : Sphere (n := 3)) :
    coreExtension c d hcd a (d.chart z.val) = coreInclusion c d hcd a (c.secondBoundaryMap d hcd z) :=
  coreExtension_apply c d hcd a (c.secondBoundaryMap d hcd z)

end DifferentialGeometry.Topology.SelfAttachment

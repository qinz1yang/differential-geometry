import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCollarDifferential
import DifferentialGeometry.Topology.Manifold.HalfCollarExtension

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem exists_discardedTwoSidedCollar
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) :
    ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun y : Sphere 2 => (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall y)),
      ∃ hwidth : c.radius ≤ cuttingCollarWidth (G.delta b.1),
        ∀ q (hq : 0 ≤ q.2.val), c.toFun q = G.discardedCoreCollar b hb
          ((H.event i).transition.trace.capping.attaching b q.1,
            ⟨q.2.val, hq, q.2.property.2.trans_le hwidth⟩) := by
  have hw := cuttingCollarWidth_pos (G.delta_pos b.1)
  have hinj : Function.Injective (fun y : Sphere 2 =>
      G.discardedCoreCollar b hb (y, ⟨0, le_rfl, hw⟩)) := by
    intro x y hxy
    exact congrArg Prod.fst ((G.discardedCoreCollar_isEmbedding b hb).injective hxy)
  obtain ⟨d, hdwidth, hd⟩ :=
    DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_halfClosedInterval
      hw (G.discardedCoreCollar b hb) (G.discardedCoreCollar_contMDiff b hb) hinj
      (fun s => G.discardedCoreCollar_mfderiv_bijective b hb (s, ⟨0, le_rfl, hw⟩))
  let c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun y : Sphere 2 => (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall y)) := {
    radius := d.radius
    radius_pos := d.radius_pos
    neighborhood := d.neighborhood
    toDiffeomorph := (d.reparametrize ((H.event i).transition.attaching b)).toDiffeomorph
    zero_eq := by
      intro y
      change d.toFun ((H.event i).transition.attaching b y,
        ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩) = _
      rw [d.toFun_zero, (H.event i).transition.attaching_eq,
        ← G.discardedCap_eq_discardedCoreCollar_zero] }
  refine ⟨c, hdwidth, ?_⟩
  intro q hq
  change d.toFun ((H.event i).transition.attaching b q.1, q.2) = _
  simpa only [(H.event i).transition.attaching_eq] using
    hd ((H.event i).transition.attaching b q.1, q.2) hq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

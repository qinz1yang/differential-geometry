import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationModels

/-!
# Local model profiles for a concrete relative assembly

An actual compact map transports the old interior geometry without changing its model. Surface
products supply the complementary native profile through their genuine circle fibrations.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

theorem relativeCapHyperbolicProfile {C D : CompactCarrier.{u}}
    {U : TopologicalSpace.Opens C.Carrier} {V : TopologicalSpace.Opens D.Carrier}
    (e : C.pieceInterior U ≃ₘ⟮C.model, D.model⟯ D.pieceInterior V)
    (g : D.InteriorGeometry V)
    (hg : letI := Manifold.interiorChartedSpace D.model ∞ (M := D.pieceInterior V)
      letI := Manifold.interiorIsManifold D.model ∞ (M := D.pieceInterior V)
      g.model = .hyperbolic) :
    ∃ h : C.InteriorGeometry U,
      letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
      letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
      h.model = .hyperbolic :=
  ⟨transportInteriorGeometry e g, (relativeCapTransportInteriorGeometry_model e g).trans hg⟩

end GC.Seifert

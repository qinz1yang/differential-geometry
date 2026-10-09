import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialLoopLayer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GStrongAssemblyV2

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierConnected_StrongX135 : ConnectedSpace carrier.Carrier := carrier_connected

def radialStrongCertificate : StrongCertificate carrier boundary :=
  strongCertificateOfLayers_GGFF radialPrepared radialSafe radialAdapted radialVertices
    radialVertexLink radialPorts radialSeams radialFaces radialSeamFaceLink
    radialHandleEnds radialRimRegions radialLoopLayer

theorem radialStrongCertificate_rimProduct : radialStrongCertificate.val.RimProduct :=
  radialStrongCertificate.property

theorem radialStrongCertificate_counts :
    radialStrongCertificate.val.vertexCount = 2 ∧
    radialStrongCertificate.val.handleCount = 0 ∧
    radialStrongCertificate.val.edgeCircleCount = 1 ∧
    radialStrongCertificate.val.torusSeamCount = 1 ∧
    radialStrongCertificate.val.sphereSeamCount = 0 ∧
    radialStrongCertificate.val.arcFaceCount = 0 ∧
    radialStrongCertificate.val.loopFaceCount = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem radialStrong_raw_or_aux_nonneg :
    Nonempty (RawGraphPresentation carrier) ∨
      (carrier.model.boundary carrier.Carrier = ∅ ∧
        ∃ g : SmoothRiemannianMetric carrier.model carrier.Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :=
  StrongCertificate.raw_or_aux_nonneg carrier radialStrongCertificate

theorem radialStrong_fc42 :
    Nonempty (RawGraphPresentation carrier) ∨
      (carrier.model.boundary carrier.Carrier = ∅ ∧
        ∃ g : SmoothRiemannianMetric carrier.model carrier.Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :=
  Assembly.exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct
    carrier radialStrongCertificate.val radialStrongCertificate.property

end GC.GraphManifold.Assembly.FC39P0.X135Radial

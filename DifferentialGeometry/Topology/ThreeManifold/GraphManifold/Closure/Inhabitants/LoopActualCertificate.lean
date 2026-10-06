import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcLayer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Strong
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRimProduct

/-!
The SAME actual original ball-handle cycle, deep solid core and first-circle region assemble.
Its actual one handle and two corners retain the original RimProduct in the strong closed wrapper.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly
open FC39P0

def loopActualCertificate : DecompositionCertificate
    (NoCuts.carrier standardThreeSphereLift.{0})
    (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{0})) :=
  ofLayers loopVertexLayer loopEdgeLayer loopCircleRegionData loopPortLayer loopSeamLayer
    loopFaceLayer loopHandleEndLayer loopRimChartLayer loopArcLayer loopCoverLayer loopVerticalLayer
    loopRimRegionLayer loopProtectionLayer

theorem loopActualCertificate_rimProduct : loopActualCertificate.RimProduct := by
  intro _h b
  exact standardLoopBallHandleCycle_rimProduct ⟨0,standardLoopBallHandleCycle.len_pos⟩ b

def loopActualStrongCertificate : StrongCertificate
    (NoCuts.carrier standardThreeSphereLift.{0})
    (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{0})) :=
  ⟨loopActualCertificate,loopActualCertificate_rimProduct⟩

def loopActualStrongClosedCertificate :
    StrongClosedCertificate (NoCuts.carrier standardThreeSphereLift.{0}) :=
  loopActualStrongCertificate.toClosed

def loopActualClosedCertificate :
    ClosedDecompositionCertificate (NoCuts.carrier standardThreeSphereLift.{0}) :=
  loopActualStrongClosedCertificate.toClosedCertificate

theorem loopActualCertificate_counts :
    loopActualCertificate.vertexCount = 2 ∧ loopActualCertificate.handleCount = 1 ∧
    loopActualCertificate.faceCount = 2 ∧ loopActualCertificate.arcFaceCount = 1 ∧
    loopActualCertificate.loopFaceCount = 1 ∧ loopActualCertificate.circ.cornerCount = 2 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem loopActualCertificate_noSeams :
    loopActualCertificate.torusSeamCount = 0 ∧ loopActualCertificate.sphereSeamCount = 0 ∧
    loopActualCertificate.edgeCircleCount = 0 :=
  ⟨rfl,rfl,rfl⟩

theorem loopActualCertificate_nonemptyHandle : Nonempty (Fin loopActualCertificate.handleCount) :=
  ⟨(0 : Fin 1)⟩

theorem loopActualStrongCertificate_same : loopActualStrongCertificate.val =
    loopActualCertificate := rfl

theorem loopActualClosedCertificate_same :
    loopActualClosedCertificate.cert = loopActualCertificate := rfl

end GC.GraphManifold.Assembly

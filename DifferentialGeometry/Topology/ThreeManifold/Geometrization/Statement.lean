import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Prime
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SmoothTorusReconstruction

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
namespace GC.Endpoint
universe u

structure GeometricDecomposition (P : ConnectedClosedOrientedManifold.{u} 3) where
  carrier : CompactCarrier.{u}
  components : carrier.Components
  boundary : TorusGluing carrier
  assembly : SmoothAssembly boundary
  reconstruction : assembly.Reconstruction P
  incompressible : assembly.Incompressible reconstruction
  leftPiece : Fin boundary.count → Fin components.count
  rightPiece : Fin boundary.count → Fin components.count
  left_owned : ∀ i, boundary.gluing.left i ⊆ components.piece (leftPiece i)
  right_owned : ∀ i, boundary.gluing.right i ⊆ components.piece (rightPiece i)
  geometry : components.Geometry

structure GeometrizationCertificate (M : ConnectedClosedOrientedManifold.{u} 3) where
  primeData : PrimeDecomposition M
  geometricFactors : (i : Fin primeData.factors.length) →
    GeometricDecomposition (primeData.factors.get i)

def Geometrizes (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Nonempty (GeometrizationCertificate M)

def GeometrizationConjecture : Prop :=
  ∀ M : ConnectedClosedOrientedManifold.{u} 3, Geometrizes M

def SmoothGeometrizationConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (o : ManifoldOrientation (𝓡 3) M 3),
    Geometrizes { Carrier := M, orientation := o }

theorem geometrizationConjecture_iff_smooth :
    GeometrizationConjecture.{u} ↔ SmoothGeometrizationConjecture.{u} := by
  constructor
  · intro h M _ _ _ _ _ _ o
    exact h { Carrier := M, orientation := o }
  · intro h M
    exact h M.Carrier M.orientation

def GeometrizationCertificate.reconstruction
    {M : ConnectedClosedOrientedManifold.{u} 3} (C : GeometrizationCertificate M) :=
  C.primeData.reconstruction

def GeometrizationCertificate.transport
    {M N : ConnectedClosedOrientedManifold.{u} 3} (C : GeometrizationCertificate M)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      N.toClosedOrientedManifold) : GeometrizationCertificate N where
  primeData := C.primeData.transport f
  geometricFactors := C.geometricFactors

theorem geometrizes_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      N.toClosedOrientedManifold) (h : Geometrizes M) : Geometrizes N := by
  obtain ⟨C⟩ := h
  exact ⟨C.transport f⟩

end GC.Endpoint

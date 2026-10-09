import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Statement

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.Topology
open scoped Manifold ContDiff Topology
namespace GC.Topology
universe u

def componentCarrier (C : CompactCarrier.{u}) (D : C.Components) (i : Fin D.count) :
    CompactCarrier.{u} where
  kind := C.kind
  Carrier := D.piece i
  compact := isCompact_iff_compactSpace.mp (D.piece_compact i)
  orientation := C.orientation.restrictOpen (D.piece i)

structure TorusDecomposition (M : ConnectedClosedOrientedManifold.{u} 3) where
  carrier : CompactCarrier.{u}
  components : carrier.Components
  boundary : TorusGluing carrier
  reconstructionAtlas : SmoothAssembly boundary
  reconstruction : reconstructionAtlas.Reconstruction M
  leftPiece : Fin boundary.count → Fin components.count
  rightPiece : Fin boundary.count → Fin components.count
  left_owned : ∀ i, boundary.gluing.left i ⊆ components.piece (leftPiece i)
  right_owned : ∀ i, boundary.gluing.right i ⊆ components.piece (rightPiece i)

namespace TorusDecomposition

def component {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)
    (i : Fin D.components.count) : CompactCarrier.{u} :=
  componentCarrier D.carrier D.components i

def toGeometricDecomposition {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M)
    (h : D.reconstructionAtlas.Incompressible D.reconstruction)
    (g : D.components.Geometry) : GeometricDecomposition M where
  carrier := D.carrier
  components := D.components
  boundary := D.boundary
  assembly := D.reconstructionAtlas
  reconstruction := D.reconstruction
  incompressible := h
  leftPiece := D.leftPiece
  rightPiece := D.rightPiece
  left_owned := D.left_owned
  right_owned := D.right_owned
  geometry := g

end TorusDecomposition

end GC.Topology

import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff Topology
namespace GC.Endpoint
universe u

inductive CarrierModel
  | closed | withBoundary

abbrev CarrierModel.Space : CarrierModel → Type
  | .closed => EuclideanSpace ℝ (Fin 3)
  | .withBoundary => EuclideanHalfSpace 3

instance (k : CarrierModel) : TopologicalSpace k.Space := by
  cases k
  · exact inferInstanceAs (TopologicalSpace (EuclideanSpace ℝ (Fin 3)))
  · exact inferInstanceAs (TopologicalSpace (EuclideanHalfSpace 3))

abbrev CarrierModel.model (k : CarrierModel) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) k.Space := by
  cases k with
  | closed => exact 𝓡 3
  | withBoundary => exact 𝓡∂ 3

structure CompactCarrier where
  kind : CarrierModel
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace kind.Space Carrier]
  [smooth : IsManifold kind.model ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [compact : CompactSpace Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  orientation : ManifoldOrientation kind.model Carrier 3

attribute [instance] CompactCarrier.topology CompactCarrier.charts CompactCarrier.smooth
  CompactCarrier.hausdorff CompactCarrier.compact CompactCarrier.secondCountable

namespace CompactCarrier

abbrev model (C : CompactCarrier) := C.kind.model

def interior (C : CompactCarrier) : TopologicalSpace.Opens C.Carrier :=
  Manifold.intrinsicInterior C.model ∞ (by simp)

def pieceInterior (C : CompactCarrier) (U : TopologicalSpace.Opens C.Carrier) :
    TopologicalSpace.Opens C.Carrier := U ⊓ C.interior

structure Components (C : CompactCarrier) where
  count : ℕ
  count_pos : 0 < count
  piece : Fin count → TopologicalSpace.Opens C.Carrier
  closed : ∀ i, IsClosed (piece i : Set C.Carrier)
  connected : ∀ i, ConnectedSpace (piece i)
  disjoint : Pairwise (fun i j => Disjoint (piece i : Set C.Carrier) (piece j))
  covers : ⋃ i, (piece i : Set C.Carrier) = Set.univ
  interior_connected : ∀ i, ConnectedSpace (C.pieceInterior (piece i))

instance (C : CompactCarrier) (U : TopologicalSpace.Opens C.Carrier) :
    BoundarylessManifold C.model (C.pieceInterior U) where
  isInteriorPoint' x := C.model.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property.2

theorem Components.piece_compact {C : CompactCarrier} (D : C.Components)
    (i : Fin D.count) : IsCompact (D.piece i : Set C.Carrier) :=
  (D.closed i).isCompact

instance (C : CompactCarrier) (U : TopologicalSpace.Opens C.Carrier) :
    SigmaCompactSpace (C.pieceInterior U) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen C.model
      (C.pieceInterior U).isOpen)

def InteriorGeometry (C : CompactCarrier) (U : TopologicalSpace.Opens C.Carrier) :=
  letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
  letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
  GC.Geometry.GeometricStructure (𝓡 3) (C.pieceInterior U)

def interiorGeometryOfOriginal (C : CompactCarrier) (U : TopologicalSpace.Opens C.Carrier)
    (g : GC.Geometry.GeometricStructure C.model (C.pieceInterior U)) :
    C.InteriorGeometry U := by
  letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
  letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
  exact g.pullback (Manifold.interiorAtlasDiffeomorph C.model ∞ (M := C.pieceInterior U)).symm

def Components.Geometry {C : CompactCarrier} (D : C.Components) :=
  (i : Fin D.count) → C.InteriorGeometry (D.piece i)

end CompactCarrier
end GC.Endpoint

import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatPairs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidFoldData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassConsumers
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Interfaces

/-!
# The geometry of a flat closed triangle block

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§0, §4, §5, with review 27: the flat family first). For charts `C` of a closed triangle block with
`orbChi = 0` and a fold datum `D` on the flat triangle `C.closedEuclidShape`, the fold `flatMap`
restricted to its open domain (`flatRestrict`) is a surjective local diffeomorphism onto the
interior of the block whose same-image pairs are related by local isometries of the model
(`foldRel_of_flatMap_eq`); the restricted model metric of `closedConnectionModel` (`E³` or `Nil`)
therefore descends (`GeometricStructure.ofFold`), with the Thurston atlas of the cone profile and
completeness from compactness of the closed block (`closedTriangleFlatGeometry`, model
`closedTable ⟨d, hc⟩` by `closedTriangleFlatGeometry_model`). On a closed manifold `Q` this gives
the one-piece geometric decomposition (`closedTriangleFlatDecomposition`), and with CF's flat fold
(`CompactShape.exists_foldData_flat`) every closed triangle block with `orbChi = 0` has one
(`closedTriangleBlockGeometry_of_flat`). The frozen `ClosedTriangleBlockGeometry` follows from the
two curved families by the sign of `orbChi` (`closedTriangleBlockGeometry_of_curved`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

section Geometry

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (h0 : d.orbChi = 0) (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

set_option hygiene false in
local notation "𝒦" => flatDatum C hc h3 h0 D

def flatRestrict (y : flatDomain (𝒦)) : W.pieceInterior ⊤ := flatMap C hc h3 (𝒦) y

theorem isLocalDiffeomorph_flatRestrict :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (flatRestrict C hc h3 h0 D) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  exact isLocalDiffeomorph_restrict_open (flatDomain (𝒦))
    (fun x => isLocalDiffeomorphAt_flatMap C hc h3 h0 D x.2)

theorem surjective_flatRestrict : Function.Surjective (flatRestrict C hc h3 h0 D) := by
  intro q
  obtain ⟨x, hx, h⟩ := surjective_flatMap C hc h3 h0 D q
  exact ⟨⟨x, hx⟩, h⟩

def closedTriangleFlatGeometry [CompactSpace (W.pieceInterior ⊤)] : W.InteriorGeometry ⊤ := by
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  have hF := isLocalDiffeomorph_flatRestrict C hc h3 h0 D
  have hsurj := surjective_flatRestrict C hc h3 h0 D
  have hcompat := metricFiberCompatible_of_foldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦))
    (flatMap C hc h3 (𝒦)) hF (fun _ _ hy hy' h => foldRel_of_flatMap_eq C hc h3 h0 D hy hy' h)
  exact GeometricStructure.ofFold ((𝒦).m.coneProfile.metric.restrictOpen (flatDomain (𝒦)))
    ((ConnectionModel.hasThurstonAtlas_coneProfile (𝒦).m).foldRestrictOpen (flatDomain (𝒦)))
    (ConnectionModel.thurston_ne_hyperbolic _) (flatRestrict C hc h3 h0 D) hF hsurj hcompat
    (foldMetric_complete_of_compact _ _ hF hsurj hcompat)

theorem closedTriangleFlatGeometry_model [CompactSpace (W.pieceInterior ⊤)] :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (closedTriangleFlatGeometry C hc h3 h0 D).model = closedTable ⟨d, hc⟩ :=
  d.closedConnectionModel_thurston hc h3

end Geometry

section Decomposition

variable (Q : ConnectedClosedOrientedManifold.{u} 3)

theorem compactSpace_noCuts_pieceInterior :
    CompactSpace ((NoCuts.carrier Q).pieceInterior ⊤) := by
  have h : (((NoCuts.carrier Q).pieceInterior ⊤ : TopologicalSpace.Opens Q.Carrier) :
      Set Q.Carrier) = univ :=
    eq_univ_of_forall fun _ => ⟨trivial, BoundarylessManifold.isInteriorPoint⟩
  exact isCompact_iff_compactSpace.mp (by rw [h]; exact isCompact_univ)

variable {Q} {d : SeifertData} (C : SeifertBlockCharts (NoCuts.carrier Q) d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (h0 : d.orbChi = 0) (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

def closedTriangleFlatDecomposition : GeometricDecomposition Q where
  carrier := NoCuts.carrier Q
  components := NoCuts.components Q
  boundary := NoCuts.boundary Q
  assembly := NoCuts.assembly Q
  reconstruction := NoCuts.reconstruction Q
  incompressible := fun i => i.elim0
  leftPiece := fun i => i.elim0
  rightPiece := fun i => i.elim0
  left_owned := fun i => i.elim0
  right_owned := fun i => i.elim0
  geometry _ :=
    letI := compactSpace_noCuts_pieceInterior Q
    closedTriangleFlatGeometry C hc h3 h0 D

theorem closedTriangleBlockGeometry_of_flat (B : SeifertBlock (NoCuts.carrier Q) d)
    (hc : d.ports = 0) (h3 : d.cones.length = 3) (h0 : d.orbChi = 0) :
    Nonempty (GeometricDecomposition Q) := by
  obtain ⟨C⟩ := B.exists_closed_charts_unconditional hc
  obtain ⟨D⟩ := CompactShape.exists_foldData_flat (C.closedEuclidShape hc h3 h0).toCompactShape rfl
  exact ⟨closedTriangleFlatDecomposition C hc h3 h0 D⟩

end Decomposition

theorem closedTriangleBlockGeometry_flat (Q : ConnectedClosedOrientedManifold.{u} 3)
    (hQ : ∃ d : SeifertData, d.ports = 0 ∧ d.cones.length = 3 ∧ d.orbChi = 0 ∧
      Nonempty (SeifertBlock (NoCuts.carrier Q) d)) :
    Nonempty (GeometricDecomposition Q) := by
  obtain ⟨d, hc, h3, h0, ⟨B⟩⟩ := hQ
  exact closedTriangleBlockGeometry_of_flat B hc h3 h0

theorem closedTriangleBlockGeometry_of_curved
    (hhyp : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData), d.ports = 0 →
      d.cones.length = 3 → d.orbChi < 0 → SeifertBlock (NoCuts.carrier Q) d →
        Nonempty (GeometricDecomposition Q))
    (hsph : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData), d.ports = 0 →
      d.cones.length = 3 → 0 < d.orbChi → SeifertBlock (NoCuts.carrier Q) d →
        Nonempty (GeometricDecomposition Q)) :
    ClosedTriangleBlockGeometry.{u} := by
  rintro Q ⟨d, hc, h3, ⟨B⟩⟩
  rcases lt_trichotomy d.orbChi 0 with h | h | h
  · exact hhyp Q d hc h3 h B
  · exact closedTriangleBlockGeometry_of_flat B hc h3 h
  · exact hsph Q d hc h3 h B

end ClosedTriangle

end GC.Seifert

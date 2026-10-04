import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypPairs
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypFoldData

/-!
# The geometry of a hyperbolic-base closed triangle block

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §0, with
review 33: one assembly for the rows `H² × ℝ` and `SL₂~`). For charts `C` of a closed triangle
block with `orbChi < 0` and a fold datum `D` on the hyperbolic triangle `C.closedHypShape`, the
fold `hypMap` restricted to its open domain (`hypRestrict`) is a surjective local diffeomorphism
onto the interior of the block whose same-image pairs are related by local isometries of the
model (`foldRel_of_hypMap_eq`); the restricted model metric of `closedConnectionModel`
(`H² × ℝ` if `e = 0`, `SL₂~` otherwise) therefore descends (`GeometricStructure.ofFold`), with
the Thurston atlas of the cone profile and completeness from compactness of the closed block
(`closedTriangleHypGeometry`, model `closedTable ⟨d, hc⟩` by `closedTriangleHypGeometry_model`).
On a closed manifold `Q` this gives the one-piece geometric decomposition
(`closedTriangleHypDecomposition`), and with CF-H's hyperbolic fold
(`CompactShape.exists_foldData_hyperbolic`) every closed triangle block with `orbChi < 0` has one
(`closedTriangleBlockGeometry_hyp`, the hyperbolic-base binder of B3b's
`closedTriangleBlockGeometry_of_curved`). The frozen `ClosedTriangleBlockGeometry` then follows
from the spherical family alone (`closedTriangleBlockGeometry_of_spherical`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

section Geometry

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (hχ : d.orbChi < 0) (D : (C.closedHypShape hc h3 hχ).FoldData)

set_option hygiene false in
local notation "𝒦" => hypDatum C hc h3 hχ D

def hypRestrict (y : hypDomain (𝒦)) : W.pieceInterior ⊤ := hypMap C hc h3 (𝒦) y

theorem isLocalDiffeomorph_hypRestrict :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (hypRestrict C hc h3 hχ D) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  exact isLocalDiffeomorph_restrict_open (hypDomain (𝒦))
    (fun x => isLocalDiffeomorphAt_hypMap C hc h3 hχ D x.2)

theorem surjective_hypRestrict : Function.Surjective (hypRestrict C hc h3 hχ D) := by
  intro q
  obtain ⟨x, hx, h⟩ := surjective_hypMap C hc h3 hχ D q
  exact ⟨⟨x, hx⟩, h⟩

def closedTriangleHypGeometry [CompactSpace (W.pieceInterior ⊤)] : W.InteriorGeometry ⊤ := by
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  have hF := isLocalDiffeomorph_hypRestrict C hc h3 hχ D
  have hsurj := surjective_hypRestrict C hc h3 hχ D
  have hcompat := metricFiberCompatible_of_foldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦))
    (hypMap C hc h3 (𝒦)) hF (fun _ _ hy hy' h => foldRel_of_hypMap_eq C hc h3 hχ D hy hy' h)
  exact GeometricStructure.ofFold ((𝒦).m.coneProfile.metric.restrictOpen (hypDomain (𝒦)))
    ((ConnectionModel.hasThurstonAtlas_coneProfile (𝒦).m).foldRestrictOpen (hypDomain (𝒦)))
    (ConnectionModel.thurston_ne_hyperbolic _) (hypRestrict C hc h3 hχ D) hF hsurj hcompat
    (foldMetric_complete_of_compact _ _ hF hsurj hcompat)

theorem closedTriangleHypGeometry_model [CompactSpace (W.pieceInterior ⊤)] :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (closedTriangleHypGeometry C hc h3 hχ D).model = closedTable ⟨d, hc⟩ :=
  d.closedConnectionModel_thurston hc h3

end Geometry

section Decomposition

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {d : SeifertData}
  (C : SeifertBlockCharts (NoCuts.carrier Q) d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (hχ : d.orbChi < 0) (D : (C.closedHypShape hc h3 hχ).FoldData)

def closedTriangleHypDecomposition : GeometricDecomposition Q where
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
    closedTriangleHypGeometry C hc h3 hχ D

theorem closedTriangleBlockGeometry_of_hyp (B : SeifertBlock (NoCuts.carrier Q) d)
    (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : d.orbChi < 0) :
    Nonempty (GeometricDecomposition Q) := by
  obtain ⟨C⟩ := B.exists_closed_charts_unconditional hc
  obtain ⟨D⟩ := CompactShape.exists_foldData_hyperbolic (C.closedHypShape hc h3 hχ)
    (C.closedHypShape_curv hc h3 hχ)
  exact ⟨closedTriangleHypDecomposition C hc h3 hχ D⟩

end Decomposition

theorem closedTriangleBlockGeometry_hyp :
    ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData), d.ports = 0 →
      d.cones.length = 3 → d.orbChi < 0 → SeifertBlock (NoCuts.carrier Q) d →
        Nonempty (GeometricDecomposition Q) :=
  fun _ _ hc h3 hχ B => closedTriangleBlockGeometry_of_hyp B hc h3 hχ

theorem closedTriangleBlockGeometry_of_spherical
    (hsph : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData), d.ports = 0 →
      d.cones.length = 3 → 0 < d.orbChi → SeifertBlock (NoCuts.carrier Q) d →
        Nonempty (GeometricDecomposition Q)) :
    ClosedTriangleBlockGeometry.{u} :=
  closedTriangleBlockGeometry_of_curved closedTriangleBlockGeometry_hyp hsph

end Hyp

end ClosedTriangle

end GC.Seifert

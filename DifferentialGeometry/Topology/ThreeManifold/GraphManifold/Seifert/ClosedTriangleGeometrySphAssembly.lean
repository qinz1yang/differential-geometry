import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphPairs
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphFoldData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypAssembly

/-!
# The geometry of a spherical closed triangle block

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §0, §2, §6,
with review 32). For charts `C` of a closed triangle block with `orbChi > 0`, a fold datum `D` on
the spherical triangle `C.closedSphShape` and a base layout `L`, the chart-level fold
`sphFoldMap` is `2π`-periodic in the Hopf fibre, a local diffeomorphism on `sphBase L`, onto the
interior of the block, and same-image points are related by isometries of the round sphere
(`foldRel_of_sphFoldMap_eq`); it therefore descends to the round three-sphere and the round metric
descends to a complete spherical geometry on the closed block (`sphGeometry`), whose model is
`closedTable ⟨d, hc⟩` (`closedTriangleSphGeometry_model`). With CF-S2's spherical fold
(`CompactShape.exists_foldData_spherical`) and B3d2's layout (`exists_sphLayout`) every closed
triangle block with `orbChi > 0` has the one-piece geometric decomposition
(`closedTriangleBlockGeometry_sph`, the spherical binder of
`closedTriangleBlockGeometry_of_curved`), and with B3c's hyperbolic-base rows and B3b's flat rows the frozen interface holds
(`closedTriangleBlockGeometry`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

section Geometry

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

def closedTriangleSphGeometry [CompactSpace (W.pieceInterior ⊤)] : W.InteriorGeometry ⊤ := by
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  exact sphGeometry (sphFoldMap L C hc h3) (sphFoldMap_period C hc h3 hχ D L)
    (isOpen_sphBase L) (fun _ hx => isLocalDiffeomorphAt_sphFoldMap C hc h3 hχ D L hx)
    (surjective_sphFoldMap C hc h3 hχ D L)
    (fun _ _ hx hx' h => foldRel_of_sphFoldMap_eq C hc h3 hχ D L hx hx' h)

theorem closedTriangleSphGeometry_model [CompactSpace (W.pieceInterior ⊤)] :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (closedTriangleSphGeometry C hc h3 hχ D L).model = closedTable ⟨d, hc⟩ := by
  rw [← d.closedConnectionModel_thurston hc h3, d.closedConnectionModel_of_sph hχ]
  rfl

end Geometry

section Decomposition

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {d : SeifertData}
  (C : SeifertBlockCharts (NoCuts.carrier Q) d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

def closedTriangleSphDecomposition : GeometricDecomposition Q where
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
    closedTriangleSphGeometry C hc h3 hχ D L

theorem closedTriangleBlockGeometry_of_sph (B : SeifertBlock (NoCuts.carrier Q) d)
    (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi) :
    Nonempty (GeometricDecomposition Q) := by
  obtain ⟨C⟩ := B.exists_closed_charts_unconditional hc
  obtain ⟨D⟩ := CompactShape.exists_foldData_spherical (C.closedSphShape hc h3 hχ)
    (C.closedSphShape_curv hc h3 hχ)
  obtain ⟨L⟩ := exists_sphLayout (sphDatum C hc h3 hχ D)
  exact ⟨closedTriangleSphDecomposition C hc h3 hχ D L⟩

end Decomposition

theorem closedTriangleBlockGeometry_sph :
    ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData), d.ports = 0 →
      d.cones.length = 3 → 0 < d.orbChi → SeifertBlock (NoCuts.carrier Q) d →
        Nonempty (GeometricDecomposition Q) :=
  fun _ _ hc h3 hχ B => closedTriangleBlockGeometry_of_sph B hc h3 hχ

end Sph

theorem closedTriangleBlockGeometry : ClosedTriangleBlockGeometry.{u} :=
  Hyp.closedTriangleBlockGeometry_of_spherical Sph.closedTriangleBlockGeometry_sph

end ClosedTriangle

end GC.Seifert

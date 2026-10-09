import DifferentialGeometry.Geometry.Thurston.ZeroCutHyperbolic
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry

/-!
# Admission (b), hyperbolic branch

Lane K17b (chapter 6 design v2, §1 (b); decisions D5, D7). Admission (b) of
`GM/Refinement.lean` starts from a torus decomposition `D` of a closed `M` with incompressible
tori whose pieces are hyperbolic or graph pieces; its conclusion is `Geometrizes M`.

* Relative output of a hyperbolic piece (D5). A hyperbolic piece is never cut: its relative
  output is the piece itself, as the compact carrier `componentCarrier D.carrier D.components i`
  with its own collars. `componentGeometry` moves an interior geometry of the piece to the whole
  interior of that carrier and `pieceGeometry` moves it back (both through X12's
  `componentInteriorDiffeomorph`), keeping the model (`componentGeometry_model`,
  `pieceGeometry_model`). Geometries on all component carriers reassemble along `D` itself
  (`geometryOfComponents`, `geometricDecompositionOfComponents`); no metric matching is needed.
* All pieces geometric. The decomposition `D` with any geometry on its pieces is a geometric
  decomposition of `M` (`TorusDecomposition.toGeometricDecomposition`), so in the all-hyperbolic
  case the conclusion of (b) follows from `IsPrime M` alone
  (`exists_prime_geometric_decomposition_of_isPrime_of_geometry`).
* No tori. With `D.boundary.count = 0` there is one piece; a hyperbolic one makes `M` prime and
  geometric by K17 and K18 (`exists_prime_geometric_decomposition_of_zeroCut_of_hyperbolic`,
  with the hyperbolic piece given as an existential).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open scoped Manifold ContDiff Topology

namespace GC.Topology.TorusDecomposition

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)

def componentGeometry (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i)) :
    (componentCarrier D.carrier D.components i).InteriorGeometry ⊤ :=
  GC.Seifert.transportInteriorGeometry
    (GC.Seifert.componentInteriorDiffeomorph D.carrier D.components i) g

def pieceGeometry (i : Fin D.components.count)
    (g : (componentCarrier D.carrier D.components i).InteriorGeometry ⊤) :
    D.carrier.InteriorGeometry (D.components.piece i) :=
  GC.Seifert.transportInteriorGeometry
    (GC.Seifert.componentInteriorDiffeomorph D.carrier D.components i).symm g

theorem componentGeometry_model (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i)) :
    letI := Manifold.interiorChartedSpace (componentCarrier D.carrier D.components i).model ∞
      (M := (componentCarrier D.carrier D.components i).pieceInterior ⊤)
    letI := Manifold.interiorIsManifold (componentCarrier D.carrier D.components i).model ∞
      (M := (componentCarrier D.carrier D.components i).pieceInterior ⊤)
    letI := Manifold.interiorChartedSpace D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    letI := Manifold.interiorIsManifold D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    (D.componentGeometry i g).model = g.model :=
  rfl

theorem pieceGeometry_model (i : Fin D.components.count)
    (g : (componentCarrier D.carrier D.components i).InteriorGeometry ⊤) :
    letI := Manifold.interiorChartedSpace (componentCarrier D.carrier D.components i).model ∞
      (M := (componentCarrier D.carrier D.components i).pieceInterior ⊤)
    letI := Manifold.interiorIsManifold (componentCarrier D.carrier D.components i).model ∞
      (M := (componentCarrier D.carrier D.components i).pieceInterior ⊤)
    letI := Manifold.interiorChartedSpace D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    letI := Manifold.interiorIsManifold D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    (D.pieceGeometry i g).model = g.model :=
  rfl

def geometryOfComponents
    (G : ∀ i, (componentCarrier D.carrier D.components i).InteriorGeometry ⊤) :
    D.components.Geometry :=
  fun i => D.pieceGeometry i (G i)

def geometricDecompositionOfComponents
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (G : ∀ i, (componentCarrier D.carrier D.components i).InteriorGeometry ⊤) :
    GeometricDecomposition M :=
  D.toGeometricDecomposition incompressible (D.geometryOfComponents G)

end GC.Topology.TorusDecomposition

namespace GC.Endpoint

universe u

theorem exists_prime_geometric_decomposition_of_isPrime_of_geometry
    (M : ConnectedClosedOrientedManifold.{u} 3) (hM : IsPrime M) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (geometry : D.components.Geometry) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  refine ⟨PrimeDecomposition.ofIsPrime M hM, ?_⟩
  rintro ⟨_ | n, hn⟩
  · exact ⟨D.toGeometricDecomposition incompressible geometry⟩
  · exact absurd hn (by simp [PrimeDecomposition.ofIsPrime_factors])

theorem exists_prime_geometric_decomposition_of_zeroCut_of_hyperbolic
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (h : D.boundary.count = 0) (i : Fin D.components.count)
    (hyperbolic : ∃ g : D.carrier.InteriorGeometry (D.components.piece i),
      letI := Manifold.interiorChartedSpace D.carrier.model ∞
        (M := D.carrier.pieceInterior (D.components.piece i))
      letI := Manifold.interiorIsManifold D.carrier.model ∞
        (M := D.carrier.pieceInterior (D.components.piece i))
      g.model = .hyperbolic) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  obtain ⟨g, hg⟩ := hyperbolic
  exact exists_prime_geometric_decomposition_of_zeroCut_hyperbolic M D h i g hg

end GC.Endpoint

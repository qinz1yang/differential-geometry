import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RefinementEndgame
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitProved

/-!
# Endgame of chapter 6: the two geometric-decomposition admissions without inputs

Lane W6's endgame theorems with their last inputs proved: `hC` is lane B3's
`ClosedTriangle.closedTriangleBlockGeometry` (flat B3b, hyperbolic-base rows B3c, spherical row B3d)
and `hMS` is lane MS's `RelativeNormalization.mixedSplit`. Admission (a) of
`GraphManifold/Refinement` becomes
`exists_geometric_decomposition_of_prime_rawGraphPresentation_unconditional`; admission (b), stated
with BE's mirror `PieceProfile` because `HyperbolicOrGraph` lives only in the frozen file, becomes
`exists_prime_geometric_decomposition_of_pieceProfile_unconditional`. Neither this module nor its
imports import `GraphManifold/Refinement` or `GraphManifold/SphereSplitting`.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.Seifert
open GC.Seifert.RelativeNormalization

universe u

namespace GC.GraphManifold

theorem exists_geometric_decomposition_of_prime_rawGraphPresentation_unconditional
    (P : ConnectedClosedOrientedManifold.{u} 3) (hP : IsPrime P)
    (G : RawGraphPresentation (NoCuts.carrier P)) :
    Nonempty (GeometricDecomposition P) :=
  exists_geometric_decomposition_of_prime_rawGraphPresentation_of_closedTriangle
    ClosedTriangle.closedTriangleBlockGeometry P hP G

theorem exists_prime_geometric_decomposition_of_pieceProfile_unconditional
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : (i : Fin D.components.count) → PieceProfile D.carrier D.components i) :
    ∃ P : PrimeDecomposition M,
      ∀ i : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get i)) :=
  exists_prime_geometric_decomposition_of_pieceProfile_of_inputs
    ClosedTriangle.closedTriangleBlockGeometry mixedSplit M D incompressible pieces

end GC.GraphManifold

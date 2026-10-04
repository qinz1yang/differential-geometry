import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RefinementEndgamePrime
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassConsumers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminalSplit
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryFinal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedger
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationOrientedLoop
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksEndpoint
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationInitial
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalCoverEuler
import
  DifferentialGeometry.Topology.ThreeManifold.Geometrization.PrimeGeometricDecompositionWithTori

/-!
# Endgame of chapter 6: the two geometric admissions modulo their open inputs

Lane W6. The two chapter-6 admissions of `GraphManifold/Refinement.lean`, with every input that is
a theorem discharged and the open ones taken with their interface types.

* (S⁺) holds unconditionally (`seifertRefinement_unconditional`): K07's refinement from P1
  (`Wiring.elementarizeOnSubCollar`), the split move from the capped surgery with the proved ledger
  item N4 (`exists_sideData_proved`) and the terminal move `moveTerminal'`.
* (a) `exists_geometric_decomposition_of_prime_rawGraphPresentation_of_closedTriangle hC` has the
  statement of `exists_geometric_decomposition_of_prime_rawGraphPresentation` after `hC`: K07 with
  (S⁺), `hC` and X30's union geometry `goodBlockUnionGeometry_unconditional` on A5's
  `filledPantsBlockGeometry`.
* (b) `exists_prime_geometric_decomposition_of_pieceProfile_of_inputs hC hMS` is BE's mixed
  endpoint with `mx_moves`, `orientedSingleSphere`, X57's `relativeTerminal_to_blockPresentation`,
  `initialMixedStage`, `closedTriangle_fibre_nontrivial` and `filledPantsBlockGeometry`. Its pieces
  are given by `PieceProfile`, the constructor-by-constructor mirror of the frozen
  `HyperbolicOrGraph`, so that this module does not import `GraphManifold/Refinement`; the frozen
  statement itself follows by converting the pieces constructor by constructor.

The open inputs are `hC : ClosedTriangleBlockGeometry` (closed three-cone blocks) and
`hMS : MixedSplit` (the mixed split move).
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.Seifert
open GC.Seifert.RelativeNormalization

universe u

namespace GC.Seifert

theorem seifertRefinement_unconditional : SeifertRefinement.{u} :=
  seifertRefinement_of_elementarizeClosed_of_split_of_terminal
    (elementarizeClosed_of_elementarizeOnSubCollar Wiring.elementarizeOnSubCollar)
    (moveSplit_of_fibreFillingSphereSurgery (fibreFillingSphereSurgery_of_sideData
      fun _ E _ _ h hlin _ hT _ K a => E.exists_sideData_proved h hlin hT K a))
    moveTerminal'

end GC.Seifert

namespace GC.GraphManifold

theorem exists_geometric_decomposition_of_prime_rawGraphPresentation_of_closedTriangle
    (hC : ClosedTriangleBlockGeometry.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3) (hP : IsPrime P)
    (G : RawGraphPresentation (NoCuts.carrier P)) :
    Nonempty (GeometricDecomposition P) :=
  exists_geometric_decomposition_of_prime_rawGraphPresentation_of_inputs
    seifertRefinement_unconditional hC
    (goodBlockUnionGeometry_unconditional filledPantsBlockGeometry hC) P hP G

theorem exists_prime_geometric_decomposition_of_pieceProfile_of_inputs
    (hC : ClosedTriangleBlockGeometry.{u}) (hMS : MixedSplit.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : (i : Fin D.components.count) → PieceProfile D.carrier D.components i) :
    ∃ P : PrimeDecomposition M,
      ∀ i : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get i)) :=
  exists_prime_geometric_decomposition_mixed_of_inputs mx_moves hMS orientedSingleSphere
    relativeTerminal_to_blockPresentation initialMixedStage closedTriangle_fibre_nontrivial hC
    filledPantsBlockGeometry M D incompressible pieces

end GC.GraphManifold

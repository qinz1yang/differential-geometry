import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierNormalize
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

/-!
# Arbitrary distance-one genus-one carriers and the zero-distance terminal move

The proved smooth torus mapping class theorem linearizes the actual presentation without
changing its carrier. The full sphere identification then closes the original terminal statement.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem exists_orientedDiffeomorph_sphere_of_twoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (hp : PrimitiveSlope.delta (torusUnit (T.pairing.matching j) • meridianSlope)
      meridianSlope = 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  let hT := torusMappingClassLinear_holds
  let D := linearPresentation hT T
  let P' : ∀ i, SolidTorusPiece D i := fun i => linearPiece hT (P i)
  have hD : D.pairing.matching j =
      linearTorusDiffeomorph (torusUnit (T.pairing.matching j)) := rfl
  have hpD : PrimitiveSlope.delta (torusUnit (D.pairing.matching j) • meridianSlope)
      meridianSlope = 1 := by
    rw [hD, torusUnit_linearTorusDiffeomorph]
    exact hp
  exact exists_orientedDiffeomorph_sphere_of_linearTwoSolidTori D hc P' j
    (torusUnit (T.pairing.matching j)) hD hpD

namespace ElementaryPresentation

theorem seifertFactor_of_solidSeam_zero_of_lensCarrier
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
    (hL : E.kind (E.toTorus.leftPiece j) = 1) (hR : E.kind (E.toTorus.rightPiece j) = 1)
    (h0 : E.fillingDistance j true = 0) (h0' : E.fillingDistance j false = 0) :
    SeifertFactor Q := by
  have hc := (E.genusOne_counts_of_solidSides hL hR).1
  have hz : E.fillingDistance j true + E.fillingDistance j false = 0 := by
    rw [h0, h0']
  have hp := E.lensDistance_eq_one_of_zero_fillingDistance j
    (Nat.eq_zero_of_add_eq_zero_right hz)
  obtain ⟨f⟩ := exists_orientedDiffeomorph_sphere_of_twoSolidTori E.toTorus hc
    (E.solidPieces_of_solidSides hL hR) j hp
  exact Or.inl (isStandardFactor_of_orientedDiffeomorph f.symm
    isStandardFactor_standardThreeSphereLift)

end ElementaryPresentation

end GC.Seifert

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierComparison
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierProductModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation

/-!
# Distance-zero genus-one carriers are sphere products

A meridian-preserving upper triangular correction reduces the actual matching to the canonical
sphere-product presentation. Full cut diffeomorphisms descend through the actual quotient.
The established mapping class theorem handles arbitrary smooth matching internally.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem exists_diffeomorph_product_of_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (M : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (hp : PrimitiveSlope.delta (M • meridianSlope) meridianSlope = 0) :
    Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier) := by
  obtain ⟨U, hU, hMU, _h10, _h00, _h11⟩ :=
    exists_meridianPreserving_product_normalForm M hp
  refine exists_twoSolidComparison_of_linearCorrection T productCarrierTorusPresentation hc
    productCarrier_components_count productCarrier_pairing_count P j productCarrierSeamIndex
    productCarrier_left_ne_right exists_productCarrierLeft_germ exists_productCarrierRight_germ
    M U hm hU ?_
  rw [hMU]
  exact productCarrier_matching

theorem exists_orientedDiffeomorph_product_of_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (M : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (hp : PrimitiveSlope.delta (M • meridianSlope) meridianSlope = 0) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      sphereTwoTimesCircleLift.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := exists_diffeomorph_product_of_linearTwoSolidTori T hc P j M hm hp
  rcases f.preservesOrientation_or_preservesOrientation_opposite Q.orientation
    sphereTwoTimesCircleLift.orientation with hf | hf
  · exact ⟨⟨f, hf⟩⟩
  · obtain ⟨r, hr⟩ := Manifold.exists_orientationReversing_sphereTwoTimesCircleLift
    exact ⟨⟨f.trans r, Diffeomorph.preservesOrientation_trans hf hr⟩⟩

theorem exists_orientedDiffeomorph_product_of_twoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (hp : PrimitiveSlope.delta (torusUnit (T.pairing.matching j) • meridianSlope)
      meridianSlope = 0) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      sphereTwoTimesCircleLift.toClosedOrientedManifold) := by
  let hT := torusMappingClassLinear_holds
  let D := linearPresentation hT T
  let P' : ∀ i, SolidTorusPiece D i := fun i => linearPiece hT (P i)
  have hm : D.pairing.matching j =
      linearTorusDiffeomorph (torusUnit (T.pairing.matching j)) := rfl
  exact exists_orientedDiffeomorph_product_of_linearTwoSolidTori D hc P' j
    (torusUnit (T.pairing.matching j)) hm hp

end GC.Seifert

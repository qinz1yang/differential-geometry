import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierNormalize
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

/-!
# Arbitrary genus-one carriers with nonzero lens parameter

The established mapping class theorem linearizes the presentation on the same actual carrier.
The full normalized lens diffeomorphism supplies the standard-factor witness, including opposite
orientations, for every nonzero lower-left matching coefficient.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem exists_orientedDiffeomorph_lens_of_nonzero_twoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (h10 : (torusUnit (T.pairing.matching j)).val 1 0 ≠ 0) :
    ∃ (p : ℕ) (hp : NeZero p) (q : ℤ) (hpq : IsCoprime (p : ℤ) q),
      p = ((torusUnit (T.pairing.matching j)).val 1 0).natAbs ∧
      (Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
        (@lensSpaceFormGroup p hp q hpq).manifold.toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
        (@lensSpaceFormGroup p hp q hpq).manifold.opposite.toClosedOrientedManifold)) := by
  let hT := torusMappingClassLinear_holds
  let D := linearPresentation hT T
  let P' : ∀ i, SolidTorusPiece D i := fun i => linearPiece hT (P i)
  have hD : D.pairing.matching j =
      linearTorusDiffeomorph (torusUnit (T.pairing.matching j)) := rfl
  exact exists_orientedDiffeomorph_lens_of_nonzero_linearTwoSolidTori D hc P' j
    (torusUnit (T.pairing.matching j)) hD h10

theorem isStandardFactor_of_nonzero_twoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (h10 : (torusUnit (T.pairing.matching j)).val 1 0 ≠ 0) : isStandardFactor Q := by
  obtain ⟨p, hp, q, hpq, _hpM, h⟩ :=
    exists_orientedDiffeomorph_lens_of_nonzero_twoSolidTori T hc P j h10
  let : NeZero p := hp
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨lensSpaceFormGroup p q hpq, ⟨e⟩⟩
  · obtain ⟨G, ⟨g⟩⟩ := (lensSpaceFormGroup p q hpq).exists_orientedDiffeomorph_opposite
    exact Or.inl ⟨G, ⟨e.trans g⟩⟩

end GC.Seifert

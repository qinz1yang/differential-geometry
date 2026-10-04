import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierArithmetic
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierSphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierComparison
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

/-!
# Full carrier identification after extendable matrix normalization

A meridian preserving source coordinate change is extended over the actual solid piece.
The resulting genuine collar germs descend through the quotient to the normalized lens carrier.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)

theorem exists_diffeomorph_lens_of_normalized_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (M U : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (hU : U • meridianSlope = meridianSlope) (hMU : M * U = lensMatrixUnit p q hpq) :
    Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (lensSpaceFormGroup p q hpq).manifold.Carrier) := by
  let D := lensCarrierTorusPresentation p q hpq
  let k := lensCarrierSeamIndex p q hpq
  refine exists_twoSolidComparison_of_linearCorrection T D hc rfl rfl P j k ?_ ?_ ?_
    M U hm hU ?_
  · intro h
    exact zero_ne_one (congrArg Fin.val h)
  · exact exists_lensCarrierLeft_germ p q hpq
  · exact exists_lensCarrierRight_germ p q hpq
  · rw [hMU]
    rfl

end Lens

theorem exists_orientedDiffeomorph_lens_of_nonzero_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (M : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (h10 : M.val 1 0 ≠ 0) :
    ∃ (p : ℕ) (hp : NeZero p) (q : ℤ) (hpq : IsCoprime (p : ℤ) q),
      p = (M.val 1 0).natAbs ∧
      (Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
        (@lensSpaceFormGroup p hp q hpq).manifold.toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
        (@lensSpaceFormGroup p hp q hpq).manifold.opposite.toClosedOrientedManifold)) := by
  obtain ⟨p, hp, q, hpq, U, hU, hMU, hpM, _h10, _h00, _h11⟩ :=
    exists_meridianPreserving_lens_normalForm M h10
  let hpN : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let : NeZero p := hpN
  obtain ⟨f⟩ := exists_diffeomorph_lens_of_normalized_linearTwoSolidTori
    p q hpq T hc P j M U hm hU hMU
  refine ⟨p, hpN, q, hpq, hpM, ?_⟩
  rcases f.preservesOrientation_or_preservesOrientation_opposite Q.orientation
    (lensSpaceFormGroup p q hpq).manifold.orientation with h | h
  · exact Or.inl ⟨⟨f, h⟩⟩
  · exact Or.inr ⟨⟨f, h⟩⟩

theorem isStandardFactor_of_nonzero_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (M : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (h10 : M.val 1 0 ≠ 0) : isStandardFactor Q := by
  obtain ⟨p, hp, q, hpq, _hpM, h⟩ :=
    exists_orientedDiffeomorph_lens_of_nonzero_linearTwoSolidTori T hc P j M hm h10
  let : NeZero p := hp
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨lensSpaceFormGroup p q hpq, ⟨e⟩⟩
  · obtain ⟨G, ⟨g⟩⟩ := (lensSpaceFormGroup p q hpq).exists_orientedDiffeomorph_opposite
    exact Or.inl ⟨G, ⟨e.trans g⟩⟩

theorem exists_orientedDiffeomorph_sphere_of_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (M : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (hp : PrimitiveSlope.delta (torusUnit (T.pairing.matching j) • meridianSlope)
      meridianSlope = 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  have hcM : (M.val 1 0).natAbs = 1 := by
    rw [hm, torusUnit_linearTorusDiffeomorph, delta_smul_meridian_meridian] at hp
    exact hp
  have h10 : M.val 1 0 ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hcM
    exact Nat.zero_ne_one hcM
  obtain ⟨p, hp0, q, hpq, U, hU, hMU, hpM, _h10, _h00, _h11⟩ :=
    exists_meridianPreserving_lens_normalForm M h10
  obtain rfl : p = 1 := hpM.trans hcM
  obtain ⟨f⟩ := exists_diffeomorph_lens_of_normalized_linearTwoSolidTori
    1 q hpq T hc P j M U hm hU hMU
  obtain ⟨g⟩ := exists_orientedDiffeomorph_lens_one_sphere.{u} q hpq
  rcases (f.trans g.1).preservesOrientation_or_preservesOrientation_opposite Q.orientation
    standardThreeSphereLift.{u}.orientation with h | h
  · exact ⟨⟨f.trans g.1, h⟩⟩
  · obtain ⟨r⟩ := standardThreeSphereLift_orientationReversing_diffeomorph.{u}
    let e : ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
        standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold := ⟨f.trans g.1, h⟩
    exact ⟨e.trans r⟩

end GC.Seifert

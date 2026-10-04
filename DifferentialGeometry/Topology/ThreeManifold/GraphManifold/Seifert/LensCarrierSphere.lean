import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierLinear
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial
import DifferentialGeometry.Topology.Manifold.SphereLinearIsometry

/-!
# The actual order-one lens carrier is the standard sphere

The quotient by the trivial lens action is identified with the oriented standard sphere.
A linear two-solid-torus presentation with this lens matching inherits that full identification.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem exists_orientedDiffeomorph_lens_one_sphere (q : ℤ) (hpq : IsCoprime (1 : ℤ) q) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (lensSpaceFormGroup 1 q hpq).manifold.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  have hG : Subsingleton (lensSpaceFormGroup 1 q hpq).group :=
    @Equiv.subsingleton _ (Multiplicative (ZMod 1))
      (lensSpaceFormGroupEquiv 1 q hpq).toEquiv.symm inferInstance
  exact exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group _ hG

theorem exists_orientedDiffeomorph_sphere_of_lens_one_matching
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (q : ℤ) (hpq : IsCoprime (1 : ℤ) q)
    (hm : T.pairing.matching j = linearTorusDiffeomorph (lensMatrixUnit 1 q hpq)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := exists_diffeomorph_lens_of_linearTwoSolidTori 1 q hpq T hc P j hm
  obtain ⟨g⟩ := exists_orientedDiffeomorph_lens_one_sphere.{u} q hpq
  rcases (f.trans g.1).preservesOrientation_or_preservesOrientation_opposite Q.orientation
    standardThreeSphereLift.{u}.orientation with h | h
  · exact ⟨⟨f.trans g.1, h⟩⟩
  · obtain ⟨r⟩ := standardThreeSphereLift_orientationReversing_diffeomorph.{u}
    let e : ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
        standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold := ⟨f.trans g.1, h⟩
    exact ⟨e.trans r⟩

end GC.Seifert

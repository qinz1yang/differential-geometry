import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedCongruence
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Transport
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereSummand
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy

/-!
# Prime summands of prime graph manifolds

If a prime closed oriented `3`-manifold `M` is orientedly diffeomorphic to a finite connected sum,
then every summand is either diffeomorphic to the `3`-sphere or orientedly diffeomorphic to `M`:
moving the summand to the front, primality makes either it or the rest a sphere, and a sphere is
orientedly diffeomorphic to the standard sphere, which is a unit for the oriented connected sum.
Consequently a prime sphere summand of a prime graph manifold carries a raw graph presentation,
transported either from `M` or from a given presentation of the standard sphere.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.Topology

theorem nonempty_orientedDiffeomorph_standardThreeSphereLift_of_diffeomorph
    (P : ConnectedClosedOrientedManifold.{u} 3)
    (f : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  rcases f.preservesOrientation_or_preservesOrientation_opposite P.orientation
      standardThreeSphereLift.{u}.orientation with h | h
  · exact ⟨⟨f, h⟩⟩
  · obtain ⟨r⟩ := standardThreeSphereLift_orientationReversing_diffeomorph.{u}
    let g : ClosedOrientedManifold.OrientedDiffeomorph P.toClosedOrientedManifold
        standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold := ⟨f, h⟩
    exact ⟨g.trans r⟩

theorem diffeomorph_sphere_or_orientedDiffeomorph_of_finiteConnectedSum_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M)
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (e : ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold M.toClosedOrientedManifold)
    (i : Fin L.length) :
    Nonempty ((L.get i).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (L.get i).toClosedOrientedManifold M.toClosedOrientedManifold) := by
  obtain ⟨F⟩ := finiteConnectedSum_perm (List.getElem_cons_eraseIdx_perm i.isLt)
  have e' := F.trans e
  generalize L.eraseIdx i = R at e'
  change ClosedOrientedManifold.OrientedDiffeomorph
    (finiteConnectedSum (L.get i :: R)).toClosedOrientedManifold M.toClosedOrientedManifold at e'
  generalize L.get i = X at e' ⊢
  cases R with
  | nil => exact Or.inr ⟨e'⟩
  | cons N K =>
    rcases hM X (finiteConnectedSum (N :: K)) ⟨e'.1.symm⟩ with hX | hR
    · exact Or.inl hX
    · obtain ⟨f⟩ := hR
      obtain ⟨s⟩ := nonempty_orientedDiffeomorph_standardThreeSphereLift_of_diffeomorph _ f
      obtain ⟨c⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
        (ClosedOrientedManifold.OrientedDiffeomorph.refl X.toClosedOrientedManifold) s
      obtain ⟨v⟩ := connectedSum_sphere_right X
      exact Or.inr ⟨v.symm.trans (c.symm.trans e')⟩

end DifferentialGeometry.Topology

namespace GC.GraphManifold

theorem rawGraphPresentation_of_sphere_summand_of_isPrime
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    {M P : ConnectedClosedOrientedManifold.{u} 3} (hM : GC.Endpoint.IsPrime M)
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) := by
  have h := diffeomorph_sphere_or_orientedDiffeomorph_of_finiteConnectedSum_of_isPrime hM
    S.reconstruction S.index
  rw [S.factor_eq] at h
  rcases h with hf | hg
  · obtain ⟨f⟩ := hf
    obtain ⟨g⟩ := nonempty_orientedDiffeomorph_standardThreeSphereLift_of_diffeomorph P f
    exact ⟨G₀.transport g.symm.1 g.symm.2⟩
  · obtain ⟨g⟩ := hg
    exact ⟨G.transport g.symm.1 g.symm.2⟩

end GC.GraphManifold

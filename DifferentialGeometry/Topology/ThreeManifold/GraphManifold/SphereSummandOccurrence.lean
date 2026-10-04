import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereSummandConditional
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Opposite

/-!
# Prime summands of graph manifolds, conditionally on structure and factor occurrence

`NonsphereFactorOccurrence` states that every non-sphere prime factor of one oriented connected
sum decomposition of a closed oriented `3`-manifold is diffeomorphic, with no condition on
orientations, to a non-sphere prime factor of any other such decomposition. It is weaker than
`PrimeDecompositionUnique`, which asks for oriented diffeomorphisms, and it says nothing about
multiplicities.

Since a raw graph presentation of a connected closed oriented manifold transports along every
diffeomorphism (`rawGraphPresentation_of_diffeomorph`), this weaker input suffices: a prime
summand `P` of a closed oriented `3`-manifold `M` with a raw graph presentation has a raw graph
presentation, given `GraphPrimeStructure`, `NonsphereFactorOccurrence` and a raw graph
presentation of the standard sphere.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold

def NonsphereFactorOccurrence : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
    (∀ Q ∈ L, GC.Endpoint.IsPrime Q ∧
      ¬ Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)) →
    (∀ Q ∈ K, GC.Endpoint.IsPrime Q ∧
      ¬ Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)) →
    ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold M.toClosedOrientedManifold →
    ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum K).toClosedOrientedManifold M.toClosedOrientedManifold →
    ∀ P ∈ K, ∃ Q ∈ L, Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier)

theorem nonsphereFactorOccurrence_of_primeDecompositionUnique :
    PrimeDecompositionUnique.{u} → NonsphereFactorOccurrence.{u} := by
  intro hU M L K hL hK eL eK P hP
  obtain ⟨Q, hQ, ⟨g⟩⟩ := hU M L K hL hK eL eK P hP
  exact ⟨Q, hQ, ⟨g.1⟩⟩

theorem rawGraphPresentation_of_sphere_summand_of_structure_of_occurrence
    (hS : GraphPrimeStructure.{u}) (hO : NonsphereFactorOccurrence.{u})
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P)
    (hP : GC.Endpoint.IsPrime P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) := by
  by_cases hsph :
      Nonempty (P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)
  · obtain ⟨f⟩ := hsph
    exact rawGraphPresentation_of_diffeomorph G₀ f.symm
  obtain ⟨L, hL, ⟨eL⟩⟩ := hS M G
  obtain ⟨L', hL', ⟨fL⟩⟩ := exists_nonsphere_finiteConnectedSum L
  obtain ⟨F⟩ := finiteConnectedSum_perm (List.getElem_cons_eraseIdx_perm S.index.isLt)
  have e₀ := F.trans S.reconstruction
  generalize S.factors.eraseIdx S.index = R at e₀
  change ClosedOrientedManifold.OrientedDiffeomorph
    (finiteConnectedSum (S.factors.get S.index :: R)).toClosedOrientedManifold
    M.toClosedOrientedManifold at e₀
  rw [S.factor_eq] at e₀
  obtain ⟨D⟩ := exists_primeDecomposition (finiteConnectedSum R)
  obtain ⟨K, hK, ⟨fK⟩⟩ := exists_nonsphere_finiteConnectedSum D.factors
  obtain ⟨a⟩ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (P :: K)).toClosedOrientedManifold
      (connectedSum P (finiteConnectedSum K)).toClosedOrientedManifold) :=
    finiteConnectedSum_append [P] K
  obtain ⟨b⟩ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (P :: R)).toClosedOrientedManifold
      (connectedSum P (finiteConnectedSum R)).toClosedOrientedManifold) :=
    finiteConnectedSum_append [P] R
  obtain ⟨c⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    (ClosedOrientedManifold.OrientedDiffeomorph.refl P.toClosedOrientedManifold)
    (fK.trans D.reconstruction)
  have hK' : ∀ Q ∈ P :: K, IsPrime Q ∧
      ¬ Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact ⟨hP, hsph⟩
    · exact ⟨D.prime Q (hK Q hQ).1, (hK Q hQ).2⟩
  obtain ⟨Q, hQ, ⟨g⟩⟩ := hO M L' (P :: K)
    (fun Q hQ => ⟨(hL Q (hL' Q hQ).1).1, (hL' Q hQ).2⟩) hK' (fL.trans eL)
    (a.trans (c.trans (b.symm.trans e₀))) P (List.mem_cons_self ..)
  obtain ⟨GQ⟩ := (hL Q (hL' Q hQ).1).2
  exact rawGraphPresentation_of_diffeomorph GQ g

theorem rawGraphPresentation_of_sphere_summand_of_assumptions'
    (hS : GraphPrimeStructure.{u}) (hO : NonsphereFactorOccurrence.{u})
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M))
    (S : GC.Topology.SphereSummand M P) (hP : IsPrime P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) :=
  rawGraphPresentation_of_sphere_summand_of_structure_of_occurrence hS hO G₀ G S hP

end GC.GraphManifold

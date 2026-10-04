import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeSummand
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Existence

/-!
# Prime summands of graph manifolds, conditionally on structure and uniqueness

A prime summand `P` of a closed oriented `3`-manifold `M` with a raw graph presentation has a raw
graph presentation, provided two classical inputs: every such `M` is an oriented connected sum of
prime factors with raw graph presentations (`GraphPrimeStructure`), and the non-sphere prime
factors of an oriented connected sum decomposition are unique up to oriented diffeomorphism
(`PrimeDecompositionUnique`), together with a raw graph presentation of the standard sphere. If
`P` is a sphere the presentation of the sphere is transported. Otherwise, after removing sphere
factors, `P` followed by the non-sphere prime factors of the remaining summands is a second
decomposition of `M`, so `P` is orientedly diffeomorphic to a factor of the given structure.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.Topology

theorem exists_nonsphere_finiteConnectedSum (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ P ∈ K, P ∈ L ∧
        ¬ Nonempty (P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum K).toClosedOrientedManifold
        (finiteConnectedSum L).toClosedOrientedManifold) := by
  induction L with
  | nil => exact ⟨[], by simp, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  | cons P L ih =>
    obtain ⟨K, hK, ⟨e⟩⟩ := ih
    obtain ⟨a⟩ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum (P :: L)).toClosedOrientedManifold
        (connectedSum P (finiteConnectedSum L)).toClosedOrientedManifold) :=
      finiteConnectedSum_append [P] L
    by_cases hP :
        Nonempty (P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)
    · refine ⟨K, fun Q hQ => ⟨List.mem_cons_of_mem P (hK Q hQ).1, (hK Q hQ).2⟩, ?_⟩
      obtain ⟨f⟩ := hP
      obtain ⟨s⟩ := nonempty_orientedDiffeomorph_standardThreeSphereLift_of_diffeomorph P f
      obtain ⟨c⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph s
        (ClosedOrientedManifold.OrientedDiffeomorph.refl
          (finiteConnectedSum L).toClosedOrientedManifold)
      obtain ⟨l⟩ := connectedSum_sphere_left (finiteConnectedSum L)
      exact ⟨e.trans (a.trans (c.trans l)).symm⟩
    · obtain ⟨b⟩ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (finiteConnectedSum (P :: K)).toClosedOrientedManifold
          (connectedSum P (finiteConnectedSum K)).toClosedOrientedManifold) :=
        finiteConnectedSum_append [P] K
      obtain ⟨c⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
        (ClosedOrientedManifold.OrientedDiffeomorph.refl P.toClosedOrientedManifold) e
      refine ⟨P :: K, fun Q hQ => ?_, ⟨b.trans (c.trans a.symm)⟩⟩
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact ⟨List.mem_cons_self .., hP⟩
      · exact ⟨List.mem_cons_of_mem _ (hK Q hQ).1, (hK Q hQ).2⟩

end DifferentialGeometry.Topology

namespace GC.GraphManifold

def GraphPrimeStructure : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3), RawGraphPresentation (NoCuts.carrier M) →
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ Q ∈ L, GC.Endpoint.IsPrime Q ∧
        Nonempty (RawGraphPresentation (NoCuts.carrier Q))) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold M.toClosedOrientedManifold)

def PrimeDecompositionUnique : Prop :=
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
    ∀ P ∈ K, ∃ Q ∈ L, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Q.toClosedOrientedManifold P.toClosedOrientedManifold)

theorem rawGraphPresentation_of_sphere_summand_of_structure_of_unique
    (hS : GraphPrimeStructure.{u}) (hU : PrimeDecompositionUnique.{u})
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P)
    (hP : GC.Endpoint.IsPrime P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) := by
  by_cases hsph :
      Nonempty (P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)
  · obtain ⟨f⟩ := hsph
    obtain ⟨g⟩ := nonempty_orientedDiffeomorph_standardThreeSphereLift_of_diffeomorph P f
    exact ⟨G₀.transport g.symm.1 g.symm.2⟩
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
  obtain ⟨Q, hQ, ⟨g⟩⟩ := hU M L' (P :: K)
    (fun Q hQ => ⟨(hL Q (hL' Q hQ).1).1, (hL' Q hQ).2⟩) hK' (fL.trans eL)
    (a.trans (c.trans (b.symm.trans e₀))) P (List.mem_cons_self ..)
  obtain ⟨GQ⟩ := (hL Q (hL' Q hQ).1).2
  exact ⟨GQ.transport g.1 g.2⟩

theorem rawGraphPresentation_of_sphere_summand_of_assumptions
    (hS : GraphPrimeStructure.{u}) (hU : PrimeDecompositionUnique.{u})
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    {M P : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (S : GC.Topology.SphereSummand M P)
    (hP : IsPrime P) :
    Nonempty (RawGraphPresentation (NoCuts.carrier P)) :=
  rawGraphPresentation_of_sphere_summand_of_structure_of_unique hS hU G₀ G S hP

end GC.GraphManifold

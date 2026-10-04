import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereInstances

/-!
# Graph prime structure from inheritance of raw presentations by connected-sum factors

`GraphPrimeStructure` asks that every closed oriented `3`-manifold with a raw graph presentation
be an oriented finite connected sum of prime manifolds with raw graph presentations. It follows
from the single-splitting input `RawPresentationFactorInheritance`: whenever such a manifold is
orientedly diffeomorphic to `A # B` with both fundamental groups nontrivial, both `A` and `B`
have raw graph presentations. The proof is the strong induction on the rank of the fundamental
group that proves `exists_primeDecomposition`. The prime decomposition with graph factors and
geometrization under the per-prime geometric input follow.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint

namespace GC.GraphManifold

universe u

def RawPresentationFactorInheritance : Prop :=
  ∀ (M A B : ConnectedClosedOrientedManifold.{u} 3),
    RawGraphPresentation (NoCuts.carrier M) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum A B).toClosedOrientedManifold M.toClosedOrientedManifold) →
    Nontrivial (FundamentalGroup A.Carrier (chosenPoint A)) →
    Nontrivial (FundamentalGroup B.Carrier (chosenPoint B)) →
    Nonempty (RawGraphPresentation (NoCuts.carrier A)) ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier B))

theorem graphPrimeStructure_of_factorInheritance
    (hF : RawPresentationFactorInheritance.{u}) : GraphPrimeStructure.{u} := by
  suffices h : ∀ n, ∀ N : ConnectedClosedOrientedManifold.{u} 3,
      fundamentalGroupRank N = n → RawGraphPresentation (NoCuts.carrier N) →
      ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
        (∀ Q ∈ L, IsPrime Q ∧ Nonempty (RawGraphPresentation (NoCuts.carrier Q))) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (finiteConnectedSum L).toClosedOrientedManifold N.toClosedOrientedManifold) from
    fun M G => h _ M rfl G
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hN G
    subst hN
    by_cases hP : IsPrime N
    · refine ⟨[N], fun Q hQ => ?_, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
      obtain rfl := List.mem_singleton.mp hQ
      exact ⟨hP, ⟨G⟩⟩
    · obtain ⟨A, B, ⟨e⟩, hA, hB⟩ := exists_nontrivial_splitting_of_not_isPrime N hP
      obtain ⟨hlA, hlB⟩ := fundamentalGroupRank_lt_of_connectedSum A B N e hA hB
      obtain ⟨⟨GA⟩, ⟨GB⟩⟩ := hF N A B G ⟨e⟩ hA hB
      obtain ⟨LA, hLA, ⟨eA⟩⟩ := ih _ hlA A rfl GA
      obtain ⟨LB, hLB, ⟨eB⟩⟩ := ih _ hlB B rfl GB
      obtain ⟨f⟩ := finiteConnectedSum_append LA LB
      obtain ⟨g⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph eA eB
      exact ⟨LA ++ LB, fun Q hQ => (List.mem_append.mp hQ).elim (hLA Q) (hLB Q),
        ⟨(f.trans g).trans e⟩⟩

theorem exists_prime_decomposition_of_rawGraphPresentation_of_factorInheritance
    (hF : RawPresentationFactorInheritance.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : GC.Endpoint.PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  exists_prime_decomposition_of_rawGraphPresentation_of_graphPrimeStructure
    (graphPrimeStructure_of_factorInheritance hF) M G

theorem geometrizes_of_rawGraphPresentation_of_factorInheritance
    (hF : RawPresentationFactorInheritance.{u})
    (hgeo : ∀ P : ConnectedClosedOrientedManifold.{u} 3, GC.Endpoint.IsPrime P →
      RawGraphPresentation (NoCuts.carrier P) →
        Nonempty (GC.Endpoint.GeometricDecomposition P))
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) : GC.Endpoint.Geometrizes M :=
  geometrizes_of_rawGraphPresentation_of_graphPrimeStructure
    (graphPrimeStructure_of_factorInheritance hF) hgeo M G

end GC.GraphManifold

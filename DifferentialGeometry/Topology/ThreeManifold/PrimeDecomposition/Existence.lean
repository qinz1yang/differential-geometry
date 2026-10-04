import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Splitting
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Rank
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws

/-!
# Existence of prime decompositions

Every connected closed oriented smooth 3-manifold has a prime decomposition.  The proof is a strong
induction on the rank of the fundamental group: a prime manifold is its own decomposition, and a
non-prime manifold splits as an oriented connected sum of two factors of strictly smaller rank,
whose decompositions are concatenated.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
universe u

namespace DifferentialGeometry.Topology

private def primeDecompositionSingleton (M : ConnectedClosedOrientedManifold.{u} 3)
    (hM : GC.Endpoint.IsPrime M) : GC.Endpoint.PrimeDecomposition M where
  factors := [M]
  factors_nonempty := List.cons_ne_nil _ _
  prime := fun _ hP => List.mem_singleton.mp hP ▸ hM
  reconstruction := ClosedOrientedManifold.OrientedDiffeomorph.refl _

private theorem nonempty_primeDecomposition_of_connectedSum
    {A B M : ConnectedClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum A B).toClosedOrientedManifold M.toClosedOrientedManifold)
    (DA : GC.Endpoint.PrimeDecomposition A) (DB : GC.Endpoint.PrimeDecomposition B) :
    Nonempty (GC.Endpoint.PrimeDecomposition M) := by
  obtain ⟨f⟩ := finiteConnectedSum_append DA.factors DB.factors
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    DA.reconstruction DB.reconstruction
  exact ⟨{ factors := DA.factors ++ DB.factors
           factors_nonempty := fun h => DA.factors_nonempty (List.append_eq_nil_iff.mp h).1
           prime := fun P hP => (List.mem_append.mp hP).elim (DA.prime P) (DB.prime P)
           reconstruction := (f.trans g).trans e }⟩

theorem exists_primeDecomposition (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (GC.Endpoint.PrimeDecomposition M) := by
  suffices h : ∀ n, ∀ N : ConnectedClosedOrientedManifold.{u} 3,
      fundamentalGroupRank N = n → Nonempty (GC.Endpoint.PrimeDecomposition N) from
    h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hN
    subst hN
    by_cases hP : GC.Endpoint.IsPrime N
    · exact ⟨primeDecompositionSingleton N hP⟩
    · obtain ⟨A, B, ⟨e⟩, hA, hB⟩ := exists_nontrivial_splitting_of_not_isPrime N hP
      obtain ⟨hlA, hlB⟩ := fundamentalGroupRank_lt_of_connectedSum A B N e hA hB
      obtain ⟨DA⟩ := ih _ hlA A rfl
      obtain ⟨DB⟩ := ih _ hlB B rfl
      exact nonempty_primeDecomposition_of_connectedSum e DA DB

end DifferentialGeometry.Topology

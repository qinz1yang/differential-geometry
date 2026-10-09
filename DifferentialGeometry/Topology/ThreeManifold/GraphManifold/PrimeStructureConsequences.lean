import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereSummandConditional
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Transport

/-!
# Prime decompositions of graph manifolds from the prime structure input

Assuming `GraphPrimeStructure` and a raw graph presentation of the standard sphere, every closed
oriented `3`-manifold with a raw graph presentation has a prime decomposition whose factors all
have raw graph presentations. The structure input yields a list of prime factors with
presentations reconstructing `M`; if the list is empty, `M` is orientedly the standard sphere and
the one-factor decomposition `[S³]` is used with the given presentation of the sphere. Given in
addition the per-prime geometric decomposition input, such a manifold geometrizes.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint

namespace GC.GraphManifold

universe u

theorem exists_prime_decomposition_of_rawGraphPresentation_of_structure
    (hS : GraphPrimeStructure.{u})
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : GC.Endpoint.PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hS M G
  cases L with
  | nil =>
    refine ⟨standardThreeSphereLiftPrimeDecomposition.transport e, fun i => ?_⟩
    rw [List.mem_singleton.mp (List.get_mem _ i)]
    exact ⟨G₀⟩
  | cons P L =>
    exact ⟨⟨P :: L, List.cons_ne_nil P L, fun Q hQ => (hL Q hQ).1, e⟩,
      fun i => (hL _ (List.get_mem _ i)).2⟩

theorem geometrizes_of_rawGraphPresentation_of_structure
    (hS : GraphPrimeStructure.{u})
    (G₀ : RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}))
    (hgeo : ∀ P : ConnectedClosedOrientedManifold.{u} 3, GC.Endpoint.IsPrime P →
      RawGraphPresentation (NoCuts.carrier P) →
        Nonempty (GC.Endpoint.GeometricDecomposition P))
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) : GC.Endpoint.Geometrizes M := by
  obtain ⟨D, hD⟩ := exists_prime_decomposition_of_rawGraphPresentation_of_structure hS G₀ M G
  refine ⟨{ primeData := D, geometricFactors := fun i => ?_ }⟩
  exact Classical.choice
    (hgeo (D.factors.get i) (D.prime _ (List.get_mem _ _)) (Classical.choice (hD i)))

end GC.GraphManifold

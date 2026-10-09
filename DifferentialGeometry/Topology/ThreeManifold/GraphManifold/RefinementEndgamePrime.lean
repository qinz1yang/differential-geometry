import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeStructureSideDataProved
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelProved

/-!
# Endgame of chapter 5: the prime decomposition of a graph manifold

Lane W6. `exists_prime_decomposition_of_rawGraphPresentation_unconditional` has exactly the
statement of `exists_prime_decomposition_of_rawGraphPresentation` (`GraphManifold/Refinement.lean`,
Endpoint A of chapter 5), with no hypothesis: it is
`endpoint_prime_decomposition_of_sideData_proved` applied to the ledger item N4, now the theorem
`ElementaryPresentation.exists_sideData_proved`. This module imports neither
`GraphManifold/Refinement` nor `GraphManifold/SphereSplitting`, so the frozen file can import it
in place of `SphereSplitting` and take this theorem as the body of its first declaration.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem exists_prime_decomposition_of_rawGraphPresentation_unconditional
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  endpoint_prime_decomposition_of_sideData_proved
    (fun _ E _ _ h hlin _ hT _ K a => E.exists_sideData_proved h hlin hT K a) M G

end GC.GraphManifold

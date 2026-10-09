import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeGraph
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeInjective
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeTwo

/-!
# Unions of good blocks are prime

Chapter 5 plan P4, tiers T3 and T4. A closed `Q` with a torus presentation whose ports are
π₁-injective and whose pieces have freely indecomposable, non-cyclic fundamental groups is prime
(`isPrime_of_torusPresentation`): π₁ of `Q` is freely indecomposable by T2
(`TorusPresentation.indecomposableNoncyclic_of_vertex`), and a freely indecomposable π₁ makes `Q`
prime by van Kampen for connected sums and the Poincaré conjecture
(`isPrime_of_freelyIndecomposable`). For a union of good blocks
`B : BlockedPresentation (NoCuts.carrier Q)` the ports are those of the blocks
(`pieceBoundaryTori_incompressible_of_isGood`), so `Q` is prime as soon as every block has
freely indecomposable, non-cyclic π₁ (`BlockedPresentation.isPrime_of_vertex`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)

universe u

namespace GC.Seifert

theorem isPrime_of_torusPresentation {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q))
    (hports : ∀ i, (T.pieceBoundaryTori i).incompressible)
    (hvert : ∀ i (x : T.components.piece i),
      IndecomposableNoncyclic (FundamentalGroup (T.components.piece i) x)) :
    IsPrime Q :=
  isPrime_of_freelyIndecomposable Q (chosenPoint Q)
    (T.indecomposableNoncyclic_of_vertex T.externalCount_eq_zero hports hvert (chosenPoint Q)).1

namespace BlockedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem isPrime_of_vertex (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hvert : ∀ i (x : (componentCarrier B.base.cutCarrier B.base.components i).Carrier),
      IndecomposableNoncyclic
        (FundamentalGroup (componentCarrier B.base.cutCarrier B.base.components i).Carrier x)) :
    IsPrime Q :=
  isPrime_of_torusPresentation B.base (B.pieceBoundaryTori_incompressible_of_isGood hB) hvert

theorem isPrime_of_fillingCount_le_one (B : BlockedPresentation (NoCuts.carrier Q))
    (hB : B.IsGood) (hn : 0 < B.base.pairing.count) (hf : ∀ i, (B.data i).fillingCount ≤ 1) :
    IsPrime Q :=
  B.isPrime_of_vertex hB fun i x => (B.block i).indecomposableNoncyclic_of_commute (hB i)
    (B.ports_ne_zero_of_pairing_pos hn i)
    ((B.block i).exists_fibreClass_commute_of_fillingCount_le_one (hf i)) x

end BlockedPresentation

theorem terminalUnion_prime {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hn : 0 < B.base.pairing.count) : IsPrime Q :=
  B.isPrime_of_vertex hB fun i x =>
    (B.block i).indecomposableNoncyclic (hB i) (B.ports_ne_zero_of_pairing_pos hn i) x

theorem isPrime_of_goodBlockUnion_of_pairing_pos {Q : ConnectedClosedOrientedManifold.{u} 3}
    (h : ∃ B : BlockedPresentation (NoCuts.carrier Q), B.IsGood ∧ 0 < B.base.pairing.count) :
    IsPrime Q := by
  obtain ⟨B, hB, hn⟩ := h
  exact terminalUnion_prime B hB hn

end GC.Seifert

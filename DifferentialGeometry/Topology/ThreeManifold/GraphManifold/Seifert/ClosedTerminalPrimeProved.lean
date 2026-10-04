import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalPrimeNonneg
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalCoverEuler

/-!
# Closed terminal primeness

Chapter 5 plan P5, closed. Both three-cone certificates are theorems: `hfin` is Codex X42's
`closedTriangle_finite_fundamentalGroup` and `hnon` is lane P5c's
`closedTriangle_fibre_nontrivial`. Feeding `hnon` to the connectors of
`ClosedTerminalPrimeNonneg.lean` gives the frozen unconditional P5 statements
`closedTerminal_prime`, `zeroSeamBlocked_prime` and `TerminalPresentation.isPrime`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold

universe u

namespace GC.Seifert

theorem closedTerminal_prime (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0) : IsPrime Q :=
  closedTerminal_prime_of_nonneg closedTriangle_fibre_nontrivial Q d B hclosed

theorem zeroSeamBlocked_prime {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hzero : B.base.pairing.count = 0) : IsPrime Q :=
  zeroSeamBlocked_prime_of_nonneg closedTriangle_fibre_nontrivial B hB hzero

theorem TerminalPresentation.isPrime {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TerminalPresentation Q) : IsPrime Q :=
  T.isPrime_of_nonneg closedTriangle_fibre_nontrivial

end GC.Seifert

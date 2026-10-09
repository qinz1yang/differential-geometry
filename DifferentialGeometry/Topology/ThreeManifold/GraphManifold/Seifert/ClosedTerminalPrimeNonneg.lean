import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalPrimeThreeCone
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFinite

/-!
# Closed terminal primeness modulo the nonpositive three-cone certificate

Codex X42 proved the frozen `closedTriangle_finite_fundamentalGroup` (a closed block with three
cones and `0 < orbChi` has finite `π₁`), the certificate `hfin` of `ClosedTerminalPrime.lean`.
With it the three-cone forms of `ClosedTerminalPrimeThreeCone.lean` keep only `hnon` (a nontrivial
fibre class when `orbChi ≤ 0`): `closedTerminal_prime_of_nonneg`,
`zeroSeamBlocked_prime_of_nonneg` and `TerminalPresentation.isPrime_of_nonneg`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold

universe u

namespace GC.Seifert

theorem closedTerminal_prime_of_nonneg
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0) : IsPrime Q :=
  closedTerminal_prime_of_three_cone closedTriangle_finite_fundamentalGroup hnon Q d B hclosed

theorem zeroSeamBlocked_prime_of_nonneg
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hzero : B.base.pairing.count = 0) : IsPrime Q :=
  zeroSeamBlocked_prime_of_three_cone closedTriangle_finite_fundamentalGroup hnon B hB hzero

theorem TerminalPresentation.isPrime_of_nonneg
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    {Q : ConnectedClosedOrientedManifold.{u} 3} (T : TerminalPresentation Q) : IsPrime Q :=
  T.isPrime_of_three_cone closedTriangle_finite_fundamentalGroup hnon

end GC.Seifert

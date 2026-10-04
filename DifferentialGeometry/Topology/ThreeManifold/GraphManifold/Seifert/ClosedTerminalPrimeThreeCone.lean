import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof

/-!
# Closed terminal primeness modulo the two three-cone certificates

The standard-factor certificate `hsmall` of `ClosedTerminalPrime.lean` is already a theorem: a
closed block with at most two cones is a standard factor by
`SeifertBlock.isStandardFactor_of_closed_small` with `torusMappingClassLinear_holds`. Feeding it
to the `_standard` variants leaves only the two three-cone certificates `hfin` (finite `π₁` when
`0 < orbChi`) and `hnon` (a nontrivial fibre class when `orbChi ≤ 0`) as explicit hypotheses of
`closedTerminal_prime_of_three_cone`, `zeroSeamBlocked_prime_of_three_cone` and
`TerminalPresentation.isPrime_of_three_cone`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold

universe u

namespace GC.Seifert

theorem closedTerminal_prime_of_three_cone
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0) : IsPrime Q :=
  closedTerminal_prime_of_standard hfin hnon
    (fun _Q _d B hp hc => B.isStandardFactor_of_closed_small hp hc torusMappingClassLinear_holds)
    Q d B hclosed

theorem zeroSeamBlocked_prime_of_three_cone
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hzero : B.base.pairing.count = 0) : IsPrime Q :=
  zeroSeamBlocked_prime_of_standard hfin hnon
    (fun _Q _d B hp hc => B.isStandardFactor_of_closed_small hp hc torusMappingClassLinear_holds)
    B hB hzero

theorem TerminalPresentation.isPrime_of_three_cone
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    {Q : ConnectedClosedOrientedManifold.{u} 3} (T : TerminalPresentation Q) : IsPrime Q :=
  T.isPrime_of_standard hfin hnon
    (fun _Q _d B hp hc => B.isStandardFactor_of_closed_small hp hc torusMappingClassLinear_holds)

end GC.Seifert

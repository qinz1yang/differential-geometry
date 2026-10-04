import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalPrime
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrime

/-!
# Terminal presentations

Chapter 5 plan P5/P0 (survey X31 §4, accepted by review 19). A `TerminalPresentation Q` keeps,
for one closed oriented `Q`, both a raw graph presentation of `Q` and a proof that `Q` is a
Seifert factor: a standard factor, a closed triangle block or a closed union of good blocks. It
is a future normalization output, not an input: it assumes neither primeness nor geometry, and
the two fields need not be related.

Primeness (`TerminalPresentation.isPrime_of`) splits the factor proof: a standard factor is
prime (`isPrime_of_isStandardFactor`); a closed triangle block is prime by
`closedTerminal_prime_of`; a union of good blocks is prime by `terminalUnion_prime` if it has a
seam and by `zeroSeamBlocked_prime_of` otherwise. The remaining P5 certificates `hfin`, `hnon`,
`hsmall` (see `ClosedTerminalPrime.lean`) are explicit hypotheses; the `_standard` variant takes
`hsmall` in the stronger standard-factor form.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold

universe u

namespace GC.Seifert

structure TerminalPresentation (Q : ConnectedClosedOrientedManifold.{u} 3) where
  raw : RawGraphPresentation (NoCuts.carrier Q)
  factor : SeifertFactor Q

theorem SeifertFactor.isPrime_of
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → IsPrime Q)
    {Q : ConnectedClosedOrientedManifold.{u} 3} (h : SeifertFactor Q) : IsPrime Q := by
  rcases h with hs | ⟨d, hp, -, ⟨B⟩⟩ | ⟨B, hB⟩
  · exact isPrime_of_isStandardFactor Q hs
  · exact closedTerminal_prime_of hfin hnon hsmall Q d B hp
  · rcases Nat.eq_zero_or_pos B.base.pairing.count with hz | hn
    · exact zeroSeamBlocked_prime_of hfin hnon hsmall B hB hz
    · exact terminalUnion_prime B hB hn

namespace TerminalPresentation

theorem isPrime_of
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → IsPrime Q)
    {Q : ConnectedClosedOrientedManifold.{u} 3} (T : TerminalPresentation Q) : IsPrime Q :=
  T.factor.isPrime_of hfin hnon hsmall

theorem isPrime_of_standard
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → isStandardFactor Q)
    {Q : ConnectedClosedOrientedManifold.{u} 3} (T : TerminalPresentation Q) : IsPrime Q :=
  T.isPrime_of hfin hnon fun Q d B hp hc => isPrime_of_isStandardFactor Q (hsmall Q d B hp hc)

end TerminalPresentation

end GC.Seifert

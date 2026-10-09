import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFibre
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometryDispatch
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.CentrePrime

/-!
# Closed terminal blocks are prime, given the two three-cone certificates

Chapter 5 plan P5, the prime assembly for closed blocks (route of review 19). The three
remaining P5 certificates enter as explicit hypotheses of the `_of` theorems, with exactly the
types of the frozen statements, quantified over the closed block:

* `hfin`: a closed block with three cones and `0 < orbChi` has finite `π₁` (frozen
  `closedTriangle_finite_fundamentalGroup`);
* `hnon`: a closed block with three cones and `orbChi ≤ 0` has a nontrivial fibre class
  (frozen `closedTriangle_fibre_nontrivial`);
* `hsmall`: a closed block with at most two cones gives a prime carrier (the weaker form, fed
  by a future `closedSmall_isPrime`), or a standard factor in the `_standard` variants (frozen
  `closedSmall_isStandardFactor`).

A closed block has at most three cones. With three cones and `0 < orbChi` the carrier has finite
`π₁` and is prime (`isPrime_of_finite_fundamentalGroup`). With `orbChi ≤ 0` the fibre class is
nontrivial at some point and central at some point (`exists_closedFibreClass_commute`); after
moving both to one point (`fibreClass_commute_transfer`) the carrier is prime
(`closedBlock_prime_of_fibreClass_ne_one`, through `isPrime_of_center_nontrivial`). This gives
`closedTerminal_prime_of`.

Zero outer seams. A blocked presentation of a closed carrier without seams has no owned sides,
so every block has no free port (`ports_eq_zero_of_pairing_count_eq_zero`, the converse direction
of `unique_block_of_ports_eq_zero`). The block of any piece is then transported to a closed block
on the whole carrier (`zeroPortBlock`), and `zeroSeamBlocked_prime_of` follows. Goodness is not
used for zero seams; positive seams are `terminalUnion_prime`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold

universe u

namespace GC.Seifert

namespace BlockedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem ports_eq_zero_of_pairing_count_eq_zero (B : BlockedPresentation (NoCuts.carrier Q))
    (hzero : B.base.pairing.count = 0) (i : Fin B.base.components.count) :
    (B.data i).ports = 0 := by
  have : IsEmpty (B.base.OwnedSide i) := ⟨fun s => by
    rcases s with ⟨k | k | k, -⟩
    · exact Fin.elim0 (Fin.cast hzero k)
    · exact Fin.elim0 (Fin.cast hzero k)
    · exact Fin.elim0 (Fin.cast B.base.externalCount_eq_zero k)⟩
  rw [← (B.block i).externalCount_eq, B.externalCount_eq i, Fintype.card_eq_zero]

end BlockedPresentation

theorem closedBlock_prime_of_fibreClass_ne_one (Q : ConnectedClosedOrientedManifold.{u} 3)
    (d : SeifertData) (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0)
    (hnon : ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    IsPrime Q := by
  obtain ⟨p, hp⟩ := hnon
  obtain ⟨q, hq⟩ := exists_closedFibreClass_commute Q d B hclosed
  exact isPrime_of_center_nontrivial Q (B.productToCarrier p) (B.fibreClass p) hp
    (B.fibreClass_commute_transfer q p hq)

theorem cones_length_le_two_or_eq_three (d : SeifertData) :
    d.cones.length ≤ 2 ∨ d.cones.length = 3 := by
  have h := d.ports_add_length_add_length
  have hk := d.k_le_three
  omega

theorem closedTerminal_prime_of
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → IsPrime Q)
    (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0) : IsPrime Q := by
  rcases cones_length_le_two_or_eq_three d with hc | hc
  · exact hsmall Q d B hclosed hc
  rcases lt_or_ge 0 d.orbChi with hchi | hchi
  · have := hfin Q d B hclosed hc hchi
    exact isPrime_of_finite_fundamentalGroup Q (chosenPoint Q)
  · exact closedBlock_prime_of_fibreClass_ne_one Q d B hclosed (hnon Q d B hclosed hc hchi)

theorem closedTerminal_prime_of_standard
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → isStandardFactor Q)
    (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0) : IsPrime Q :=
  closedTerminal_prime_of hfin hnon
    (fun Q d B hp hc => isPrime_of_isStandardFactor Q (hsmall Q d B hp hc)) Q d B hclosed

theorem zeroSeamBlocked_prime_of
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → IsPrime Q)
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (_hB : B.IsGood)
    (hzero : B.base.pairing.count = 0) : IsPrime Q := by
  let i : Fin B.base.components.count := ⟨0, B.base.components.count_pos⟩
  have h := B.ports_eq_zero_of_pairing_count_eq_zero hzero i
  exact closedTerminal_prime_of hfin hnon hsmall Q (B.data i) (B.zeroPortBlock i h) h

theorem zeroSeamBlocked_prime_of_standard
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hsmall : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length ≤ 2 → isStandardFactor Q)
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hzero : B.base.pairing.count = 0) : IsPrime Q :=
  zeroSeamBlocked_prime_of hfin hnon
    (fun Q d B hp hc => isPrime_of_isStandardFactor Q (hsmall Q d B hp hc)) B hB hzero

end GC.Seifert

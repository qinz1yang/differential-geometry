import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereSummandConditional

/-!
# The prime structure of graph manifolds from the normalization

Chapter 5 plan P0, step 5 (survey X31 §5, review 19 §7–8). `GraphPrimeStructure` asks, for every
closed `M` with a raw graph presentation, for a list of prime factors with raw presentations
whose connected sum is orientedly `M`. The raw-retaining normalization `normalize_of_moves` gives
a list of manifolds with terminal presentations; each keeps its raw presentation
(`TerminalPresentation.raw`) and is prime by `TerminalPresentation.isPrime_of_three_cone`
(standard factors, closed blocks, and good unions: `terminalUnion_prime` with a seam, the
zero-seam branch otherwise). The hypotheses are exactly the strengthened split move `hM2`, the
elementarization `hE`, and the two three-cone certificates `hfin`, `hnon` of P5.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem graphPrimeStructure_of_normalize_of_elementarizeClosed
    (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeClosed.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} := by
  intro M G
  obtain ⟨L, hL, e⟩ := normalize_of_moves_of_elementarizeClosed hM2 hE M G
  refine ⟨L, fun Q hQ => ?_, e⟩
  obtain ⟨T⟩ := hL Q hQ
  exact ⟨T.isPrime_of_three_cone hfin hnon, ⟨T.raw⟩⟩

theorem graphPrimeStructure_of_normalize
    (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeOnSubCollar.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_normalize_of_elementarizeClosed hM2
    (elementarizeClosed_of_elementarizeOnSubCollar hE) hfin hnon

end GC.GraphManifold

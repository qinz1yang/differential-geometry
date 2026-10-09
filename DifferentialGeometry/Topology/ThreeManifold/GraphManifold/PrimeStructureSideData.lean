import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.NormalizationConsequences
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminalSplit

/-!
# The prime structure and Endpoint A modulo the four open inputs

Chapter 5 plan P0. The strengthened split move follows from the capped solid tori of N2c's
surgery (`moveSplitTerminalRaw_of_sideData`), so `GraphPrimeStructure` and the prime
decomposition with raw factors of Endpoint A hold modulo exactly four inputs, all explicit:
the ledger item N4 (`hN4`, the statement of `exists_sideData`), the elementarization `hE` of P1,
and the two three-cone certificates `hfin`, `hnon` of P5.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem graphPrimeStructure_of_sideData
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hE : ElementarizeOnSubCollar.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_normalize (moveSplitTerminalRaw_of_sideData hN4) hE hfin hnon

theorem endpoint_prime_decomposition_of_sideData
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hE : ElementarizeOnSubCollar.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  endpoint_prime_decomposition (moveSplitTerminalRaw_of_sideData hN4) hE hfin hnon M G

end GC.GraphManifold

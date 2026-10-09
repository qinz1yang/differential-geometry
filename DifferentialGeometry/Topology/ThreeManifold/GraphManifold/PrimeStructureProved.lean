import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeStructureNonneg
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusFinal

/-!
# Graph prime structure modulo the side data and the nonpositive three-cone certificate

P1's `ElementarizeOnSubCollar` is proved (`Wiring.elementarizeOnSubCollar`, lanes P1X2 and MD5b),
so P0a's consumers drop `hE`: `graphPrimeStructure_of_normalize_of_elementarize` (with `hfin`),
`graphPrimeStructure_of_normalize_of_nonneg_of_elementarize`,
`graphPrimeStructure_of_sideData_of_nonneg_of_elementarize` (only N4's side data and `hnon`),
`endpoint_prime_decomposition_of_sideData_of_elementarize` (with `hfin`) and
`endpoint_prime_decomposition_of_sideData_of_nonneg_of_elementarize` (only N4 and `hnon`).
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem graphPrimeStructure_of_normalize_of_elementarize
    (hM2 : MoveSplitTerminalRaw.{u})
    (hfin : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData),
      SeifertBlock (NoCuts.carrier Q) d → d.ports = 0 → d.cones.length = 3 → 0 < d.orbChi →
        Finite (FundamentalGroup Q.Carrier (chosenPoint Q)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_normalize hM2 Wiring.elementarizeOnSubCollar hfin hnon

theorem graphPrimeStructure_of_normalize_of_nonneg_of_elementarize
    (hM2 : MoveSplitTerminalRaw.{u})
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_normalize_of_nonneg hM2 Wiring.elementarizeOnSubCollar hnon

theorem graphPrimeStructure_of_sideData_of_nonneg_of_elementarize
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_sideData_of_nonneg hN4 Wiring.elementarizeOnSubCollar hnon

theorem endpoint_prime_decomposition_of_sideData_of_elementarize
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
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
  endpoint_prime_decomposition_of_sideData hN4 Wiring.elementarizeOnSubCollar hfin hnon M G

theorem endpoint_prime_decomposition_of_sideData_of_nonneg_of_elementarize
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  endpoint_prime_decomposition_of_sideData_of_nonneg hN4 Wiring.elementarizeOnSubCollar hnon M G

end GC.GraphManifold

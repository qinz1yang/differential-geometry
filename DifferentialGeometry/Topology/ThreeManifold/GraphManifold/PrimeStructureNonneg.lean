import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeStructureSideData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFinite

/-!
# Graph prime structure without the finite three-cone certificate

Codex X42's `closedTriangle_finite_fundamentalGroup` discharges `hfin` in P0a's consumers:
`graphPrimeStructure_of_normalize_of_nonneg`, `graphPrimeStructure_of_sideData_of_nonneg` and
`endpoint_prime_decomposition_of_sideData_of_nonneg` keep the strengthened split move (or N4's side
data), `hE` and `hnon` only.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem graphPrimeStructure_of_normalize_of_nonneg
    (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeOnSubCollar.{u})
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_normalize hM2 hE closedTriangle_finite_fundamentalGroup hnon

theorem graphPrimeStructure_of_sideData_of_nonneg
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hE : ElementarizeOnSubCollar.{u})
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_sideData hN4 hE closedTriangle_finite_fundamentalGroup hnon

theorem endpoint_prime_decomposition_of_sideData_of_nonneg
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hE : ElementarizeOnSubCollar.{u})
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  endpoint_prime_decomposition_of_sideData hN4 hE closedTriangle_finite_fundamentalGroup hnon M G

end GC.GraphManifold

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeStructureProved
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalPrimeProved

/-!
# Graph prime structure modulo the side data

Chapter 5 plan P0 with P1 and P5 closed. The elementarization `hE` is proved
(`Wiring.elementarizeOnSubCollar`) and both three-cone certificates are theorems
(`closedTriangle_finite_fundamentalGroup`, `closedTriangle_fibre_nontrivial`), so P0a's consumers
keep only `hN4`, the statement of the ledger item N4 `exists_sideData`:
`graphPrimeStructure_of_sideData_proved`, `endpoint_prime_decomposition_of_sideData_proved`
(Endpoint A) and `endpoint_geometrizes_of_sideData_proved` (with the per-prime geometric input
`hgeo` of the geometric consumer).
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert

namespace GC.GraphManifold

universe u

theorem graphPrimeStructure_of_sideData_proved
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂)) :
    GraphPrimeStructure.{u} :=
  graphPrimeStructure_of_sideData_of_nonneg_of_elementarize hN4 closedTriangle_fibre_nontrivial

theorem endpoint_prime_decomposition_of_sideData_proved
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) :=
  exists_prime_decomposition_of_rawGraphPresentation_of_graphPrimeStructure
    (graphPrimeStructure_of_sideData_proved hN4) M G

theorem endpoint_geometrizes_of_sideData_proved
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂))
    (hgeo : ∀ P : ConnectedClosedOrientedManifold.{u} 3, IsPrime P →
      RawGraphPresentation (NoCuts.carrier P) → Nonempty (GeometricDecomposition P))
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    Geometrizes M :=
  geometrizes_of_rawGraphPresentation_of_graphPrimeStructure
    (graphPrimeStructure_of_sideData_proved hN4) hgeo M G

end GC.GraphManifold

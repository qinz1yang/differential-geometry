import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.LocalRawFaces

/-!
# Chapter-14 assembly, bridge B3: the pure torus assembly to a raw presentation

Lane ASM-B3, group 2 (design §3 B3 last item, draft §(b) B3 last sentence). From regular cut data
whose pieces are recognised as model carriers that carry raw presentations, a raw presentation of
`W`:

1. B3 (`RegularCutData.toTorusPresentation`, `Closure/AssemblyCutSystem.lean`) gives a torus
   presentation of `W` whose component `j` is the piece `j` (`RegularCutData.pieceDiffeomorph`,
   from `EmbeddedCutSystem.pieceDiffeomorph`, `Seifert/EmbeddedPieces.lean:1443`);
2. G1 (`exists_rawGraphPresentation_of_carrierDiffeomorph`,
   `Closure/CarrierDiffeomorphTransport.lean:38`) carries the raw presentation of the model to the
   component, along the model diffeomorphism followed by `pieceDiffeomorph` (the model is connected
   because the piece is);
3. `exists_rawGraphPresentation_of_rawPieces` (`Closure/LocalRawFaces.lean:331`) assembles the raw
   presentations of the components into one of `W`.

Sphere seams are not handled here (they go through L2-relative).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace RegularCutData

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : RegularCutData W E)

/-- A raw presentation of a carrier diffeomorphic to the piece `j` gives one of the component `j`
of the B3 presentation (G1 along the model diffeomorphism followed by `pieceDiffeomorph`). -/
theorem nonempty_rawGraphPresentation_component (j : Fin D.count) {X : CompactCarrier.{u}}
    (G : RawGraphPresentation X) (e : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (D.piece j).Piece) :
    Nonempty (RawGraphPresentation (D.toTorusPresentation.Component j)) := by
  have : ConnectedSpace X.Carrier := e.symm.surjective.connectedSpace e.symm.continuous
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph G (e.trans (D.pieceDiffeomorph j))

end RegularCutData

/-- **Pure torus assembly (B3 → raw).** If every piece of a regular cut is diffeomorphic to a
carrier with a raw presentation, then `W` has a raw presentation. Self-seams are allowed. -/
theorem exists_rawGraphPresentation_of_regularCutData {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} (D : RegularCutData W E)
    (hpiece : ∀ j, ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (D.piece j).Piece)) :
    Nonempty (RawGraphPresentation W) := by
  choose X hG he using hpiece
  exact exists_rawGraphPresentation_of_rawPieces D.toTorusPresentation fun j =>
    (D.nonempty_rawGraphPresentation_component j (hG j).some (he j).some).some

end GC.GraphManifold.Assembly

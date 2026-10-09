import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry

/-!
# Interior geometry transport through actual compact component maps

A whole compact component diffeomorphism restricts to its intrinsic interior. Composing the
native component-interior identifications transports the existing geometry and keeps its model.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u v

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {W' : CompactCarrier.{v}}
  {T : TorusPresentation W} {U : TorusPresentation W'}
  {i : Fin T.components.count} {i' : Fin U.components.count}
  (e : (componentCarrier T.cutCarrier T.components i).Carrier
    ≃ₘ⟮(componentCarrier T.cutCarrier T.components i).model,
      (componentCarrier U.cutCarrier U.components i').model⟯
      (componentCarrier U.cutCarrier U.components i').Carrier)

def componentInteriorTransportDiffeomorph :
    U.cutCarrier.pieceInterior (U.components.piece i') ≃ₘ⟮U.cutCarrier.model,
      T.cutCarrier.model⟯ T.cutCarrier.pieceInterior (T.components.piece i) := by
  let C := componentCarrier T.cutCarrier T.components i
  let D := componentCarrier U.cutCarrier U.components i'
  let et : (⊤ : TopologicalSpace.Opens D.Carrier) ≃ₘ⟮D.model, C.model⟯
      (⊤ : TopologicalSpace.Opens C.Carrier) :=
    (topOpensDiffeomorph (I := D.model) D.Carrier).trans
      (e.symm.trans (topOpensDiffeomorph (I := C.model) C.Carrier).symm)
  exact (componentInteriorDiffeomorph U.cutCarrier U.components i').symm.trans
    ((pieceInteriorCongr et).trans (componentInteriorDiffeomorph T.cutCarrier T.components i))

def transportComponentInteriorGeometry
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i)) :
    U.cutCarrier.InteriorGeometry (U.components.piece i') :=
  transportInteriorGeometry (componentInteriorTransportDiffeomorph e) g

theorem transportComponentInteriorGeometry_model
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i)) :
    letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := Manifold.interiorChartedSpace U.cutCarrier.model ∞
      (M := U.cutCarrier.pieceInterior (U.components.piece i'))
    letI := Manifold.interiorIsManifold U.cutCarrier.model ∞
      (M := U.cutCarrier.pieceInterior (U.components.piece i'))
    (transportComponentInteriorGeometry e g).model = g.model := rfl

include e in
theorem exists_transportComponentHyperbolicGeometry
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i))
    (hg :
      letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
        (M := T.cutCarrier.pieceInterior (T.components.piece i))
      letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
        (M := T.cutCarrier.pieceInterior (T.components.piece i))
      g.model = .hyperbolic) :
    ∃ g' : U.cutCarrier.InteriorGeometry (U.components.piece i'),
      letI := Manifold.interiorChartedSpace U.cutCarrier.model ∞
        (M := U.cutCarrier.pieceInterior (U.components.piece i'))
      letI := Manifold.interiorIsManifold U.cutCarrier.model ∞
        (M := U.cutCarrier.pieceInterior (U.components.piece i'))
      g'.model = .hyperbolic :=
  ⟨transportComponentInteriorGeometry e g,
    (transportComponentInteriorGeometry_model e g).trans hg⟩

end GC.Seifert

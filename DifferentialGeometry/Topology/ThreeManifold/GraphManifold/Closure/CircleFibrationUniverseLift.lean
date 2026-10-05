import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PresentationUniverseLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece

/-!
The actual circle fibration lifts with its base, projection, neighborhoods and original charts.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawUniverseLift

attribute [local instance] uliftChartedSpace isManifold_ulift

abbrev surface (S : CompactSurface.{0}) : CompactSurface.{u} where
  kind := S.kind
  Carrier := ULift.{u} S.Carrier
  charts := uliftChartedSpace (S.kind.Space 2) S.Carrier
  secondCountable := Homeomorph.ulift.isEmbedding.secondCountableTopology
  connected := Homeomorph.ulift.connectedSpace_iff.mpr inferInstance

instance surfaceCharts (S : CompactSurface.{0}) :
    ChartedSpace (S.kind.Space 2) (surface.{u} S).Carrier :=
  (surface S).charts

def surfaceUp (S : CompactSurface.{0}) :
    S.Carrier ≃ₘ⟮S.kind.model 2, S.kind.model 2⟯ (surface.{u} S).Carrier :=
  uliftDiffeomorph (S.kind.model 2) S.Carrier

abbrev surfaceOpenLift (S : CompactSurface.{0}) (V : TopologicalSpace.Opens S.Carrier) :
    TopologicalSpace.Opens (surface.{u} S).Carrier :=
  ⟨ULift.down ⁻¹' V, V.isOpen.preimage continuous_uliftDown⟩

def surfaceOpenDown (S : CompactSurface.{0}) (V : TopologicalSpace.Opens S.Carrier) :
    surfaceOpenLift.{u} S V ≃ₘ⟮S.kind.model 2, S.kind.model 2⟯ V where
  toEquiv := (setDown (V : Set S.Carrier)).toEquiv
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((surfaceUp S).symm.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((surfaceUp S).contMDiff.comp contMDiff_subtype_val)

def fibration (C : CompactCarrier.{0}) (U : TopologicalSpace.Opens C.Carrier)
    (F : CircleFibration C U) : CircleFibration (carrier.{u} C) (openLift C U) where
  base := surface F.base
  projection := ⟨fun x => ULift.up (F.projection (openDown C U x)),
    continuous_uliftUp.comp (F.projection.continuous.comp (openDown C U).continuous)⟩
  surjective := (surfaceUp F.base).surjective.comp
    (F.surjective.comp (openDown C U).surjective)
  smooth := (surfaceUp F.base).contMDiff.comp (F.smooth.comp (openDown C U).contMDiff)
  neighborhood b := surfaceOpenLift F.base (F.neighborhood b.down)
  mem_neighborhood b := F.mem_neighborhood b.down
  trivialization b :=
    ((opensComapDiffeomorph (openDown C U)
      (TopologicalSpace.Opens.comap F.projection (F.neighborhood b.down))).trans
        (F.trivialization b.down)).trans
      ((surfaceOpenDown F.base (F.neighborhood b.down)).symm.prodCongr
        (Diffeomorph.refl (𝓡 1) Circle ∞))
  projection_trivialization b x := by
    change ULift.up (((F.trivialization b.down
      (opensComapDiffeomorph (openDown C U)
        (TopologicalSpace.Opens.comap F.projection (F.neighborhood b.down)) x)).1).val) =
      ULift.up (F.projection (openDown C U x.val))
    congr 1
    exact F.projection_trivialization b.down
      (opensComapDiffeomorph (openDown C U)
        (TopologicalSpace.Opens.comap F.projection (F.neighborhood b.down)) x)

end GC.GraphManifold.RawUniverseLift

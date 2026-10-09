import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksSelected

/-!
# The native compact component of a selected star contraction

The actual selected quotient is the native final component of the selected contraction's
embedded cut system. Its whole compact carrier maps diffeomorphically onto that component.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.SelectedStarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {d : SeifertData}
  (G : SelectedStarGroup T d) (hext : ∀ i, T.externalPiece i ∉ G.set)
  (hk : T.cutCarrier.kind = .withBoundary)

local instance relativeSelectedGroup_charts :
    ChartedSpace (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).kind.Space
      (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).Carrier :=
  (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).charts

local instance relativeSelectedGroup_smooth :
    IsManifold (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).model ∞
      (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).Carrier :=
  (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).smooth

include hext in
private theorem relativeSelectedComplementConnected :
    IsConnected ((Set.univ :
      Set (T.restrictAlongPairing G.set G.selected G.selected_internal).QuotientSpace) \
        ((T.restrictAlongPairing G.set G.selected G.selected_internal).quotientMap ''
          (T.restrictAlongBoundaryTori G.set G.selected).image)) :=
  T.restrictAlong_hconn_complement G.set G.selected G.selected_internal hext
    (G.relativeSelected_interior_connected hext)

private def relativeSelectedNativeDiffeomorph (a : Fin G.setᶜ.card ⊕ Unit)
    (ha : a = .inr ()) :
    (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).Carrier ≃ₘ⟮
      (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).model,
      CarrierModel.withBoundary.model⟯
      (T.alongPieceGeometry G.set G.selected G.selected_internal hext hk
        (G.relativeSelectedComplementConnected hext) a).Carrier := by
  subst a
  exact Diffeomorph.refl _ _ ∞

private theorem relativeSelectedNativeDiffeomorph_map (a : Fin G.setᶜ.card ⊕ Unit)
    (ha : a = .inr ())
    (x : (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).Carrier) :
    (T.alongPieceGeometry G.set G.selected G.selected_internal hext hk
      (G.relativeSelectedComplementConnected hext) a).map
      (G.relativeSelectedNativeDiffeomorph hext hk a ha x) =
      T.restrictAlongMap G.set G.selected G.selected_internal x := by
  subst a
  rfl

private theorem relativeSelectedNativeCount (a : Fin G.setᶜ.card ⊕ Unit)
    (ha : a = .inr ()) :
    (T.alongPieceGeometry G.set G.selected G.selected_internal hext hk
      (G.relativeSelectedComplementConnected hext) a).torusCount =
      (G.restrictBlock hext).presentation.externalCount := by
  subst a
  rfl

private def relativeSelectedNativePort (a : Fin G.setᶜ.card ⊕ Unit)
    (ha : a = .inr ()) : Fin (G.restrictBlock hext).presentation.externalCount ≃
      Fin ((T.alongPieceGeometry G.set G.selected G.selected_internal hext hk
        (G.relativeSelectedComplementConnected hext) a).torusCount) :=
  finCongr (G.relativeSelectedNativeCount hext hk a ha).symm

private theorem relativeSelectedNativeDiffeomorph_collar (a : Fin G.setᶜ.card ⊕ Unit)
    (ha : a = .inr ()) (r : Fin (G.restrictBlock hext).presentation.externalCount)
    (p : Torus × EuclideanHalfSpace 1) :
    G.relativeSelectedNativeDiffeomorph hext hk a ha
      ((G.restrictBlock hext).presentation.external.collar r p) =
      (T.alongPieceGeometry G.set G.selected G.selected_internal hext hk
        (G.relativeSelectedComplementConnected hext) a).collar
          (G.relativeSelectedNativePort hext hk a ha r) p := by
  subst a
  rfl

private theorem relativeSelectedLastGeometry :
    (T.alongGeometryIndexEquiv G.set).symm (Fin.last G.setᶜ.card) = .inr () :=
  (T.alongGeometryIndexEquiv G.set).symm_apply_eq.mpr rfl

def relativeSelectedGroupDiffeomorph :
    (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).Carrier ≃ₘ⟮
      (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).model,
      (componentCarrier (G.relativeSelectedContraction hext hk).cutCarrier
        (G.relativeSelectedContraction hext hk).components (Fin.last G.setᶜ.card)).model⟯
      (componentCarrier (G.relativeSelectedContraction hext hk).cutCarrier
        (G.relativeSelectedContraction hext hk).components (Fin.last G.setᶜ.card)).Carrier :=
  (G.relativeSelectedNativeDiffeomorph hext hk _ G.relativeSelectedLastGeometry).trans
    ((T.alongCutSystem G.set G.selected G.selected_internal hext hk
      (G.relativeSelectedComplementConnected hext)).pieceDiffeomorph (Fin.last G.setᶜ.card))

theorem relativeSelectedGroupDiffeomorph_cutMap
    (x : (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).Carrier) :
    (G.relativeSelectedContraction hext hk).cutMap
      (G.relativeSelectedGroupDiffeomorph hext hk x).val =
      T.restrictAlongMap G.set G.selected G.selected_internal x :=
  G.relativeSelectedNativeDiffeomorph_map hext hk _ _ x

theorem relativeSelectedGroupDiffeomorph_oriented :
    letI := (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).charts
    letI := (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).smooth
    (G.relativeSelectedGroupDiffeomorph hext hk).preservesOrientation
      (T.restrictAlongCarrier G.set G.selected G.selected_internal hext).orientation
      (componentCarrier (G.relativeSelectedContraction hext hk).cutCarrier
        (G.relativeSelectedContraction hext hk).components
        (Fin.last G.setᶜ.card)).orientation := by
  let C := T.restrictAlongCarrier G.set G.selected G.selected_internal hext
  let : ChartedSpace C.kind.Space C.Carrier := C.charts
  let : IsManifold C.model ∞ C.Carrier := C.smooth
  let U := G.relativeSelectedContraction hext hk
  let F := T.restrictAlongMap G.set G.selected G.selected_internal
  have hF : IsOrientedFold (W := W) (C := C) F := by
    intro x
    refine ⟨(Manifold.differentialEquivOfBijective C.model W.model F
      (T.mfderiv_restrictAlongMap_bijective G.set G.selected G.selected_internal hext)
      x).toLinearEquiv, fun v => rfl, ?_⟩
    exact Manifold.orientation_map_manifoldOrientationPullback C.model W.model
      finrank_euclideanSpace_fin F
      (T.contMDiff_restrictAlongMap G.set G.selected G.selected_internal hext)
      (T.mfderiv_restrictAlongMap_bijective G.set G.selected G.selected_internal hext)
      W.orientation x
  apply preservesOrientation_of_comp (G.relativeSelectedGroupDiffeomorph hext hk) F
    (U.cutMap ∘ Subtype.val) (oM := C.orientation)
    (oN := (componentCarrier U.cutCarrier U.components (Fin.last G.setᶜ.card)).orientation)
    (O := W.orientation)
  · intro y
    exact (U.quotient_smooth.comp contMDiff_subtype_val).mdifferentiableAt (by simp)
  · exact G.relativeSelectedGroupDiffeomorph_cutMap hext hk
  · exact hF
  · exact U.isOrientedFold_cutMap.restrict U.quotient_smooth _

def relativeSelectedGroupPort : Fin (G.restrictBlock hext).presentation.externalCount ≃
    (G.relativeSelectedContraction hext hk).OwnedSide (Fin.last G.setᶜ.card) :=
  (G.relativeSelectedNativePort hext hk _ G.relativeSelectedLastGeometry).trans
    ((T.alongCutSystem G.set G.selected G.selected_internal hext hk
      (G.relativeSelectedComplementConnected hext)).port (Fin.last G.setᶜ.card))

theorem relativeSelectedGroupDiffeomorph_collar
    (r : Fin (G.restrictBlock hext).presentation.externalCount)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    G.relativeSelectedGroupDiffeomorph hext hk
      ((G.restrictBlock hext).presentation.external.collar r p) =
      (G.relativeSelectedContraction hext hk).pieceCollar (Fin.last G.setᶜ.card)
        (G.relativeSelectedGroupPort hext hk r) p := by
  let A := T.alongCutSystem G.set G.selected G.selected_internal hext hk
    (G.relativeSelectedComplementConnected hext)
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
  change _ = A.toTorusPresentation.sideCollar
    (A.port (Fin.last G.setᶜ.card)
      (G.relativeSelectedNativePort hext hk _ G.relativeSelectedLastGeometry r)).val p
  rw [A.sideCollar_eq, A.sideOf_port, A.sideCollar_apply]
  exact congrArg (Sigma.mk (Fin.last G.setᶜ.card))
    (G.relativeSelectedNativeDiffeomorph_collar hext hk _ _ r p)

def relativeSelectedGroupBlock : PieceBlock (G.relativeSelectedContraction hext hk)
    (Fin.last G.setᶜ.card) where
  data := d
  block := (G.restrictBlock hext).transport (G.relativeSelectedGroupDiffeomorph hext hk)
    (G.relativeSelectedGroupDiffeomorph_oriented hext hk)
  port := G.relativeSelectedGroupPort hext hk
  collar_eq r p hp := G.relativeSelectedGroupDiffeomorph_collar hext hk r p hp

end GC.Seifert.SelectedStarGroup

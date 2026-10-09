import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminalSelfSeam
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationContract

/-!
# Actual selected star contractions for relative terminal blocks

The actual local Seifert block of a selected star gives connectedness of the selected quotient
and its interior. Contracting precisely its arm seams retains every omitted signed seam and
matching, including self seams of the host, and every original external half collar. The
resulting reconstruction square uses the actual map of cut points.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.SelectedStarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {d : SeifertData}
  (G : SelectedStarGroup T d) (hext : ∀ i, T.externalPiece i ∉ G.set)

theorem relativeSelected_interior_connected :
    IsConnected ((T.restrictAlongCarrier G.set G.selected G.selected_internal hext).interior :
      Set (T.restrictAlongPairing G.set G.selected G.selected_internal).QuotientSpace) := by
  let C := T.restrictAlongCarrier G.set G.selected G.selected_internal hext
  let : ChartedSpace (EuclideanHalfSpace 3) C.Carrier := C.charts
  let : IsManifold C.model ∞ C.Carrier := C.smooth
  let : ConnectedSpace C.Carrier := (G.restrictBlock hext).connectedSpace
  exact ⟨Manifold.dense_manifold_interior.nonempty,
    Manifold.isPreconnected_manifold_interior⟩

variable (hk : T.cutCarrier.kind = .withBoundary)

def relativeSelectedContraction : TorusPresentation W :=
  T.contractAlong G.set G.selected G.selected_internal hext hk
    (G.relativeSelected_interior_connected hext)

def relativeSelectedSeamEquiv : T.AlongUnpairedSeam G.selected ≃
    Fin (G.relativeSelectedContraction hext hk).pairing.count :=
  T.contractAlongRetainedSeamEquiv G.set G.selected G.selected_internal hext hk
    (G.relativeSelected_interior_connected hext)

theorem relativeSelected_seam (a : T.AlongUnpairedSeam G.selected) :
    (G.relativeSelectedContraction hext hk).seam
      (G.relativeSelectedSeamEquiv hext hk a) = T.seam a.val :=
  T.contractAlong_retained_seam G.set G.selected G.selected_internal hext hk
    (G.relativeSelected_interior_connected hext) a

theorem relativeSelected_matching (a : T.AlongUnpairedSeam G.selected) :
    (G.relativeSelectedContraction hext hk).pairing.matching
      (G.relativeSelectedSeamEquiv hext hk a) = T.pairing.matching a.val :=
  T.contractAlong_retained_matching G.set G.selected G.selected_internal hext hk
    (G.relativeSelected_interior_connected hext) a

theorem relativeSelected_externalCount :
    (G.relativeSelectedContraction hext hk).externalCount = T.externalCount := rfl

theorem relativeSelected_external_collar (r : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (G.relativeSelectedContraction hext hk).external.collar r p = T.external.collar r p :=
  T.contractAlong_retained_external_collar G.set G.selected G.selected_internal hext hk
    (G.relativeSelected_interior_connected hext) r hp

theorem relativeSelected_reconstruction (x : T.cutCarrier.Carrier) :
    (G.relativeSelectedContraction hext hk).reconstruction
      ((G.relativeSelectedContraction hext hk).pairing.quotientMap
        (T.contractAlongMap G.set G.selected G.selected_internal hext hk
          (G.relativeSelected_interior_connected hext) x)) =
      T.reconstruction (T.pairing.quotientMap x) :=
  T.contractAlong_retained_reconstruction G.set G.selected G.selected_internal hext hk
    (G.relativeSelected_interior_connected hext) x

end GC.Seifert.SelectedStarGroup

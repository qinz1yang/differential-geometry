import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEdgeCircle

/-!
# FC39 GROUP G, RIMBOX: the edge layer and its component link (consumer of the edge-circle pieces)

Lane FC39-RIMBOX-ROUND, D62-5, for the G8 assembly. Interval handles carrying the four link clauses
(`handle_whole`, `handle_proj`, `handle_disk`, `handle_rim` — the new flow handles of route B) together
with the edge-circle pieces `edgeCirclePiece_of_circleTriv_GRND` form an edge layer
(`EdgeComponentModels.edgeLayer_GRND`) with an `EdgeComponentsLink` whose index bijections are the
identities (`EdgeComponentModels.edgeComponentsLink_GRND`, frozen form
`EdgeComponentModels.exists_edgeComponentsLink_GRND`). Consumer: the export's own interval products
(`intervalTriv`) give such a link (`EdgeComponentModels.nonempty_edgeComponentsLink_intervalTriv_GRND`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- The edge layer of given interval handles and the edge-circle pieces of the export. -/
def EdgeComponentModels.edgeLayer_GRND {P : EdgeBundle W} (M : EdgeComponentModels P)
    (Hd : Fin M.intervalCount → EdgeHandle W) : EdgeLayer W :=
  ⟨M.intervalCount, Hd, M.circleCount, M.edgeCirclePiece_of_circleTriv_GRND⟩

/-- **The component link** of interval handles with their four link clauses and the edge-circle
pieces (index bijections = identities). -/
def EdgeComponentModels.edgeComponentsLink_GRND {P : EdgeBundle W} (M : EdgeComponentModels P)
    (Hd : Fin M.intervalCount → EdgeHandle W)
    (hwhole : ∀ i, range (Hd i).map = P.wholeComponent (M.componentEquiv (.inl i)))
    (hproj : ∀ i w t, ∃ hx : (Hd i).map (w, t) ∈ P.source,
      P.proj ⟨(Hd i).map (w, t), hx⟩ = M.intervalBase i t)
    (hdisk : ∀ i t, range (fun w => (Hd i).map (w, t)) = P.disk (M.intervalBase i t))
    (hrim : ∀ i t, (fun w => (Hd i).map (w, t)) '' diskRim = P.rim (M.intervalBase i t)) :
    EdgeComponentsLink P M (M.edgeLayer_GRND Hd) where
  handleEquiv := Equiv.refl _
  circleEquiv := Equiv.refl _
  handle_whole := hwhole
  circle_whole := M.edgeCirclePiece_whole_GRND
  handle_proj := hproj
  handle_disk := hdisk
  handle_rim := hrim
  circle_proj := M.edgeCirclePiece_proj_GRND
  circle_disk := M.edgeCirclePiece_disk_GRND
  circle_rim := M.edgeCirclePiece_rim_GRND

/-- **E7 (frozen form).** New interval handles with their four link clauses and the edge-circle
pieces give the edge layer and its `EdgeComponentsLink` (`handleEquiv`, `circleEquiv` = id). -/
theorem EdgeComponentModels.exists_edgeComponentsLink_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (Hd : Fin M.intervalCount → EdgeHandle W)
    (hwhole : ∀ i, range (Hd i).map = P.wholeComponent (M.componentEquiv (.inl i)))
    (hproj : ∀ i w t, ∃ hx : (Hd i).map (w, t) ∈ P.source,
      P.proj ⟨(Hd i).map (w, t), hx⟩ = M.intervalBase i t)
    (hdisk : ∀ i t, range (fun w => (Hd i).map (w, t)) = P.disk (M.intervalBase i t))
    (hrim : ∀ i t, (fun w => (Hd i).map (w, t)) '' diskRim = P.rim (M.intervalBase i t)) :
    ∃ L : EdgeComponentsLink P M
        ⟨M.intervalCount, Hd, M.circleCount, M.edgeCirclePiece_of_circleTriv_GRND⟩,
      (∀ h, L.handleEquiv h = h) ∧ ∀ j, L.circleEquiv j = j :=
  ⟨M.edgeComponentsLink_GRND Hd hwhole hproj hdisk hrim, fun _ => rfl, fun _ => rfl⟩

/-- **Consumer.** The export's own interval products and the edge-circle pieces form an edge layer
with a component link. -/
theorem EdgeComponentModels.nonempty_edgeComponentsLink_intervalTriv_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) :
    Nonempty (EdgeComponentsLink P M (M.edgeLayer_GRND M.intervalTriv)) :=
  ⟨M.edgeComponentsLink_GRND M.intervalTriv M.intervalTriv_range M.intervalTriv_proj
    M.intervalTriv_disk M.intervalTriv_rim⟩

end GC.GraphManifold.Assembly.FC39P0

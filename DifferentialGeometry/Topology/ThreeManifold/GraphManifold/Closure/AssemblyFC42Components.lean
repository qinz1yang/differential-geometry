import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

/-!
# FC42 piece B3: every nonempty compact carrier has a component decomposition

The L2 theorems (`exists_rawGraphPresentation_of_sphereCut_nonseparating` / `_separating`, V2) take
`DQ : X.Q.Components` as an input, and the tree builds `Components` only for concrete carriers.
`nonempty_components_of_nonempty` builds one for any compact carrier with a point: the pieces are
the connected components (open, by local connectedness of a manifold; finitely many, by
compactness), each piece is connected, and so is its interior (`isPreconnected_manifold_interior`
on the piece, `Topology/Manifold/ConnectedInterior.lean`).

Deviation from the FC42 dry stub `dry_exists_components` (`Nonempty Q.Components` for every
compact carrier): the hypothesis `[Nonempty Q.Carrier]` is added. The stub is false for the empty
carrier, because `Components.count_pos` and `Components.connected` force a point.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The interior of a connected open piece of a carrier is connected. -/
theorem connectedSpace_pieceInterior_of_connectedSpace (Q : CompactCarrier.{u})
    (U : TopologicalSpace.Opens Q.Carrier) (hc : ConnectedSpace U) :
    ConnectedSpace (Q.pieceInterior U) := by
  have he : (Q.pieceInterior U : Set Q.Carrier) = Q.model.interior Q.Carrier ∩ U := by
    ext x
    exact and_comm
  apply isConnected_iff_connectedSpace.mp
  rw [he]
  have hp : IsPreconnected (U : Set Q.Carrier) :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  obtain ⟨x, hx⟩ := (DifferentialGeometry.Topology.Manifold.dense_manifold_interior
    (I := Q.model) (M := U)).nonempty
  exact ⟨⟨x.val, Q.model.isInteriorPoint_iff_isInteriorPoint_val.mp hx, x.property⟩,
    DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior_inter_open U hp⟩

/-- A carrier is locally connected (it is a manifold). -/
theorem locallyConnectedSpace_carrier (Q : CompactCarrier.{u}) :
    LocallyConnectedSpace Q.Carrier := by
  let _ : LocallyPathConnectedSpace (range Q.model) :=
    Q.model.convex_range.locallyPathConnectedSpace
  let _ : LocallyConnectedSpace Q.kind.Space :=
    Q.model.isClosedEmbedding.isEmbedding.toHomeomorph.locallyConnectedSpace
  exact ChartedSpace.locallyConnectedSpace Q.kind.Space Q.Carrier

/-- The connected component of a point as an open set of the carrier. -/
def carrierComponentOpens (Q : CompactCarrier.{u}) (x : Q.Carrier) : TopologicalSpace.Opens Q.Carrier :=
  let _ : LocallyConnectedSpace Q.Carrier := locallyConnectedSpace_carrier Q
  ⟨connectedComponent x, isOpen_connectedComponent⟩

/-- **B3.** A compact carrier with a point has a component decomposition (its connected
components). -/
theorem nonempty_components_of_nonempty (Q : CompactCarrier.{u}) [Nonempty Q.Carrier] :
    Nonempty Q.Components := by
  let _ : LocallyConnectedSpace Q.Carrier := locallyConnectedSpace_carrier Q
  let e := Finite.equivFin (ConnectedComponents Q.Carrier)
  let rep : Fin (Nat.card (ConnectedComponents Q.Carrier)) → Q.Carrier := fun i =>
    (ConnectedComponents.surjective_coe (e.symm i)).choose
  have hrep : ∀ i, ((rep i : Q.Carrier) : ConnectedComponents Q.Carrier) = e.symm i := fun i =>
    (ConnectedComponents.surjective_coe (e.symm i)).choose_spec
  have hmem : ∀ x : Q.Carrier, x ∈ connectedComponent (rep (e x)) := by
    intro x
    have h : ((rep (e x) : Q.Carrier) : ConnectedComponents Q.Carrier) = x := by
      rw [hrep, Equiv.symm_apply_apply]
    exact connectedComponent_eq_iff_mem.mp (ConnectedComponents.coe_eq_coe.mp h).symm
  have hconn : ∀ i, ConnectedSpace (carrierComponentOpens Q (rep i)) := fun i =>
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  refine ⟨{
    count := Nat.card (ConnectedComponents Q.Carrier)
    count_pos := Nat.card_pos
    piece := fun i => carrierComponentOpens Q (rep i)
    closed := fun i => isClosed_connectedComponent
    connected := hconn
    disjoint := ?_
    covers := ?_
    interior_connected := fun i =>
      connectedSpace_pieceInterior_of_connectedSpace Q _ (hconn i) }⟩
  · intro i j hij
    change Disjoint (connectedComponent (rep i)) (connectedComponent (rep j))
    refine connectedComponent_disjoint fun h => hij ?_
    have h' : ((rep i : Q.Carrier) : ConnectedComponents Q.Carrier) = rep j :=
      ConnectedComponents.coe_eq_coe.mpr h
    rw [hrep, hrep] at h'
    exact e.symm.injective h'
  · exact eq_univ_of_forall fun x => mem_iUnion.mpr ⟨e x, hmem x⟩

/-- Every piece of the decomposition of `nonempty_components_of_nonempty` is a connected component;
in general, every piece of any `Components` is a union of connected components (clopen), so it
contains the component of each of its points. -/
theorem Components.connectedComponent_subset_piece {Q : CompactCarrier.{u}} (D : Q.Components)
    (i : Fin D.count) {x : Q.Carrier} (hx : x ∈ (D.piece i : Set Q.Carrier)) :
    connectedComponent x ⊆ D.piece i :=
  (IsClopen.connectedComponent_subset ⟨D.closed i, (D.piece i).isOpen⟩ hx)

end GC.GraphManifold.Assembly

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Corners

/-!
# FC39 producer, packet P0 (gate 1), §8: `AdaptedEdgeRimData` (fields now, existence at gate 2)

Task-47 draft §8 (disposition D11). The joint output of G1 / RIMBOX-1: the producer CHOOSES the
edge layer, the circle region (normalized corners and rounding) and the rim charts together, with
the component registration, the restriction link, the labelled corner compatibility, the rim
product at every rim and the support control inside prescribed safe neighbourhoods.

* `ProducerSafeNeighbourhoods` — optional open neighbourhoods of the original compact sets, chosen
  BEFORE the final layers (never the final `ProtectionLayer` as a premise): a safe neighbourhood per
  shared face (`SharedSafe`) and a saturated safe tube per actual endpoint circle, inside the raw
  labelled tube, around the rim base point, with pairwise disjoint closures avoiding the external
  collars and the shared-face neighbourhoods;
* `AdaptedEdgeRimData` — the fields of §8 (the two `*_eq` fields forbid two registrations).

Existence is the gate-2 target `stub_exists_adaptedEdgeRimData` (`Targets.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **§8 Prescribed safe neighbourhoods of the producer.** -/
structure ProducerSafeNeighbourhoods (Rw : FC39RowsV2 W E) where
  shared : Rw.SharedFace → TopologicalSpace.Opens W.Carrier
  shared_safe : SharedSafe Rw shared
  cornerBase : Rw.edge.EdgeEnd → TopologicalSpace.Opens Rw.circle.Base
  cornerBase_sub : ∀ e, (cornerBase e : Set Rw.circle.Base) ⊆ Rw.labelledTubes.base e
  rimBase_mem : ∀ e, Rw.junctions.rimBase e.1 ∈ cornerBase e
  corner_closure_disjoint : Pairwise fun e e' =>
    Disjoint (closure (Rw.circle.tube (cornerBase e))) (closure (Rw.circle.tube (cornerBase e')))
  corner_off_external : ∀ e i,
    Disjoint (closure (Rw.circle.tube (cornerBase e))) (E.collar i).target
  corner_off_shared : ∀ e σ,
    Disjoint (closure (Rw.circle.tube (cornerBase e))) (closure (shared σ : Set W.Carrier))

/-- The saturated safe tube of an endpoint circle. -/
def ProducerSafeNeighbourhoods.corner {Rw : FC39RowsV2 W E} (safe : ProducerSafeNeighbourhoods Rw)
    (e : Rw.edge.EdgeEnd) : Set W.Carrier :=
  Rw.circle.tube (safe.cornerBase e)

/-- **§8 The joint adapted edge–rim data.** -/
structure AdaptedEdgeRimData (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) where
  edges : EdgeLayer W
  circ : CircleRegion W
  components : EdgeComponentsLink Pr.rows.edge Pr.rows.edgeModels edges
  circle : CircleRestrictionLink Pr.rows.circle circ
  rims : RimChartLayer W edges circ
  labelled : LabelledCornerCompatibility Pr edges circ rims
  components_eq : labelled.edgeLink = components
  circle_eq : labelled.circleLink = circle
  product : ∀ h b, RimProductAt (rims.rimChart h b) (edges.handle h) b
  rim_closure_in_safe : ∀ h b,
    closure (rims.rimChart h b).target ⊆ safe.corner (labelled.edgeLink.endOfHandle h b)
  rounding_in_safe :
    Subtype.val '' (circ.proj ⁻¹' symmDiff {c | circ.rounding c ≤ 0} circ.cornerBase) ⊆
      ⋃ e, safe.corner e

/-- The rim targets lie in the safe tubes (derived from the closure containment). -/
theorem AdaptedEdgeRimData.rim_in_safe {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.rims.rimChart h b).target ⊆ safe.corner (A.labelled.edgeLink.endOfHandle h b) :=
  subset_closure.trans (A.rim_closure_in_safe h b)

end GC.GraphManifold.Assembly.FC39P0

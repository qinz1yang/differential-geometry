import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Adapted
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2

/-!
# FC39 GROUP G: the joint adapted edge–rim data over the prepared rows V2

Lane FC39-G-GFF, D58-1: the structure `AdaptedEdgeRimData` (§8) is indexed by the prepared rows;
its V2 form `AdaptedEdgeRimDataV2 Pr safe` (`Pr : FC39PreparedV2 W E`) has the same fields, with the
labelled corner compatibility `LabelledCornerCompatibilityV2`. The safe neighbourhoods
`ProducerSafeNeighbourhoods Pr.rows` read only the raw rows and are unchanged.

* `AdaptedEdgeRimData.toV2` — every old adapted package is a V2 one over `Pr.toV2` (all fields the
  old ones; `labelled := A.labelled.toV2`);
* `AdaptedEdgeRimDataV2.rim_in_safe` — the rim targets lie in the safe tubes.
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

/-- **§8 The joint adapted edge–rim data over the prepared rows V2.** -/
structure AdaptedEdgeRimDataV2 (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) where
  edges : EdgeLayer W
  circ : CircleRegion W
  components : EdgeComponentsLink Pr.rows.edge Pr.rows.edgeModels edges
  circle : CircleRestrictionLink Pr.rows.circle circ
  rims : RimChartLayer W edges circ
  labelled : LabelledCornerCompatibilityV2 Pr edges circ rims
  components_eq : labelled.edgeLink = components
  circle_eq : labelled.circleLink = circle
  product : ∀ h b, RimProductAt (rims.rimChart h b) (edges.handle h) b
  rim_closure_in_safe : ∀ h b,
    closure (rims.rimChart h b).target ⊆ safe.corner (labelled.edgeLink.endOfHandle h b)
  rounding_in_safe :
    Subtype.val '' (circ.proj ⁻¹' symmDiff {c | circ.rounding c ≤ 0} circ.cornerBase) ⊆
      ⋃ e, safe.corner e

/-- The rim targets lie in the safe tubes (derived from the closure containment). -/
theorem AdaptedEdgeRimDataV2.rim_in_safe {Pr : FC39PreparedV2 W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.rims.rimChart h b).target ⊆ safe.corner (A.labelled.edgeLink.endOfHandle h b) :=
  subset_closure.trans (A.rim_closure_in_safe h b)

/-- **Every old adapted package is a V2 one** over `Pr.toV2` (forgetful map; all fields the old
ones). -/
def AdaptedEdgeRimData.toV2 {Pr : FC39Prepared W E} {safe : ProducerSafeNeighbourhoods Pr.rows}
    (A : AdaptedEdgeRimData Pr safe) : AdaptedEdgeRimDataV2 Pr.toV2 safe where
  edges := A.edges
  circ := A.circ
  components := A.components
  circle := A.circle
  rims := A.rims
  labelled := A.labelled.toV2
  components_eq := A.components_eq
  circle_eq := A.circle_eq
  product := A.product
  rim_closure_in_safe := A.rim_closure_in_safe
  rounding_in_safe := A.rounding_in_safe

@[simp] theorem AdaptedEdgeRimData.toV2_edges {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe) :
    A.toV2.edges = A.edges :=
  rfl

@[simp] theorem AdaptedEdgeRimData.toV2_circ {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe) :
    A.toV2.circ = A.circ :=
  rfl

theorem AdaptedEdgeRimData.toV2_rims {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe) :
    A.toV2.rims = A.rims :=
  rfl

theorem AdaptedEdgeRimData.toV2_labelled {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe) :
    A.toV2.labelled = A.labelled.toV2 :=
  rfl

end GC.GraphManifold.Assembly.FC39P0

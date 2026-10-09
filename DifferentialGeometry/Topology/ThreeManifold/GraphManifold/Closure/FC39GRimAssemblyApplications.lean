import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAssembly

/-!
# FC39 GROUP G, RIMBOX (G8): consumers of the adapted edge–rim data

Lane FC39-G-RIMBOXc.

* `exists_adaptedEdgeRimDataV2_of_prepared_GRIM` — the V1 prepared rows (`FC39Prepared.toV2`) also carry
  adapted edge–rim data V2;
* `exists_adaptedEdgeRimDataV2_rim_in_safe_GRIM` — for the produced data every rim-chart target lies in
  the safe tube of its endpoint and the rounded / cornered base differ only inside the safe tubes.
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

/-- The V1 prepared rows carry adapted edge–rim data V2 over their forgetful image. -/
theorem exists_adaptedEdgeRimDataV2_of_prepared_GRIM (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) : Nonempty (AdaptedEdgeRimDataV2 Pr.toV2 safe) :=
  exists_adaptedEdgeRimDataV2_GRIM Pr.toV2 safe

/-- The produced data keep every rim target inside the safe tube of its endpoint, and the rounding
inside the safe tubes. -/
theorem exists_adaptedEdgeRimDataV2_rim_in_safe_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) :
    ∃ A : AdaptedEdgeRimDataV2 Pr safe,
      (∀ h b, (A.rims.rimChart h b).target ⊆ safe.corner (A.labelled.edgeLink.endOfHandle h b)) ∧
      Subtype.val '' (A.circ.proj ⁻¹' symmDiff {c | A.circ.rounding c ≤ 0} A.circ.cornerBase) ⊆
        ⋃ e, safe.corner e := by
  obtain ⟨A⟩ := exists_adaptedEdgeRimDataV2_GRIM Pr safe
  exact ⟨A, A.rim_in_safe, A.rounding_in_safe⟩

end GC.GraphManifold.Assembly.FC39P0

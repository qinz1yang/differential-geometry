import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalLanding

/-!
# X143: derived edge-circle fibre compatibility

Review 73 D73-4: derive whole-fibre equality from the existing component, junction and
circle-restriction links, for the pointwise GFIN witness, with no new producer premise.
-/
set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold.Assembly

/-- Each boundary circle of an edge-circle fibre is a whole fibre of the same circle region. -/
def DecompositionCertificate.EdgeCircleFibreCompatible
    {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) : Prop :=
  ∀ e (z : Circle), ∃ b : D.circ.Base,
    (D.edgeCircle e).piece.map ''
        {q | (𝓡∂ 3).IsBoundaryPoint q ∧ (D.edgeCircle e).proj q = z} =
      Subtype.val '' (D.circ.proj ⁻¹' {b})

namespace FC39P0

/-- No additional producer hypothesis: whole rims and the existing restriction link suffice. -/
theorem strongCertificateOfAdapted_GFIN_edgeCircleFibreCompatible
    {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows)
    (A : AdaptedEdgeRimDataV2 Pr safe) :
    (strongCertificateOfAdapted_GFIN Pr safe A).1.EdgeCircleFibreCompatible := by
  change ∀ e : Fin A.edges.edgeCircleCount, ∀ z : Circle,
    ∃ b : A.circ.Base, (A.edges.edgeCircle e).piece.map ''
    {q | (𝓡∂ 3).IsBoundaryPoint q ∧ (A.edges.edgeCircle e).proj q = z} =
      Subtype.val '' (A.circ.proj ⁻¹' {b})
  intro e z
  let c := Pr.rows.edgeModels.circleBase (A.components.circleEquiv e) z
  have hc : c ∈ Pr.rows.edge.cbase := by
    apply ActualComponent.subset
    rw [← Pr.rows.edgeModels.circleBase_range]
    exact mem_range_self z
  obtain ⟨x, hx⟩ := Pr.rows.circle.fibre_nonempty_GCVP (Pr.rows.junctions.rimBase c)
  have hxr : x ∈ Pr.rows.edge.rim c := by
    rw [Pr.rows.junctions.rim_fibre c hc]
    exact hx
  have hxd : x ∈ (A.circ.domain : Set W.Carrier) := by
    apply A.circ.region_subset_domain
    rw [A.circle.region_eq]
    exact Pr.rows.vertical_subset_region_GCVP
      (Pr.rows.edge.rim_subset_vertical_GCVP hc hxr)
  obtain ⟨b, hb⟩ := A.circle.exists_fibre_eq_GCVP hx hxd
  refine ⟨b, ?_⟩
  have hr : (A.edges.edgeCircle e).piece.map ''
      {q | (𝓡∂ 3).IsBoundaryPoint q ∧ (A.edges.edgeCircle e).proj q = z} =
        Pr.rows.edge.rim c := by
    simpa only [and_comm] using A.components.circle_rim e z
  rw [hr, Pr.rows.junctions.rim_fibre c hc]
  exact hb.symm

end FC39P0
end GC.GraphManifold.Assembly

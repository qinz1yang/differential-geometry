import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkKernel74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonRows

/-!
# Inhabitants of the D74-5 link tables (`RowsLinkKernel74`)

Lane S-LANDING (`_LND74`), G1 consumer. The five plain-data tables of `RowsLinkKernel74` hold,
with `ψ = id`, on the two X136 singleton configurations `configurationRows b`:

* `b = false`: the round `S³` with ONE zero domain covering the carrier (closed zero model),
  empty slim / edge / circle families (the stage families are empty);
* `b = true`: `S² × S¹` with no zero domain and ONE slim piece covering the carrier, empty edge /
  circle families (a NON-empty slim table).

Every table (zero, slim, edge, circle, regions) is inhabited, with the actual-side data chosen as
the carrier itself (`dom = univ`, `inner = ∅`, `outer = univ`); the equivalences of indices are the
identities of `Fin 1` / `Fin 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- The zero table on the singleton configurations. -/
theorem zeroLink_configuration_LND74 (b : Bool) :
    ∃ (ι : Type) (dom inner outer : ι → Set (configurationW b).Carrier)
      (uv : ι → (configurationW b).Carrier → ℝ),
      ZeroLink_LND74 (Equiv.refl _) (configurationRows b).zero dom inner outer uv := by
  cases b
  · refine ⟨Fin 1, fun _ => univ, fun _ => ∅, fun _ => univ,
      fun _ => wholeFunction standardThreeSphere, finCongr rfl, fun i => ?_⟩
    refine ⟨?_, ?_, by simp, by simp, fun x _ => rfl, ?_⟩
    · ext x
      refine ⟨fun _ => ⟨x, mem_univ x, rfl⟩, fun _ => ?_⟩
      have h := Set.ext_iff.1 zeroClosedPiece_cover x
      exact h.2 (mem_univ x)
    · change (wholePiece standardThreeSphere).map '' (𝓡∂ 3).boundary
        (wholePiece standardThreeSphere).Piece = _
      rw [wholePiece_boundary, image_empty, frontier_univ, image_empty]
      rfl
    · exact ⟨wholeFunction standardThreeSphere, univ, isOpen_univ, subset_univ _,
        fun _ _ => rfl, fun _ => rfl⟩
  · exact ⟨Fin 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      finCongr rfl, fun i => i.elim0⟩

/-- The slim table on the singleton configurations (`b = true`: one slim piece covering `W`). -/
theorem slimLink_configuration_LND74 (b : Bool) :
    ∃ (κ : Type) (comp : κ → Set (configurationW b).Carrier)
      (slimSet : Set (configurationW b).Carrier),
      SlimLink_LND74 (Equiv.refl _) (configurationRows b).slim comp slimSet := by
  cases b
  · refine ⟨Fin 0, fun k => k.elim0, ∅, ?_, finCongr rfl, fun j => j.elim0⟩
    rw [image_empty]
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨j, -⟩ := mem_iUnion.1 hx
    exact j.elim0
  · refine ⟨Fin 1, fun _ => univ, univ, ?_, finCongr rfl, fun j => ?_⟩
    · have h := Set.ext_iff.1 slimPieces_union
      ext x
      refine ⟨fun _ => ⟨x, mem_univ x, rfl⟩, fun _ => ?_⟩
      exact (h x).2 (mem_univ x)
    · have h := Set.ext_iff.1 (wholePiece_range sphereTwoTimesCircleLift)
      ext x
      refine ⟨fun _ => ⟨x, mem_univ x, rfl⟩, fun _ => ?_⟩
      exact (h x).2 (mem_univ x)

/-- The edge table (the edge family is empty). -/
theorem edgeLink_configuration_LND74 (b : Bool) :
    EdgeLink_LND74 (Equiv.refl (configurationW b).Carrier) (configurationRows b).edge
      (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 ∅ ∅ ∅ ∅ := by
  have : IsEmpty (configurationRows b).edge.Base := ⟨fun c => c.elim⟩
  have hcb : (configurationRows b).edge.cbase = ∅ := rfl
  have hsrc : ((configurationRows b).edge.source : Set (configurationW b).Carrier) = ∅ :=
    TopologicalSpace.Opens.coe_bot
  refine ⟨fun c => isEmptyElim c, Topology.IsEmbedding.of_subsingleton _, range_eq_empty _, ?_,
    ?_, ?_, rfl, fun c => isEmptyElim c, fun c => isEmptyElim c, ?_⟩
  · rw [hcb, image_empty]
  · rw [hsrc, image_empty]
  · intro x
    exact (CircleRegion.false_of_bot (NoCuts.carrier (configurationQ b)) x).elim
  · change (emptyEdges (configurationQ b)).edgePiece = _
    rw [emptyEdgePiece, image_empty]
    rfl

/-- The circle table (the circle family is empty). -/
theorem circleLink_configuration_LND74 (b : Bool) :
    CircleLink_LND74 (Equiv.refl (configurationW b).Carrier) (configurationRows b).circle
      (fun _ => (0 : ℝ)) ∅ ∅ ∅ ∅ := by
  have : IsEmpty (configurationRows b).circle.Base := ⟨fun c => PEmpty.elim c⟩
  have hcb : (configurationRows b).circle.cbase = ∅ := rfl
  have hdom : ((configurationRows b).circle.domain : Set (configurationW b).Carrier) = ∅ :=
    TopologicalSpace.Opens.coe_bot
  refine ⟨fun c => isEmptyElim c, Topology.IsEmbedding.of_subsingleton _, range_eq_empty _, ?_,
    ?_, ?_, fun c => isEmptyElim c, ?_⟩
  · rw [hcb, image_empty]
  · rw [hdom, image_empty]
  · intro x
    exact (CircleRegion.false_of_bot (NoCuts.carrier (configurationQ b)) x).elim
  · change (emptyCircles (configurationQ b)).region = _
    rw [emptyCircleRegion, image_empty]
    rfl

/-- The regions table. -/
theorem regionsLink_configuration_LND74 (b : Bool) :
    ∃ M₁ M₂ M₃ : Set (configurationW b).Carrier,
      RegionsLink_LND74 (Equiv.refl _) (configurationRows b) M₁ M₂ M₃ := by
  cases b
  · refine ⟨∅, ∅, ∅, ?_, ?_, ?_⟩
    · rw [image_empty]
      exact zeroRegionM1
    · rw [image_empty]
      exact configurationRegionM2 false
    · rw [image_empty]
      exact configurationRegionM3 false
  · refine ⟨univ, ∅, ∅, ?_, ?_, ?_⟩
    · rw [image_univ]
      exact (slimRegionM1.trans (Equiv.surjective _).range_eq.symm)
    · rw [image_empty]
      exact configurationRegionM2 true
    · rw [image_empty]
      exact configurationRegionM3 true

end GC.GraphManifold.Assembly.FC39P0.X136

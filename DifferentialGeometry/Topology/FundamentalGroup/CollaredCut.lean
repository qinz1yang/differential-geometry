/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.RelativeClosedCover
import DifferentialGeometry.Topology.FundamentalGroup.CommutativeCover
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarRestriction

open Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

theorem simplyConnectedSpace_or_preimage_of_isMulCommutative
    {X : Type*} [TopologicalSpace X] {D S Y : Set X}
    [CompactSpace S] [SimplyConnectedSpace S] [ConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (c : TwoSidedCollar ((↑) : S → X)) (hD : IsClosed D)
    (hreg : closure (interior D) = D) (hfront : frontier D = S)
    (hSY : S ⊆ interior Y) (s : S)
    (hcomm : IsMulCommutative (FundamentalGroup Y ⟨s, interior_subset (hSY s.property)⟩)) :
    SimplyConnectedSpace (((↑) : Y → X) ⁻¹' D) ∨
      SimplyConnectedSpace (((↑) : Y → X) ⁻¹' (interior D)ᶜ) := by
  obtain ⟨d, hdY, _⟩ := c.exists_subcollar_subset_open isOpen_interior
    (by simpa only [Subtype.range_coe] using hSY)
  let e : S → Y := Set.inclusion (hSY.trans interior_subset)
  let k : TwoSidedCollar e := {
    toFun := fun p => ⟨d.toFun p, interior_subset (hdY ⟨p, rfl⟩)⟩
    isOpenEmbedding_toFun :=
      _root_.Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        (d.isOpenEmbedding_toFun.continuous.subtype_mk _)
        (fun p q hpq => d.isOpenEmbedding_toFun.injective (congrArg Subtype.val hpq))
        (d.isOpenEmbedding_toFun.isOpenMap.subtype_mk _)
    zero_eq := fun t => Subtype.ext (d.zero_eq t) }
  let P := ((↑) : Y → X) ⁻¹' D
  let Q := ((↑) : Y → X) ⁻¹' (interior D)ᶜ
  have hcover : P ∪ Q = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : (x : X) ∈ interior D
    · exact Or.inl (interior_subset hx : (x : X) ∈ D)
    · exact Or.inr hx
  have hmeet : P ∩ Q = Set.range e := by
    ext x
    constructor
    · intro hx
      have hxS : (x : X) ∈ S := hfront.subset ⟨hD.closure_eq.symm ▸ hx.1, hx.2⟩
      exact ⟨⟨x, hxS⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨hD.frontier_subset (hfront.symm.subset t.property),
        (hfront.symm.subset t.property).2⟩
  have hPQ : P \ Q = ((↑) : Y → X) ⁻¹' interior D := by
    ext x
    change ((x : X) ∈ D ∧ ¬ (x : X) ∉ interior D) ↔ (x : X) ∈ interior D
    exact ⟨fun h => not_not.mp h.2, fun h => ⟨interior_subset h, not_not.mpr h⟩⟩
  have hQP : Q \ P = ((↑) : Y → X) ⁻¹' Dᶜ := by
    ext x
    change ((x : X) ∉ interior D ∧ (x : X) ∉ D) ↔ (x : X) ∉ D
    exact ⟨And.right, fun h => ⟨fun hi => h (interior_subset hi), h⟩⟩
  have hPi : frontier (interior D) = S := by
    rw [frontier, hreg, interior_interior, ← hD.frontier_eq, hfront]
  have hPcl : closure (P \ Q) = P := by
    rw [hPQ, closure_preimage_subtype_val_of_frontier_subset (hPi.subset.trans hSY), hreg]
  have hQcl : closure (Q \ P) = Q := by
    rw [hQP, closure_preimage_subtype_val_of_frontier_subset
      ((frontier_compl D).trans hfront |>.subset.trans hSY), closure_compl]
  let _ : PathConnectedSpace P := k.pathConnectedSpace_left_of_closed_cover hcover hmeet hPcl hQcl
  let _ : PathConnectedSpace Q := k.pathConnectedSpace_left_of_closed_cover
    ((union_comm Q P).trans hcover) ((inter_comm Q P).trans hmeet) hQcl hPcl
  exact k.simplyConnectedSpace_or_of_closed_cover_of_isMulCommutative
    hcover hmeet hPcl hQcl s hcomm

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

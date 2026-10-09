/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.Homology.MayerVietorisGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.DeletedBoundaryCollar

open Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {B X : Type} [TopologicalSpace B] [TopologicalSpace X]
  {e : B → X} (c : TwoSidedCollar e)

include c in
theorem exists_integralFirstHomology_sum_of_collared_closed_cover [PathConnectedSpace B]
    {P Q : Set X} (hcover : P ∪ Q = univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q)
    (a : integralSingularHomology 1 X) :
    ∃ p : integralSingularHomology 1 P, ∃ q : integralSingularHomology 1 Q,
      integralSingularHomologyMap 1 (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X)) p +
        integralSingularHomologyMap 1 (⟨Subtype.val, continuous_subtype_val⟩ : C(Q, X)) q = a := by
  have hP : IsClosed P := hPcl ▸ isClosed_closure
  have hQ : IsClosed Q := hQcl ▸ isClosed_closure
  have hPf : frontier P = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hcover hPcl hQcl).trans hmeet
  have hQf : frontier Q = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq ((union_comm Q P).trans hcover) hQcl hPcl).trans
      ((inter_comm Q P).trans hmeet)
  obtain ⟨d, _, hdP, hdQ, hU, hI⟩ :=
    c.exists_open_cover_of_closed_cover hcover hmeet hPcl hQcl
  let U := d.domainNeighborhood P
  let V := d.reverse.domainNeighborhood Q
  let h := d.homeomorphRange.trans (Homeomorph.setCongr hI.symm)
  let _ : PathConnectedSpace (U ∩ V : Set X) :=
    h.surjective.pathConnectedSpace h.continuous
  obtain ⟨u, v, huv⟩ := exists_integralFirstHomology_sum_of_open_cover
    (d.isOpen_domainNeighborhood P) (d.reverse.isOpen_domainNeighborhood Q) hU a
  obtain ⟨p, hp⟩ :=
    (integralSingularHomologyHomotopyEquiv 1 (d.domainHomotopyEquiv hP hPf.subset hdP)).surjective u
  obtain ⟨q, hq⟩ :=
    (integralSingularHomologyHomotopyEquiv 1
      (d.reverse.domainHomotopyEquiv hQ hQf.subset hdQ)).surjective v
  refine ⟨p, q, ?_⟩
  have hp' : integralSingularHomologyMap 1 (d.domainInclusion hP hPf.subset) p = u := hp
  have hq' : integralSingularHomologyMap 1 (d.reverse.domainInclusion hQ hQf.subset) q = v := hq
  rw [← hp', ← hq'] at huv
  have hPmap : (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp
        (d.domainInclusion hP hPf.subset) := rfl
  have hQmap : (⟨Subtype.val, continuous_subtype_val⟩ : C(Q, X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)).comp
        (d.reverse.domainInclusion hQ hQf.subset) := rfl
  simpa only [hPmap, hQmap, integralSingularHomologyMap_comp, LinearMap.comp_apply] using huv

include c in
theorem exists_integralFirstHomology_sum_of_deleted_collared_cover {P Q G : Set X}
    (hGc : IsClosed G) (hG : G ⊆ Set.range e) [PathConnectedSpace (e ⁻¹' Gᶜ)]
    (hcover : P ∪ Q = univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q)
    (a : integralSingularHomology 1 (Gᶜ : Set X)) :
    ∃ p : integralSingularHomology 1 (((↑) : (Gᶜ : Set X) → X) ⁻¹' P),
      ∃ q : integralSingularHomology 1 (((↑) : (Gᶜ : Set X) → X) ⁻¹' Q),
        integralSingularHomologyMap 1 (⟨Subtype.val, continuous_subtype_val⟩ :
          C(((↑) : (Gᶜ : Set X) → X) ⁻¹' P, (Gᶜ : Set X))) p +
        integralSingularHomologyMap 1 (⟨Subtype.val, continuous_subtype_val⟩ :
          C(((↑) : (Gᶜ : Set X) → X) ⁻¹' Q, (Gᶜ : Set X))) q = a := by
  have hco := hGc.isOpen_compl.isOpenEmbedding_subtypeVal
  have hcover' : ((↑) : (Gᶜ : Set X) → X) ⁻¹' P ∪ Subtype.val ⁻¹' Q = univ := by
    rw [← preimage_union, hcover, preimage_univ]
  have hmeet' : ((↑) : (Gᶜ : Set X) → X) ⁻¹' P ∩ Subtype.val ⁻¹' Q =
      Set.range (fun b : e ⁻¹' Gᶜ => (⟨e b.val, b.property⟩ : (Gᶜ : Set X))) := by
    rw [← preimage_inter, hmeet]
    ext x
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨⟨b, show e b ∈ Gᶜ from hb.symm ▸ x.property⟩, Subtype.ext hb⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b.val, rfl⟩
  have hPcl' : closure (((↑) : (Gᶜ : Set X) → X) ⁻¹' P \ Subtype.val ⁻¹' Q) =
      Subtype.val ⁻¹' P := by
    rw [← preimage_sdiff, ← hco.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hPcl]
  have hQcl' : closure (((↑) : (Gᶜ : Set X) → X) ⁻¹' Q \ Subtype.val ⁻¹' P) =
      Subtype.val ⁻¹' Q := by
    rw [← preimage_sdiff, ← hco.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hQcl]
  exact (c.complementRestriction hGc hG).exists_integralFirstHomology_sum_of_collared_closed_cover
    hcover' hmeet' hPcl' hQcl' a

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

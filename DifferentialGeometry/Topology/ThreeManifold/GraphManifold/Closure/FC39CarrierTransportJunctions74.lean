import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportFaces74

/-!
# Draft 74, D74-6: transport of the junctions along ONE carrier diffeomorphism

Lane C14-REG-CHAIN (by S-REG-CHAIN), G23 (junction package of `FC39RowsV2.transport74`). For a
carrier diffeomorphism `e` between carriers of the same kind and a junction record `J` on the
rows `(Z, C, S, P, R)`:

* **`JunctionsV2.mapCarrier74 e hk J`**: the junction record of the transported rows
  `(Z.mapCarrier74 e, C.mapCarrier74 e, S.mapCarrier74 e, P.mapCarrier74 e hk, R.mapCarrier74 e)`
  on the transported boundary tori `E.transport74 e`. The actual label `EdgeEnd → ResidualFace`
  is `J.horizontal` read through the face equivalence `SlimPiecesV2.residualEquiv74` (the faces
  of `∂M₂` and the circle-base face labels are the same types, `labelEquiv74`), the labelled
  smooth `rimBase` is unchanged (the bases are unchanged), every set identity (cover, disjoint
  interiors, shared faces, whole end disks, rim fibres, the relative complements of §5.7) is the
  `e`-image of the original one; the local faces are the original ones with relabelled faces and
  the same defining functions on the same base neighbourhoods.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] diskChartsBase_FC39P0

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}

/-- **The junctions transported along `e`** (carriers of the same kind; D74-6, faces package). -/
def JunctionsV2.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}
    {S : SlimPiecesV2 W₀ Z C} {P : EdgeBundle W₀} {R : CircleBundle W₀}
    (J : JunctionsV2 W₀ E Z C S P R) :
    JunctionsV2 W₁ (E.transport74 e) (Z.mapCarrier74 e) (C.mapCarrier74 e) (S.mapCarrier74 e)
      (P.mapCarrier74 e hk) (R.mapCarrier74 e) where
  cover := by
    have h : (⋃ a, allPieces (S.mapCarrier74 e) (P.mapCarrier74 e hk) (R.mapCarrier74 e) a) =
        e '' ⋃ a, allPieces S P R a := by
      rw [image_iUnion]
      exact iUnion_congr fun a => allPieces_mapCarrier74 e hk S P R a
    rw [h, J.cover, image_univ]
    exact (carrier_bijective_R74 e).2.range_eq
  interiors_disjoint a a' haa' := by
    dsimp only
    rw [allPieces_mapCarrier74 e hk S P R a, allPieces_mapCarrier74 e hk S P R a',
      ← image_interior_R74 e, ← image_interior_R74 e]
    exact (disjoint_image_iff e.injective).mpr (J.interiors_disjoint haa')
  shared_eq x F hxF := by
    have h := J.shared_eq (slimEndOfMap74 e S.model x) F hxF
    rw [endSet_mapCarrier74_of, h]
    exact (neighbourSet_mapCarrier74 e F).symm
  zero_cusp_disjoint i b := by
    rw [ZeroDomains.mapCarrier74_range e Z i, (C.mapCarrier74_range e b).1]
    exact (disjoint_image_iff e.injective).mpr (J.zero_cusp_disjoint i b)
  horizontal x := S.resToMap74 e (J.horizontal x)
  horizontal_disk x := by
    rw [EdgeBundle.mapCarrier74_disk e hk P x.1, residualSet_mapCarrier74]
    exact image_mono (J.horizontal_disk x)
  edge_faces F' := by
    obtain ⟨F, rfl⟩ : ∃ F, S.resToMap74 e F = F' :=
      ⟨S.resOfMap74 e F', (S.residualEquiv74 e).right_inv F'⟩
    have h1 : (⋃ (x : (P.mapCarrier74 e hk).EdgeEnd)
        (_ : S.resToMap74 e (J.horizontal x) = S.resToMap74 e F), (P.mapCarrier74 e hk).disk x.1) =
        e '' ⋃ (x : P.EdgeEnd) (_ : J.horizontal x = F), P.disk x.1 := by
      rw [image_iUnion]
      refine iUnion_congr fun x => ?_
      rw [image_iUnion]
      exact iUnion_congr_Prop (S.residualEquiv74 e).apply_eq_iff_eq fun _ =>
        EdgeBundle.mapCarrier74_disk e hk P x.1
    rw [h1, EdgeBundle.mapCarrier74_edgePiece, residualSet_mapCarrier74,
      ← image_inter (carrier_injective_R74 e), J.edge_faces F]
  rimBase := J.rimBase
  rimBase_smooth := J.rimBase_smooth
  rim_fibre c hc :=
    (EdgeBundle.mapCarrier74_rim e hk P c).trans
      ((congrArg (fun s => e '' s) (J.rim_fibre c hc)).trans
        (CircleBundle.mapCarrier74_fibre e R (J.rimBase c)).symm)
  edge_region := by
    rw [EdgeBundle.mapCarrier74_edgePiece, CircleBundle.mapCarrier74_region,
      ← image_inter (carrier_injective_R74 e), J.edge_region,
      EdgeBundle.mapCarrier74_vertical]
  local_faces c hc := by
    obtain ⟨U, hcU, L, φ, hL1, hL2, hφ, hsurj, hcb⟩ := J.local_faces c hc
    refine ⟨U, hcU, L.map (labelEquiv74 e hk S P).toEmbedding,
      fun f' => φ ((labelEquiv74 e hk S P).symm f'), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_map]
      exact hL1
    · rw [Finset.card_map]
      exact hL2
    · intro f' hf'
      obtain ⟨f, rfl⟩ := (labelEquiv74 e hk S P).surjective f'
      have hf : f ∈ L := (Finset.mem_map' _).mp hf'
      obtain ⟨h1, h2, h3⟩ := hφ f hf
      simp only [Equiv.symm_apply_apply]
      refine ⟨h1, h2, h3.trans ?_⟩
      ext c'
      refine and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [CircleBundle.mapCarrier74_fibre, circleFaceSet_mapCarrier74,
        image_subset_image_iff (carrier_injective_R74 e)]
    · intro v
      obtain ⟨w, hw⟩ := hsurj fun f => v ⟨labelEquiv74 e hk S P f.1,
        Finset.mem_map_of_mem (labelEquiv74 e hk S P).toEmbedding f.2⟩
      refine ⟨w, ?_⟩
      funext f'
      have hf'' := congrFun hw ⟨(labelEquiv74 e hk S P).symm f'.1,
        Finset.mem_map_equiv.mp f'.2⟩
      exact hf''.trans (congrArg v (Subtype.ext ((labelEquiv74 e hk S P).apply_symm_apply f'.1)))
    · refine hcb.trans ?_
      ext c'
      refine and_congr_right fun _ => ⟨fun h f' hf' => h _ (Finset.mem_map_equiv.mp hf'),
        fun h f hf => ?_⟩
      have := h (labelEquiv74 e hk S P f)
        (Finset.mem_map_of_mem (labelEquiv74 e hk S P).toEmbedding hf)
      simpa using this
  region_eq := by
    rw [regionM3_mapCarrier74 e hk S P, J.region_eq, CircleBundle.mapCarrier74_region]
  frontier_M2 := by
    rw [regionM2_mapCarrier74, ← image_frontier_R74 e, J.frontier_M2, boundaryM2_mapCarrier74]
  region_boundary := by
    rw [CircleBundle.mapCarrier74_region, boundaryM2_mapCarrier74,
      EdgeBundle.mapCarrier74_horizontalDisks, relInt_image_R74,
      ← image_inter (carrier_injective_R74 e), J.region_boundary,
      image_sdiff (carrier_injective_R74 e)]
  slim_M2 := by
    rw [S.mapCarrier74_union e, regionM2_mapCarrier74,
      ← image_inter (carrier_injective_R74 e), J.slim_M2,
      iUnion_newEnd_mapCarrier74]
  shared_removed σ := by
    have h := J.shared_removed ⟨slimEndOfMap74 e S.model σ.1, σ.2⟩
    rw [regionM1_mapCarrier74, S.mapCarrier74_union e, relInt_image_R74,
      endSet_mapCarrier74_of]
    exact image_mono h

end GC.GraphManifold.Assembly.FC39P0

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdgeCross74

/-!
# Draft 74, D74-6: junctions and labelled corner tubes transported between carriers of ANY kinds

Lane O-CROSS, G3. Same constructions as `JunctionsV2.mapCarrier74` and
`LabelledCornerTubes.mapCarrier74` (lane C14-REG-CHAIN by S-REG-CHAIN, G23) over
`EdgeBundle.mapCarrierCross74`: **`JunctionsV2.mapCarrierCross74 e J`**,
**`LabelledCornerTubes.mapCarrierCross74 e T`**.
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

/-- **The junctions transported along `e`** (carriers of ANY kinds; D74-6, faces package). -/
def JunctionsV2.mapCarrierCross74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}
    {S : SlimPiecesV2 W₀ Z C} {P : EdgeBundle W₀} {R : CircleBundle W₀}
    (J : JunctionsV2 W₀ E Z C S P R) :
    JunctionsV2 W₁ (E.transport74 e) (Z.mapCarrier74 e) (C.mapCarrier74 e) (S.mapCarrier74 e)
      (P.mapCarrierCross74 e) (R.mapCarrier74 e) where
  cover := by
    have h : (⋃ a, allPieces (S.mapCarrier74 e) (P.mapCarrierCross74 e) (R.mapCarrier74 e) a) =
        e '' ⋃ a, allPieces S P R a := by
      rw [image_iUnion]
      exact iUnion_congr fun a => allPieces_mapCarrierCross74 e S P R a
    rw [h, J.cover, image_univ]
    exact (carrier_bijective_R74 e).2.range_eq
  interiors_disjoint a a' haa' := by
    dsimp only
    rw [allPieces_mapCarrierCross74 e S P R a, allPieces_mapCarrierCross74 e S P R a',
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
    rw [EdgeBundle.mapCarrierCross74_disk e P x.1, residualSet_mapCarrier74]
    exact image_mono (J.horizontal_disk x)
  edge_faces F' := by
    obtain ⟨F, rfl⟩ : ∃ F, S.resToMap74 e F = F' :=
      ⟨S.resOfMap74 e F', (S.residualEquiv74 e).right_inv F'⟩
    have h1 : (⋃ (x : (P.mapCarrierCross74 e).EdgeEnd)
        (_ : S.resToMap74 e (J.horizontal x) = S.resToMap74 e F),
          (P.mapCarrierCross74 e).disk x.1) =
        e '' ⋃ (x : P.EdgeEnd) (_ : J.horizontal x = F), P.disk x.1 := by
      rw [image_iUnion]
      refine iUnion_congr fun x => ?_
      rw [image_iUnion]
      exact iUnion_congr_Prop (S.residualEquiv74 e).apply_eq_iff_eq fun _ =>
        EdgeBundle.mapCarrierCross74_disk e P x.1
    rw [h1, EdgeBundle.mapCarrierCross74_edgePiece, residualSet_mapCarrier74,
      ← image_inter (carrier_injective_R74 e), J.edge_faces F]
  rimBase := J.rimBase
  rimBase_smooth := J.rimBase_smooth
  rim_fibre c hc :=
    (EdgeBundle.mapCarrierCross74_rim e P c).trans
      ((congrArg (fun s => e '' s) (J.rim_fibre c hc)).trans
        (CircleBundle.mapCarrier74_fibre e R (J.rimBase c)).symm)
  edge_region := by
    rw [EdgeBundle.mapCarrierCross74_edgePiece, CircleBundle.mapCarrier74_region,
      ← image_inter (carrier_injective_R74 e), J.edge_region,
      EdgeBundle.mapCarrierCross74_vertical]
  local_faces c hc := by
    obtain ⟨U, hcU, L, φ, hL1, hL2, hφ, hsurj, hcb⟩ := J.local_faces c hc
    refine ⟨U, hcU, L.map (labelEquivCross74 e S P).toEmbedding,
      fun f' => φ ((labelEquivCross74 e S P).symm f'), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_map]
      exact hL1
    · rw [Finset.card_map]
      exact hL2
    · intro f' hf'
      obtain ⟨f, rfl⟩ := (labelEquivCross74 e S P).surjective f'
      have hf : f ∈ L := (Finset.mem_map' _).mp hf'
      obtain ⟨h1, h2, h3⟩ := hφ f hf
      simp only [Equiv.symm_apply_apply]
      refine ⟨h1, h2, h3.trans ?_⟩
      ext c'
      refine and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [CircleBundle.mapCarrier74_fibre, circleFaceSet_mapCarrierCross74,
        image_subset_image_iff (carrier_injective_R74 e)]
    · intro v
      obtain ⟨w, hw⟩ := hsurj fun f => v ⟨labelEquivCross74 e S P f.1,
        Finset.mem_map_of_mem (labelEquivCross74 e S P).toEmbedding f.2⟩
      refine ⟨w, ?_⟩
      funext f'
      have hf'' := congrFun hw ⟨(labelEquivCross74 e S P).symm f'.1,
        Finset.mem_map_equiv.mp f'.2⟩
      exact hf''.trans (congrArg v (Subtype.ext ((labelEquivCross74 e S P).apply_symm_apply f'.1)))
    · refine hcb.trans ?_
      ext c'
      refine and_congr_right fun _ => ⟨fun h f' hf' => h _ (Finset.mem_map_equiv.mp hf'),
        fun h f hf => ?_⟩
      have := h (labelEquivCross74 e S P f)
        (Finset.mem_map_of_mem (labelEquivCross74 e S P).toEmbedding hf)
      simpa using this
  region_eq := by
    rw [regionM3_mapCarrierCross74 e S P, J.region_eq, CircleBundle.mapCarrier74_region]
  frontier_M2 := by
    rw [regionM2_mapCarrier74, ← image_frontier_R74 e, J.frontier_M2, boundaryM2_mapCarrier74]
  region_boundary := by
    rw [CircleBundle.mapCarrier74_region, boundaryM2_mapCarrier74,
      EdgeBundle.mapCarrierCross74_horizontalDisks, relInt_image_R74,
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

/-- **The labelled corner tubes transported along `e`** (carriers of ANY kinds; D74-6,
tube package). -/
def LabelledCornerTubes.mapCarrierCross74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}
    {S : SlimPiecesV2 W₀ Z C} {P : EdgeBundle W₀} {R : CircleBundle W₀}
    {J : JunctionsV2 W₀ E Z C S P R} (T : LabelledCornerTubes J) :
    LabelledCornerTubes (J.mapCarrierCross74 e) where
  base x := T.base x
  rimBase_mem x := T.rimBase_mem x
  chart x := T.chart x
  chart_source x := T.chart_source x
  chart_center x := T.chart_center x
  tube_source x :=
    (subset_of_eq (CircleBundle.mapCarrier74_tube e R _)).trans (image_mono (T.tube_source x))
  tube_near x :=
    (subset_of_eq (CircleBundle.mapCarrier74_tube e R _)).trans
      ((image_mono (T.tube_near x)).trans
        (subset_of_eq (residualNear_mapCarrier74 e S (J.horizontal x)).symm))
  height_eq x z hz := by
    obtain ⟨hx, h⟩ := T.height_eq x (e.restrictOpens74 R.domain z) hz
    exact ⟨⟨e.symm z.1, hx, e.apply_symm_apply _⟩, h⟩
  face_eq x z hz :=
    (T.face_eq x (e.restrictOpens74 R.domain z) hz).trans
      (congrFun (residualFn_mapCarrier74 e S (J.horizontal x)).symm z.1)
  descended x := T.descended x
  descended_smooth x := T.descended_smooth x
  descended_regular x := T.descended_regular x
  descended_eq x z hz := by
    obtain ⟨hx, h⟩ := T.descended_eq x (e.restrictOpens74 R.domain z) hz
    exact ⟨⟨e.symm z.1, hx, e.apply_symm_apply _⟩,
      (congrFun (residualFn_mapCarrier74 e S (J.horizontal x)) z.1).trans h⟩
  vertex_side {x} {z} hz := by
    refine Iff.trans ?_ (T.vertex_side (e := x) (x := e.restrictOpens74 R.domain z) hz)
    change (z : W₁.Carrier) ∈ (S.mapCarrier74 e).rowSet ((S.mapCarrier74 e).residualOwner
      (S.resToMap74 e (J.horizontal x))) ↔ _
    rw [residualOwner_mapCarrier74, rowSet_mapCarrier74, mem_image_iff_symm_R74]
    exact Iff.rfl
  edge_side {x} {z} hz := by
    refine Iff.trans ?_ (T.edge_side (e := x) (x := e.restrictOpens74 R.domain z) hz)
    exact (Iff.of_eq (congrArg (fun s => (z : W₁.Carrier) ∈ s)
      (EdgeBundle.mapCarrierCross74_wholeComponent e P (show P.EdgeEnd from x).component))).trans
      mem_image_iff_symm_R74
  region_side {x} {z} hz := by
    refine Iff.trans ?_ (T.region_side (e := x) (x := e.restrictOpens74 R.domain z) hz)
    rw [CircleBundle.mapCarrier74_region, mem_image_iff_symm_R74]
    exact Iff.rfl

end GC.GraphManifold.Assembly.FC39P0

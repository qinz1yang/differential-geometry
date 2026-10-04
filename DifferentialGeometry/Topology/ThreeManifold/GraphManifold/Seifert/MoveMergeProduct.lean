import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMerge
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MergedSolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProductCharts

/-!
# Recollaring the merge contraction from a product diffeomorphism

A product diffeomorphism of the merged piece suffices to decrease the presentation complexity.
The remaining collars are reconstructed by contraction recollaring; no agreement with the
original full half collars is required. An annular host gives a product diffeomorphism by
absorbing its long collar into the solid torus. A pants host uses the actual single-seam
filling product for all three boundary circles, with linear matching or an explicit torus
mapping-class classification input.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
  (hf : E.HostSelfSeamFree j b)
  (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j)

include h in
theorem mergeBase_kind_mem :
    E.kind (E.hostPiece j b) - 1 ∈ ({1, 2} : Finset ℕ) := by
  have hkind := E.kind_mem (E.hostPiece j b)
  have hge := h.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkind ⊢
  omega

theorem exists_merge_of_diffeomorph
    (B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1))
    (he : Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (E.mergeContraction j b h hf hext).cutCarrier.model⟯
        (E.mergeContraction j b h hf hext).components.piece
          (E.mergeLast j b h hf hext))) :
    ∃ E' : ElementaryPresentation W, E'.complexity + 1 = E.complexity := by
  have hk3 : E.kind (E.hostPiece j b) - 1 ∈ ({1, 2, 3} : Finset ℕ) := by
    have hkind := E.mergeBase_kind_mem j b h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkind ⊢
    omega
  obtain ⟨E', hE'⟩ := exists_elementary_contract_of_diffeomorph E (E.toTorus.seamPair j)
    hext (E.toTorus.cutCarrier_kind_of_pos j.pos) (h.isConnected_region hf hext)
    (E.kind (E.hostPiece j b) - 1) hk3
    (E.mergeContraction_card_ownedSide_last j b h hf hext) B he
  exact ⟨E', by rw [hE']; exact E.mergeContraction_pairing_count j b h hf hext⟩

theorem exists_planarBase_diffeomorph_merge_of_hostKind_eq_two
    (hk2 : E.kind (E.hostPiece j b) = 2) :
    ∃ B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1),
      Nonempty
        ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (E.mergeContraction j b h hf hext).cutCarrier.model⟯
          (E.mergeContraction j b h hf hext).components.piece
            (E.mergeLast j b h hf hext)) := by
  have hA : E.IsAbsorbSeam j b := ⟨h.1, hk2⟩
  obtain ⟨e⟩ := mergedSolidTorus W E j b hA hext
  have hd : E.kind (E.hostPiece j b) - 1 = 1 := by rw [hk2]
  rw [hd]
  let P : ProductFibredPiece E.toTorus (E.seamPiece j b) 1 := h.1 ▸ E.piece _
  exact ⟨P.base, ⟨P.trivialization.trans e.symm⟩⟩

include h hf hext in
theorem exists_merge_of_selfSeamFree_of_hostKind_eq_two
    (hk2 : E.kind (E.hostPiece j b) = 2) :
    ∃ E' : ElementaryPresentation W, E'.complexity + 1 = E.complexity := by
  obtain ⟨B, he⟩ := E.exists_planarBase_diffeomorph_merge_of_hostKind_eq_two j b h hf hext hk2
  exact E.exists_merge_of_diffeomorph j b h hf hext B he


def fillingProductRestrictDiffeomorph
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    (fillingProductCarrier E j).Carrier ≃ₘ⟮(fillingProductCarrier E j).model,
      (E.toTorus.restrictCarrier (E.toTorus.seamPair j)
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).model⟯
      (E.toTorus.restrictCarrier (E.toTorus.seamPair j)
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).Carrier := by
  let hext := TorusPresentation.externalPiece_not_mem_of_closed E.toTorus
    (E.toTorus.seamPair j)
  let : ChartedSpace (EuclideanHalfSpace 3)
      (E.toTorus.restrictCarrier (E.toTorus.seamPair j) hext).Carrier :=
    (E.toTorus.restrictCarrier (E.toTorus.seamPair j) hext).charts
  have hAll : ∀ k, E.toTorus.leftPiece k ∈ E.toTorus.seamPair j ∧
      E.toTorus.rightPiece k ∈ E.toTorus.seamPair j → k ∈ ({j} : Finset _) := by
    intro k hk
    exact Finset.mem_singleton.mpr (h.eq_of_internal hf hk.1 hk.2)
  let e := E.toTorus.restrictAlongHomeomorph_of_all (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) hAll
  refine { e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (E.toTorus.contMDiff_restrictCarrier_iff (E.toTorus.seamPair j) hext e).mpr
    exact fillingProductFold_smooth E j
  · let : ChartedSpace (EuclideanHalfSpace 3)
        (Set.range (E.toTorus.restrictMap (E.toTorus.seamPair j))) :=
      (E.toTorus.restrictAtlas (E.toTorus.seamPair j) hext).toChartedSpace
    have heq : E.toTorus.restrictAlongMap (E.toTorus.seamPair j) {j}
        (fillingProduct_internal E j) ∘ e.symm = Subtype.val := by
      funext x
      exact congrArg Subtype.val (e.apply_symm_apply x)
    have hs : ContMDiffOn (𝓡∂ 3) (NoCuts.carrier Q).model ∞
        (E.toTorus.restrictAlongMap (E.toTorus.seamPair j) {j}
          (fillingProduct_internal E j) ∘ e.symm) Set.univ := by
      rw [heq]
      exact (E.toTorus.contMDiff_restrictCarrier_val (E.toTorus.seamPair j) hext).contMDiffOn
    exact contMDiffOn_univ.mp
      (E.toTorus.contMDiffOn_restrictAlong_of_comp (E.toTorus.seamPair j) {j}
        (fillingProduct_internal E j) hext (𝓡∂ 3)
        (N := (E.toTorus.restrictCarrier (E.toTorus.seamPair j) hext).Carrier)
        e.symm Set.univ e.symm.continuous.continuousOn hs)


def fillingProductMergeDiffeomorph
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    (fillingProductCarrier E j).Carrier ≃ₘ⟮(fillingProductCarrier E j).model,
      (E.mergeContraction j b h hf
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).cutCarrier.model⟯
      (E.mergeContraction j b h hf
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).components.piece
        (E.mergeLast j b h hf (TorusPresentation.externalPiece_not_mem_of_closed _ _)) := by
  let T := E.toTorus
  let S := T.seamPair j
  let hext := TorusPresentation.externalPiece_not_mem_of_closed T S
  let hk := T.cutCarrier_kind_of_pos j.pos
  let e := E.fillingProductRestrictDiffeomorph j b h hf
  let d : (fillingProductCarrier E j).Carrier ≃ₘ⟮(fillingProductCarrier E j).model,
      T.cutCarrier.model⟯ (T.contractRegion S hext hk).Carrier :=
    { e.toHomeomorph with
      contMDiff_toFun := (recast_contMDiff_iff_right (T.restrictCarrier S hext)
        T.cutCarrier.kind hk.symm e).mpr e.contMDiff
      contMDiff_invFun := (recast_contMDiff_iff_left (T.restrictCarrier S hext)
        T.cutCarrier.kind hk.symm e.symm).mpr e.symm.contMDiff }
  exact d.trans (T.contractLastDiffeomorph S hext hk (h.isConnected_region hf hext))


theorem exists_merge_of_fillingProduct
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b)
    (B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1))
    (he : Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier)) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
      E'.complexity + 1 = E.complexity := by
  obtain ⟨e⟩ := he
  exact E.exists_merge_of_diffeomorph j b h hf
    (TorusPresentation.externalPiece_not_mem_of_closed _ _) B
    ⟨e.trans (E.fillingProductMergeDiffeomorph j b h hf)⟩


include h in
theorem hostSelfSeamFree_of_kind_two
    (hk2 : E.kind (E.hostPiece j b) = 2) : E.HostSelfSeamFree j b := by
  intro k hl hr
  have hk3 := (h.host_sides hl hr).1
  omega

theorem exists_fillingProduct_of_hostKind_eq_two
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk2 : E.kind (E.hostPiece j b) = 2) :
    ∃ B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1),
      Nonempty
        ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) := by
  have hf := E.hostSelfSeamFree_of_kind_two j b h hk2
  obtain ⟨B, e⟩ := E.exists_planarBase_diffeomorph_merge_of_hostKind_eq_two j b h hf
    (TorusPresentation.externalPiece_not_mem_of_closed _ _) hk2
  exact ⟨B, ⟨e.some.trans (E.fillingProductMergeDiffeomorph j b h hf).symm⟩⟩

section ClosedConsumers

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem exists_fillingProduct_of_hostKind_eq_three_of_linearSeam
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (hlin : E.IsLinearSeam j) :
    ∃ B : PlanarBase.{u} 2, Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) := by
  exact ⟨annulusPlanarBase, E.exists_fillingProductDiffeomorph_of_linear j b h hk3 hlin⟩

theorem exists_fillingProduct_of_hostKind_eq_three_of_torusMappingClassLinear
    (hT : TorusMappingClassLinear) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) :
    ∃ B : PlanarBase.{u} 2, Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) := by
  exact ⟨annulusPlanarBase, E.exists_fillingProductDiffeomorph hT j b h hk3⟩

theorem exists_planarBase_diffeomorph_merge_of_linearSeam
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) (hlin : E.IsLinearSeam j) :
    ∃ B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1), Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (E.mergeContraction j b h hf
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)).cutCarrier.model⟯
        (E.mergeContraction j b h hf
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)).components.piece
        (E.mergeLast j b h hf (TorusPresentation.externalPiece_not_mem_of_closed _ _))) := by
  by_cases hk2 : E.kind (E.hostPiece j b) = 2
  · exact E.exists_planarBase_diffeomorph_merge_of_hostKind_eq_two j b h hf
      (TorusPresentation.externalPiece_not_mem_of_closed _ _) hk2
  · have hk3 : E.kind (E.hostPiece j b) = 3 := by
      have hmem := E.kind_mem (E.hostPiece j b)
      have hge := h.2.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    obtain ⟨B, ⟨e⟩⟩ := E.exists_fillingProduct_of_hostKind_eq_three_of_linearSeam j b h hk3 hlin
    have hd : E.kind (E.hostPiece j b) - 1 = 2 := by rw [hk3]
    rw [hd]
    exact ⟨B, ⟨e.trans (E.fillingProductMergeDiffeomorph j b h hf)⟩⟩

theorem exists_planarBase_diffeomorph_merge_of_torusMappingClassLinear
    (hT : TorusMappingClassLinear) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    ∃ B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1), Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (E.mergeContraction j b h hf
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)).cutCarrier.model⟯
        (E.mergeContraction j b h hf
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)).components.piece
        (E.mergeLast j b h hf (TorusPresentation.externalPiece_not_mem_of_closed _ _))) := by
  by_cases hk2 : E.kind (E.hostPiece j b) = 2
  · exact E.exists_planarBase_diffeomorph_merge_of_hostKind_eq_two j b h hf
      (TorusPresentation.externalPiece_not_mem_of_closed _ _) hk2
  · have hk3 : E.kind (E.hostPiece j b) = 3 := by
      have hmem := E.kind_mem (E.hostPiece j b)
      have hge := h.2.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    obtain ⟨B, ⟨e⟩⟩ :=
      E.exists_fillingProduct_of_hostKind_eq_three_of_torusMappingClassLinear hT j b h hk3
    have hd : E.kind (E.hostPiece j b) - 1 = 2 := by rw [hk3]
    rw [hd]
    exact ⟨B, ⟨e.trans (E.fillingProductMergeDiffeomorph j b h hf)⟩⟩

theorem exists_merge_of_selfSeamFree_of_linearSeam
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) (hlin : E.IsLinearSeam j) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
      E'.complexity + 1 = E.complexity := by
  obtain ⟨B, he⟩ := E.exists_planarBase_diffeomorph_merge_of_linearSeam j b h hf hlin
  exact E.exists_merge_of_diffeomorph j b h hf
    (TorusPresentation.externalPiece_not_mem_of_closed _ _) B he

theorem exists_merge_of_selfSeamFree_of_torusMappingClassLinear
    (hT : TorusMappingClassLinear) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
      E'.complexity + 1 = E.complexity := by
  obtain ⟨B, he⟩ := E.exists_planarBase_diffeomorph_merge_of_torusMappingClassLinear hT j b h hf
  exact E.exists_merge_of_diffeomorph j b h hf
    (TorusPresentation.externalPiece_not_mem_of_closed _ _) B he

end ClosedConsumers

end GC.Seifert.ElementaryPresentation

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeRegions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.VertexGroupInjectiveClosed

/-!
# The fundamental group of a torus presentation as a graph of groups

Chapter 5 plan P4, tier T2. For a torus presentation `G` of `W` without external tori whose pieces
have π₁-injective ports and freely indecomposable, non-cyclic fundamental groups, π₁ of `W` is
freely indecomposable and not cyclic at every basepoint
(`TorusPresentation.indecomposableNoncyclic_of_vertex`). This is the finite-assembly π₁
recognition of the plan: π₁ of `W` is assembled from the piece groups one seam at a time, each
seam an amalgam or an HNN extension over the injective torus group `ℤ × ℤ`, and lane GG's
`freelyIndecomposable_pushout` and `freelyIndecomposable_hnnExtension` apply at every step.

The induction is that of K09c and K19 over finsets `K` of seams and the open sets `cutOpen K`.
Its invariant is `RegionFI (cutOpen K)`. For `K = ∅` the set `cutOpen ∅` is homeomorphic to the
interior of the cut carrier (`cutOpenHomeoInterior`), in which every piece interior is clopen,
and a piece interior is homotopy equivalent to its piece (X4), so the vertex hypothesis applies
(`regionFI_cutOpen_empty`). Adding a seam `j` (`regionFI_insert`) glues its collar, whose group is
`ℤ × ℤ` (`regionFI_seamCollar`), to the path components `A`, `B` of `cutOpen K` met by its two
halves: by the HNN step when `A = B`, by two amalgam steps otherwise; every other path component
of `cutOpen K` stays clopen in `cutOpen (insert j K)`. The seam levels are injective by K09c.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.Seifert

theorem isClopen_preimage_pathComponentIn {M : Type u} [TopologicalSpace M]
    [LocallyPathConnectedSpace M] {O : Set M} (hO : IsOpen O) (x : M) :
    IsClopen (Subtype.val ⁻¹' pathComponentIn O x : Set O) := by
  refine isClopen_preimage_of_cover (D := O \ pathComponentIn O x) (hO.pathComponentIn x)
    (isOpen_diff_pathComponentIn hO x) (fun y hy => ?_) ?_
  · by_cases h : y ∈ pathComponentIn O x
    · exact Or.inl h
    · exact Or.inr ⟨hy, h⟩
  · exact Set.disjoint_left.mpr fun _ h h' => h'.2 h

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

attribute [local instance] locallyPathConnectedSpace_carrier

theorem regionFI_seamCollar (j : Fin G.pairing.count) : RegionFI (G.seamCollar j) := by
  have hb := G.bijective_seamTorusIn j (G.seamCollar j) rfl (1, 1)
  exact regionFI_of_isPathConnected (G.isPathConnected_seamCollar j) _
    ((indecomposableNoncyclic_iff_of_bijective _ _ hb).mp (indecomposableNoncyclic_torus _))

section Step
variable {G} {j : Fin G.pairing.count} {K : Finset (Fin G.pairing.count)}

theorem regionFI_insert (hj : j ∉ K) (hK : G.SeamLevelsInj K) (hOfi : RegionFI (G.cutOpen K)) :
    RegionFI (G.cutOpen (insert j K)) := by
  set O := G.cutOpen K with hOdef
  set O' := G.cutOpen (insert j K) with hO'def
  set C := G.seamCollar j with hCdef
  have hO : IsOpen O := G.isOpen_cutOpen K
  have hO'o : IsOpen O' := G.isOpen_cutOpen (insert j K)
  have hgap : C ∩ O = (G.seamSurface j)ᶜ ∩ C := G.seamCollar_inter_cutOpen j hj
  have hgap' : C ∩ O = G.negHalf j ∪ G.posHalf j := hgap.trans (G.gap_eq j)
  have hnegO : G.negHalf j ⊆ O := fun y hy =>
    (hgap' ▸ (Or.inl hy : y ∈ G.negHalf j ∪ G.posHalf j) : y ∈ C ∩ O).2
  have hposO : G.posHalf j ⊆ O := fun y hy =>
    (hgap' ▸ (Or.inr hy : y ∈ G.negHalf j ∪ G.posHalf j) : y ∈ C ∩ O).2
  have hnegC : G.negHalf j ⊆ C := fun y hy => (G.negHalf_subset_gap j hy).2
  have hposC : G.posHalf j ⊆ C := fun y hy => (G.posHalf_subset_gap j hy).2
  have hOO' : O ⊆ O' := G.cutOpen_subset_insert j K
  have hCO' : C ⊆ O' := G.seamCollar_subset_cutOpen_insert j K
  have hO'cov : O' ⊆ O ∪ C := G.cutOpen_insert_subset j K
  have hCo : IsOpen C := G.isOpen_seamCollar j
  set t₀ : Torus := (1, 1)
  set A := pathComponentIn O (G.levelNeg j t₀) with hAdef
  set B := pathComponentIn O (G.levelPos j t₀) with hBdef
  have hAo : IsOpen A := hO.pathComponentIn _
  have hBo : IsOpen B := hO.pathComponentIn _
  have hApc : IsPathConnected A :=
    isPathConnected_pathComponentIn (hnegO (G.levelNeg_mem_negHalf j t₀))
  have hBpc : IsPathConnected B :=
    isPathConnected_pathComponentIn (hposO (G.levelPos_mem_posHalf j t₀))
  have hnegA : G.negHalf j ⊆ A :=
    (G.isPathConnected_negHalf j).subset_pathComponentIn (G.levelNeg_mem_negHalf j t₀) hnegO
  have hposB : G.posHalf j ⊆ B :=
    (G.isPathConnected_posHalf j).subset_pathComponentIn (G.levelPos_mem_posHalf j t₀) hposO
  have hAO : A ⊆ O := pathComponentIn_subset
  have hBO : B ⊆ O := pathComponentIn_subset
  have hCOsub : ∀ y, y ∈ C → y ∈ O → y ∈ G.negHalf j ∪ G.posHalf j := fun y hc ho =>
    hgap' ▸ (⟨hc, ho⟩ : y ∈ C ∩ O)
  have hiNeg : InjInto A (G.levelNeg j) :=
    (hK j).1.of_subset hAO fun t => hnegA (G.levelNeg_mem_negHalf j t)
  have hiPos : InjInto B (G.levelPos j) :=
    (hK j).2.of_subset hBO fun t => hposB (G.levelPos_mem_posHalf j t)
  have hcolNeg := G.injInto_seamCollar_levelNeg j
  have hcolPos := G.injInto_seamCollar_levelPos j
  have hAfi : RegionFI A := hOfi.of_isClopen hAO (isClopen_preimage_pathComponentIn hO _)
  have hBfi : RegionFI B := hOfi.of_isClopen hBO (isClopen_preimage_pathComponentIn hO _)
  have hCfi := G.regionFI_seamCollar j
  obtain ⟨X, hXO', hXcl, hXfi, hAX, hBX, hCX⟩ : ∃ X ⊆ O',
      IsClopen (Subtype.val ⁻¹' X : Set O') ∧ RegionFI X ∧ A ⊆ X ∧ B ⊆ X ∧ C ⊆ X := by
    by_cases hAB : G.levelPos j t₀ ∈ A
    · have hBA : B = A := pathComponentIn_congr hAB
      have hposA : G.posHalf j ⊆ A := hBA ▸ hposB
      have hN : A ∩ C = G.negHalf j ∪ G.posHalf j := by
        ext y
        constructor
        · rintro ⟨ha, hc⟩
          exact hCOsub y hc (hAO ha)
        · rintro (h | h)
          · exact ⟨hnegA h, hnegC h⟩
          · exact ⟨hposA h, hposC h⟩
      have hAgap : (G.seamSurface j)ᶜ ∩ C = A ∩ C := (hN.trans (G.gap_eq j).symm).symm
      have hf₀ : ∀ t, G.levelNeg j t ∈ A ∩ C := fun t =>
        ⟨hnegA (G.levelNeg_mem_negHalf j t), hnegC (G.levelNeg_mem_negHalf j t)⟩
      have hf₁ : ∀ t, G.levelPos j t ∈ A ∩ C := fun t =>
        ⟨hposA (G.levelPos_mem_posHalf j t), hposC (G.levelPos_mem_posHalf j t)⟩
      have hX := RegionFI.union_of_hnn hAo hCo hApc (G.isPathConnected_seamCollar j) hN
        (G.isOpen_negHalf j) (G.isOpen_posHalf j) (G.disjoint_negHalf_posHalf j)
        (G.isPathConnected_negHalf j) (G.isPathConnected_posHalf j) (G.levelNeg j)
        (G.levelPos j) hf₀ hf₁ t₀ (G.levelNeg_mem_negHalf j t₀) (G.levelPos_mem_posHalf j t₀)
        (bijective_toSubset_congr hAgap (G.levelNeg j) _ _ t₀ (G.bijective_gapLevel_neg j t₀))
        (G.bijective_collar_gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) t₀)
        (bijective_toSubset_congr hAgap (G.levelPos j) _ _ t₀
          (G.bijective_gapLevel_pos j t₀)).2
        hcolPos hiNeg (hBA ▸ hiPos) hAfi
      have hXO' : A ∪ C ⊆ O' := Set.union_subset (hAO.trans hOO') hCO'
      have hXcl : IsClopen (Subtype.val ⁻¹' (A ∪ C) : Set O') := by
        refine isClopen_preimage_of_cover (D := O \ A) (hAo.union hCo)
          (isOpen_diff_pathComponentIn hO _) (fun y hy => ?_) ?_
        · rcases hO'cov hy with h | h
          · by_cases ha : y ∈ A
            · exact Or.inl (Or.inl ha)
            · exact Or.inr ⟨h, ha⟩
          · exact Or.inl (Or.inr h)
        · rw [Set.disjoint_left]
          rintro y (ha | hc) ⟨ho, hna⟩
          · exact hna ha
          · rcases hCOsub y hc ho with h | h
            · exact hna (hnegA h)
            · exact hna (hposA h)
      exact ⟨A ∪ C, hXO', hXcl, hX, Set.subset_union_left, hBA ▸ Set.subset_union_left,
        Set.subset_union_right⟩
    · have hBA : Disjoint B A := disjoint_pathComponentIn hAB
      have hCB : C ∩ B = G.posHalf j := by
        ext y
        constructor
        · rintro ⟨hc, hb⟩
          rcases hCOsub y hc (hBO hb) with h | h
          · exact (hBA.le_bot ⟨hb, hnegA h⟩).elim
          · exact h
        · intro h
          exact ⟨hposC h, hposB h⟩
      have hAV : A ∩ (C ∪ B) = G.negHalf j := by
        ext y
        constructor
        · rintro ⟨ha, hc | hb⟩
          · rcases hCOsub y hc (hAO ha) with h | h
            · exact h
            · exact (hBA.le_bot ⟨hposB h, ha⟩).elim
          · exact (hBA.le_bot ⟨hb, ha⟩).elim
        · intro h
          exact ⟨hnegA h, Or.inl (hnegC h)⟩
      have hgapcov : ∀ y, y ∈ (G.seamSurface j)ᶜ ∩ C → y ∈ G.negHalf j ∪ G.posHalf j :=
        fun y hy => (G.gap_eq j) ▸ hy
      have hcl1 : IsClopen (Subtype.val ⁻¹' (C ∩ B) :
          Set ((G.seamSurface j)ᶜ ∩ C : Set _)) := by
        refine isClopen_preimage_of_cover (D := A) (hCo.inter hBo) hAo (fun y hy => ?_) ?_
        · rcases hgapcov y hy with h | h
          · exact Or.inr (hnegA h)
          · exact Or.inl ⟨hposC h, hposB h⟩
        · rw [Set.disjoint_left]
          rintro y ⟨_, hb⟩ ha
          exact hBA.le_bot ⟨hb, ha⟩
      have hsub1 : C ∩ B ⊆ (G.seamSurface j)ᶜ ∩ C := fun y hy =>
        G.posHalf_subset_gap j (hCB ▸ hy)
      have hf1 : ∀ t, G.levelPos j t ∈ C ∩ B := fun t =>
        ⟨hposC (G.levelPos_mem_posHalf j t), hposB (G.levelPos_mem_posHalf j t)⟩
      have hs1 := surjective_toSubset_of_isClopen hsub1 hcl1 (G.levelPos j) hf1 t₀
        (G.bijective_gapLevel_pos j t₀).2
      have h1 := InjInto.union_of_amalgam hCo hBo (G.isPathConnected_seamCollar j) hBpc
        (hCB ▸ G.isPathConnected_posHalf j) (G.levelPos j) hf1 t₀ hs1 hcolPos hiPos
      have hCBfi := RegionFI.union_of_amalgam hCo hBo (G.isPathConnected_seamCollar j) hBpc
        (hCB ▸ G.isPathConnected_posHalf j) (G.levelPos j) hf1 t₀ hs1 hcolPos hiPos hCfi hBfi
      have hCBpc : IsPathConnected (C ∪ B) := (G.isPathConnected_seamCollar j).union hBpc
        ⟨G.levelPos j t₀, hposC (G.levelPos_mem_posHalf j t₀),
          hposB (G.levelPos_mem_posHalf j t₀)⟩
      have hcl2 : IsClopen (Subtype.val ⁻¹' (A ∩ (C ∪ B)) :
          Set ((G.seamSurface j)ᶜ ∩ C : Set _)) := by
        refine isClopen_preimage_of_cover (D := B) (hAo.inter (hCo.union hBo)) hBo
          (fun y hy => ?_) ?_
        · rcases hgapcov y hy with h | h
          · exact Or.inl (hAV ▸ h)
          · exact Or.inr (hposB h)
        · rw [Set.disjoint_left]
          rintro y ⟨ha, _⟩ hb
          exact hBA.le_bot ⟨hb, ha⟩
      have hsub2 : A ∩ (C ∪ B) ⊆ (G.seamSurface j)ᶜ ∩ C := fun y hy =>
        G.negHalf_subset_gap j (hAV ▸ hy)
      have hf2 : ∀ t, G.levelNeg j t ∈ A ∩ (C ∪ B) := fun t =>
        ⟨hnegA (G.levelNeg_mem_negHalf j t), Or.inl (hnegC (G.levelNeg_mem_negHalf j t))⟩
      have hX := RegionFI.union_of_amalgam hAo (hCo.union hBo) hApc hCBpc
        (hAV ▸ G.isPathConnected_negHalf j) (G.levelNeg j) hf2 t₀
        (surjective_toSubset_of_isClopen hsub2 hcl2 (G.levelNeg j) hf2 t₀
          (G.bijective_gapLevel_neg j t₀).2) hiNeg (h1.1 _ hcolNeg) hAfi hCBfi
      have hXO' : A ∪ (C ∪ B) ⊆ O' :=
        Set.union_subset (hAO.trans hOO') (Set.union_subset hCO' (hBO.trans hOO'))
      have hXcl : IsClopen (Subtype.val ⁻¹' (A ∪ (C ∪ B)) : Set O') := by
        refine isClopen_preimage_of_cover (D := (O \ A) ∩ (O \ B))
          (hAo.union (hCo.union hBo))
          ((isOpen_diff_pathComponentIn hO _).inter (isOpen_diff_pathComponentIn hO _))
          (fun y hy => ?_) ?_
        · rcases hO'cov hy with h | h
          · by_cases ha : y ∈ A
            · exact Or.inl (Or.inl ha)
            · by_cases hb : y ∈ B
              · exact Or.inl (Or.inr (Or.inr hb))
              · exact Or.inr ⟨⟨h, ha⟩, ⟨h, hb⟩⟩
          · exact Or.inl (Or.inr (Or.inl h))
        · rw [Set.disjoint_left]
          rintro y (ha | hc | hb) ⟨⟨ho, hna⟩, ⟨_, hnb⟩⟩
          · exact hna ha
          · rcases hCOsub y hc ho with h | h
            · exact hna (hnegA h)
            · exact hnb (hposB h)
          · exact hnb hb
      exact ⟨A ∪ (C ∪ B), hXO', hXcl, hX, Set.subset_union_left,
        fun y hy => Or.inr (Or.inr hy), fun y hy => Or.inr (Or.inl hy)⟩
  refine regionFI_of_forall_isClopen fun x hx => ?_
  by_cases hxX : x ∈ X
  · exact ⟨X, hXO', hxX, hXcl, hXfi⟩
  have hxO : x ∈ O := (hO'cov hx).resolve_right fun hc => hxX (hCX hc)
  set D := pathComponentIn O x with hDdef
  have hDA : Disjoint D A := disjoint_pathComponentIn fun h => hxX (hAX h)
  have hDB : Disjoint D B := disjoint_pathComponentIn fun h => hxX (hBX h)
  have hDO : D ⊆ O := pathComponentIn_subset
  refine ⟨D, hDO.trans hOO', mem_pathComponentIn_self hxO, ?_,
    hOfi.of_isClopen hDO (isClopen_preimage_pathComponentIn hO x)⟩
  refine isClopen_preimage_of_cover (D := (O \ D) ∪ C) (hO.pathComponentIn x)
    ((isOpen_diff_pathComponentIn hO x).union hCo) ?_ ?_
  · intro y hy
    rcases hO'cov hy with h | h
    · by_cases hd : y ∈ D
      · exact Or.inl hd
      · exact Or.inr (Or.inl ⟨h, hd⟩)
    · exact Or.inr (Or.inr h)
  · rw [Set.disjoint_left]
    rintro y hyD (⟨_, h⟩ | hyC)
    · exact h hyD
    · rcases hCOsub y hyC (hDO hyD) with h | h
      · exact hDA.le_bot ⟨hyD, hnegA h⟩
      · exact hDB.le_bot ⟨hyD, hposB h⟩

end Step

theorem regionFI_cutOpen (h0 : G.SeamLevelsInj ∅) (hbase : RegionFI (G.cutOpen ∅))
    (K : Finset (Fin G.pairing.count)) : RegionFI (G.cutOpen K) := by
  induction K using Finset.induction_on with
  | empty => exact hbase
  | insert j K hj ih => exact regionFI_insert hj (G.seamLevelsInj_of_empty h0 K) ih

theorem cutMap_cutOpenRetract (hext : G.externalCount = 0) (y : G.cutOpen ∅) :
    G.cutMap (G.cutOpenRetract hext y) = y := by
  change G.reconstruction (G.pairing.quotientMap
    (G.interiorDiffeomorph.symm ⟨y.1, G.mem_interiorImage hext y.2⟩ :
      G.cutCarrier.interior).1) = y.1
  rw [← G.interior_map, Diffeomorph.apply_symm_apply]

def cutOpenHomeoInterior (hext : G.externalCount = 0) :
    G.cutOpen ∅ ≃ₜ (G.cutCarrier.interior : Set G.cutCarrier.Carrier) where
  toFun := G.cutOpenToInterior hext
  invFun z := ⟨G.cutMap z, G.cutMap_mem_cutOpen_empty z.2⟩
  left_inv y := Subtype.ext (G.cutMap_cutOpenRetract hext y)
  right_inv z := Subtype.ext (G.cutOpenRetract_cutMap hext z.2 _)
  continuous_toFun := (G.cutOpenToInterior hext).continuous
  continuous_invFun := (G.continuous_cutMap.comp continuous_subtype_val).subtype_mk _

theorem bijective_pieceInteriorToPiece (i : Fin G.components.count)
    (y : G.cutCarrier.pieceInterior (G.components.piece i)) :
    Function.Bijective (FundamentalGroup.map (G.pieceInteriorToPiece i) y) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv (G.pieceInteriorHomotopyEquiv i)
  change Function.Bijective (E.functor.map :
    (FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk y) →
      (E.functor.obj (FundamentalGroupoid.mk y) ⟶
        E.functor.obj (FundamentalGroupoid.mk y)))
  exact E.fullyFaithfulFunctor.map_bijective _ _

theorem bijective_pieceInteriorToCutOpen (hext : G.externalCount = 0)
    (i : Fin G.components.count) (x : G.cutCarrier.pieceInterior (G.components.piece i)) :
    Function.Bijective (FundamentalGroup.map (G.pieceInteriorToCutOpen i) x) := by
  have hPI : (G.cutCarrier.pieceInterior (G.components.piece i) : Set G.cutCarrier.Carrier) ⊆
      (G.cutCarrier.interior : Set G.cutCarrier.Carrier) := fun y hy => hy.2
  have hpre : (Subtype.val ⁻¹' (G.cutCarrier.pieceInterior (G.components.piece i) :
      Set G.cutCarrier.Carrier) : Set (G.cutCarrier.interior : Set G.cutCarrier.Carrier)) =
      Subtype.val ⁻¹' (G.components.piece i : Set G.cutCarrier.Carrier) := by
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  have hcl : IsClopen (Subtype.val ⁻¹' (G.cutCarrier.pieceInterior (G.components.piece i) :
      Set G.cutCarrier.Carrier) : Set (G.cutCarrier.interior : Set G.cutCarrier.Carrier)) := by
    rw [hpre]
    exact ⟨(G.components.closed i).preimage continuous_subtype_val,
      (G.components.piece i).isOpen.preimage continuous_subtype_val⟩
  have he : ((G.cutOpenHomeoInterior hext : C(G.cutOpen ∅, _))).comp
      (G.pieceInteriorToCutOpen i) = inclusionMap hPI :=
    ContinuousMap.ext fun z => Subtype.ext (G.cutOpenRetract_cutMap hext z.2.2
      (G.cutMap_mem_cutOpen_empty z.2.2))
  have hb := bijective_inclusion_of_isClopen hPI hcl x
  rw [← he, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at hb
  exact (Function.Bijective.of_comp_iff' (bijective_map_homeomorph _ _) _).mp hb

theorem regionFI_cutOpen_empty (hext : G.externalCount = 0)
    (hvert : ∀ i (x : G.components.piece i),
      IndecomposableNoncyclic (FundamentalGroup (G.components.piece i) x)) :
    RegionFI (G.cutOpen ∅) := by
  intro y
  have hz : (G.cutOpenToInterior hext y : G.cutCarrier.Carrier) ∈
      ⋃ i, (G.components.piece i : Set G.cutCarrier.Carrier) := by
    rw [G.components.covers]
    exact Set.mem_univ _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  let w : G.cutCarrier.pieceInterior (G.components.piece i) :=
    ⟨G.cutOpenToInterior hext y, hi, (G.cutOpenToInterior hext y).2⟩
  have hw : G.pieceInteriorToCutOpen i w = y := Subtype.ext (G.cutMap_cutOpenRetract hext y)
  have h := (indecomposableNoncyclic_iff_of_bijective _ w
    (G.bijective_pieceInteriorToCutOpen hext i w)).mp
    ((indecomposableNoncyclic_iff_of_bijective _ w
      (G.bijective_pieceInteriorToPiece i w)).mpr (hvert i _))
  rw [hw] at h
  exact h

theorem indecomposableNoncyclic_of_vertex (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible)
    (hvert : ∀ i (x : G.components.piece i),
      IndecomposableNoncyclic (FundamentalGroup (G.components.piece i) x))
    (y : W.Carrier) : IndecomposableNoncyclic (FundamentalGroup W.Carrier y) := by
  have h := G.regionFI_cutOpen (G.seamLevelsInj_empty hext hports)
    (G.regionFI_cutOpen_empty hext hvert) Finset.univ
  rw [G.cutOpen_univ] at h
  exact (indecomposableNoncyclic_iff_of_bijective _ _
    (bijective_map_homeomorph (Homeomorph.Set.univ W.Carrier) ⟨y, Set.mem_univ y⟩)).mp
    (h ⟨y, Set.mem_univ y⟩)

end TorusPresentation

end GC.Seifert

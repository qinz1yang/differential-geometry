import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.GluingInjectionStep

/-!
# CP1-C: one collared-gluing step for components of `cutOpen K`

`step_CPC`: re-run of `injInto_insert` (`MultiSeamInjective.lean`) for general loops. If every
seam torus at the collar levels is `π₁`-injective into `cutOpen K` (`SeamLevelsInj K`), then every
path component of `cutOpen K` includes `π₁`-injectively into `cutOpen (insert j K)`.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.LongTime.CuspP1
open GC.Seifert

attribute [local instance] TorusPresentation.locallyPathConnectedSpace_carrier

section Step
variable {W : CompactCarrier.{u}} {G : TorusPresentation W} {j : Fin G.pairing.count}
  {K : Finset (Fin G.pairing.count)}

theorem step_CPC (hj : j ∉ K) (hK : G.SeamLevelsInj K) (x : W.Carrier) (hx : x ∈ G.cutOpen K) :
    Function.Injective (FundamentalGroup.map
      (inclusionMap ((pathComponentIn_subset : pathComponentIn (G.cutOpen K) x ⊆ G.cutOpen K).trans
        (G.cutOpen_subset_insert j K)))
      ⟨x, mem_pathComponentIn_self hx⟩) := by
  set O := G.cutOpen K with hOdef
  set O' := G.cutOpen (insert j K) with hO'def
  set C := G.seamCollar j with hCdef
  have hO : IsOpen O := G.isOpen_cutOpen K
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
  have hmerged : (∀ E : Set W.Carrier, E = A → ∀ h : E ⊆ O', IncInj_CPC h) ∧
      (∀ E : Set W.Carrier, E = B → ∀ h : E ⊆ O', IncInj_CPC h) := by
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
      have hX := IncInj.union_of_hnn_CPC hAo hCo hApc (G.isPathConnected_seamCollar j) hN
        (G.isOpen_negHalf j) (G.isOpen_posHalf j) (G.disjoint_negHalf_posHalf j)
        (G.isPathConnected_negHalf j) (G.isPathConnected_posHalf j) (G.levelNeg j)
        (G.levelPos j) hf₀ hf₁ t₀ (G.levelNeg_mem_negHalf j t₀) (G.levelPos_mem_posHalf j t₀)
        (bijective_toSubset_congr hAgap (G.levelNeg j) _ _ t₀ (G.bijective_gapLevel_neg j t₀))
        (G.bijective_collar_gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) t₀)
        (bijective_toSubset_congr hAgap (G.levelPos j) _ _ t₀
          (G.bijective_gapLevel_pos j t₀)).2
        hcolPos hiNeg (hBA ▸ hiPos)
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
      have hA'' : IncInj_CPC (Set.subset_union_left.trans hXO' : A ⊆ O') := fun y =>
        injective_inclusion_trans_CPC (Set.subset_union_left : A ⊆ A ∪ C) hXO' y (hX y)
          (injective_inclusion_of_isClopen hXO' hXcl _)
      refine ⟨fun E hE h => ?_, fun E hE h => ?_⟩
      · subst hE
        exact hA''
      · have hE' : E = A := hE.trans hBA
        subst hE'
        exact hA''
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
      have hcl1 : IsClopen (Subtype.val ⁻¹' (C ∩ B) : Set ((G.seamSurface j)ᶜ ∩ C : Set _)) := by
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
      have h1 := IncInj.union_of_amalgam_CPC hCo hBo (G.isPathConnected_seamCollar j) hBpc
        (hCB ▸ G.isPathConnected_posHalf j) (G.levelPos j) hf1 t₀
        (surjective_toSubset_of_isClopen hsub1 hcl1 (G.levelPos j) hf1 t₀
          (G.bijective_gapLevel_pos j t₀).2) hcolPos hiPos
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
      have h2 := IncInj.union_of_amalgam_CPC hAo (hCo.union hBo) hApc hCBpc
        (hAV ▸ G.isPathConnected_negHalf j) (G.levelNeg j) hf2 t₀
        (surjective_toSubset_of_isClopen hsub2 hcl2 (G.levelNeg j) hf2 t₀
          (G.bijective_gapLevel_neg j t₀).2) hiNeg (InjInto.mono Set.subset_union_left h1.1 hcolNeg)
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
      refine ⟨fun E hE h => ?_, fun E hE h => ?_⟩
      · subst hE
        exact fun y => injective_inclusion_trans_CPC (Set.subset_union_left : A ⊆ A ∪ (C ∪ B))
          hXO' y (h2.1 y) (injective_inclusion_of_isClopen hXO' hXcl _)
      · subst hE
        exact fun y => injective_inclusion_trans_CPC
          ((Set.subset_union_right : B ⊆ C ∪ B).trans (Set.subset_union_right : C ∪ B ⊆ A ∪ (C ∪ B)))
          hXO' y
          (injective_inclusion_trans_CPC (Set.subset_union_right : B ⊆ C ∪ B)
            (Set.subset_union_right : C ∪ B ⊆ A ∪ (C ∪ B)) y (h1.2 y) (h2.2 _))
          (injective_inclusion_of_isClopen hXO' hXcl _)
  have hother : ∀ D : Set W.Carrier, IsOpen D → D ⊆ O → IsOpen (O \ D) → Disjoint D A →
      Disjoint D B → ∀ h : D ⊆ O', IncInj_CPC h := by
    intro D hDo hDO hDc hDA hDB h
    have hcl : IsClopen (Subtype.val ⁻¹' D : Set O') := by
      refine isClopen_preimage_of_cover (D := (O \ D) ∪ C) hDo (hDc.union hCo) ?_ ?_
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
    exact injective_inclusion_of_isClopen h hcl
  have hxself : x ∈ pathComponentIn O x := mem_pathComponentIn_self hx
  by_cases hA' : x ∈ A
  · have hDA : pathComponentIn O x = A := pathComponentIn_congr hA'
    exact hmerged.1 _ hDA _ ⟨x, hxself⟩
  by_cases hB' : x ∈ B
  · have hDB : pathComponentIn O x = B := pathComponentIn_congr hB'
    exact hmerged.2 _ hDB _ ⟨x, hxself⟩
  exact hother _ (hO.pathComponentIn _) pathComponentIn_subset
    (isOpen_diff_pathComponentIn hO _) (disjoint_pathComponentIn hA')
    (disjoint_pathComponentIn hB') _ ⟨x, hxself⟩

end Step

end GC.LongTime.CuspP1

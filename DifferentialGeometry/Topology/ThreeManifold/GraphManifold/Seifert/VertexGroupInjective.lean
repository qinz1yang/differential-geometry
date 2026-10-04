import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MultiSeamInjective

/-!
# Vertex groups are injective when the ports are

Chapter 6, K19. For a torus presentation without external tori whose pieces have π₁-injective
ports (`pieceBoundaryTori … incompressible`, the shape of K10), the interior of every piece is
π₁-injective into `W` at every basepoint (`injective_pieceInterior_of_ports`), and so is every map
into `W` that factors π₁-injectively through `W` minus all seam tori
(`injective_comp_cutOpen_empty`). No separation hypothesis is used.

This re-runs the induction of K09c (`MultiSeamInjective`) over finsets `K` of seams with the
injectivity predicate generalised from torus maps to inclusions of arbitrary subsets:
`InclusionInj S S'` says `S ⊆ S'` and the inclusion is π₁-injective at every point of `S`. The
invariant `SeamLevelsInj K` of K09c holds for every `K` (`seamLevelsInj_of_empty`), and under it
the inclusion `cutOpen K ⊆ cutOpen (insert j K)` is `InclusionInj` (`inclusionInj_insert`): each
path component of `cutOpen K` is either one of the two components `A`, `B` met by the collar of
`j`, glued to it by the HNN step (`InclusionInj.union_of_hnn`) or by two amalgam steps
(`InclusionInj.union_of_amalgam`) inside a region clopen in `cutOpen (insert j K)`, or is itself
clopen there; a path component of an open set carries all of its π₁
(`inclusionInj_of_pathComponentIn`). Composing gives `cutOpen ∅ ⊆ W`
(`injective_cutOpen_empty`). A piece interior is clopen in the interior of the cut carrier, which
the inverse interior diffeomorphism identifies with `cutOpen ∅` (`cutOpenToInterior`).
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.Seifert

section Regions
variable {M : Type u} [TopologicalSpace M]

def InclusionInj (S S' : Set M) : Prop :=
  ∃ h : S ⊆ S', ∀ x : S, Function.Injective (FundamentalGroup.map (inclusionMap h) x)

theorem inclusionInj_refl (S : Set M) : InclusionInj S S :=
  ⟨subset_rfl, fun x =>
    injective_fundamentalGroup_map_of_leftInverse _ (inclusionMap subset_rfl) (fun _ => rfl) x⟩

theorem InclusionInj.trans {S S' S'' : Set M} (h : InclusionInj S S')
    (h' : InclusionInj S' S'') : InclusionInj S S'' := by
  obtain ⟨hs, hi⟩ := h
  obtain ⟨hs', hi'⟩ := h'
  refine ⟨hs.trans hs', fun x => ?_⟩
  have he : inclusionMap (hs.trans hs') = (inclusionMap hs').comp (inclusionMap hs) :=
    ContinuousMap.ext fun _ => rfl
  rw [he, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (hi' _).comp (hi x)

theorem inclusionInj_of_isClopen {S S' : Set M} (h : S ⊆ S')
    (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) : InclusionInj S S' :=
  ⟨h, injective_inclusion_of_isClopen h hcl⟩

theorem InjInto.of_inclusionInj {S S' : Set M} {f : C(Torus, M)} (h : InclusionInj S S')
    (hf : InjInto S f) : InjInto S' f :=
  hf.mono h.1 h.2

theorem inclusionInj_of_forall_preimage {A X : Set M} (h : A ⊆ X)
    (hA : ∀ a : (Subtype.val ⁻¹' A : Set X), Function.Injective
      (FundamentalGroup.map (subsetToAmbient (Subtype.val ⁻¹' A : Set X)) a)) :
    InclusionInj A X := by
  refine ⟨h, fun x => ?_⟩
  have he : inclusionMap h = (subsetToAmbient (Subtype.val ⁻¹' A : Set X)).comp
      ((preimageValHomeo X A h).symm : C(A, (Subtype.val ⁻¹' A : Set X))) :=
    ContinuousMap.ext fun _ => rfl
  rw [he, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (hA _).comp (injective_fundamentalGroup_map_of_leftInverse
    ((preimageValHomeo X A h).symm : C(A, (Subtype.val ⁻¹' A : Set X)))
    (preimageValHomeo X A h : C((Subtype.val ⁻¹' A : Set X), A))
    (preimageValHomeo X A h).apply_symm_apply x)

theorem inclusionInj_of_preimage {A X : Set M} (h : A ⊆ X) (hpc : IsPathConnected A)
    (a₀ : (Subtype.val ⁻¹' A : Set X)) (ha₀ : Function.Injective
      (FundamentalGroup.map (subsetToAmbient (Subtype.val ⁻¹' A : Set X)) a₀)) :
    InclusionInj A X := by
  have := pathConnectedSpace_preimage hpc h
  exact inclusionInj_of_forall_preimage h fun a =>
    (GC.Topology.injective_fundamentalGroup_map_iff _ a₀ a).mp ha₀

theorem inclusionInj_of_pathComponentIn [LocallyPathConnectedSpace M] {O O' : Set M}
    (hO : IsOpen O) (hOO' : O ⊆ O') (h : ∀ p ∈ O, InclusionInj (pathComponentIn O p) O') :
    InclusionInj O O' := by
  refine ⟨hOO', fun x => ?_⟩
  have hx : (x : M) ∈ pathComponentIn O (x : M) := mem_pathComponentIn_self x.2
  have hDO : pathComponentIn O (x : M) ⊆ O := pathComponentIn_subset
  have hcl : IsClopen (Subtype.val ⁻¹' pathComponentIn O (x : M) : Set O) := by
    refine isClopen_preimage_of_cover (hO.pathComponentIn _) (isOpen_diff_pathComponentIn hO _)
      (fun y hy => ?_) Set.disjoint_sdiff_right
    by_cases hd : y ∈ pathComponentIn O (x : M)
    · exact Or.inl hd
    · exact Or.inr ⟨hy, hd⟩
  have hs := surjective_fundamentalGroup_map_of_clopen (inclusionMap hDO)
    (clopenRetraction _ O hcl ⟨(x : M), hx⟩)
    (fun z => Subtype.ext (clopenRetraction_apply_of_mem _ O hcl _ _ z.2)) _ hcl
    (fun y hy => Subtype.ext (clopenRetraction_apply_of_mem _ O hcl _ y hy)) ⟨(x : M), hx⟩ hx
  obtain ⟨hD, hinj⟩ := h x x.2
  have he : inclusionMap hD = (inclusionMap hOO').comp (inclusionMap hDO) :=
    ContinuousMap.ext fun _ => rfl
  have hc := hinj ⟨(x : M), hx⟩
  rw [he] at hc
  exact injective_fundamentalGroup_map_of_comp (inclusionMap hDO) (inclusionMap hOO')
    ⟨(x : M), hx⟩ hs hc

theorem InclusionInj.union_of_amalgam {A V : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hAVpc : IsPathConnected (A ∩ V))
    (f : C(Torus, M)) (hf : ∀ t, f t ∈ A ∩ V) (t₀ : Torus)
    (hsurj : Function.Surjective (FundamentalGroup.map (toSubset f (A ∩ V) hf) t₀))
    (hfA : InjInto A f) (hfV : InjInto V f) :
    InclusionInj A (A ∪ V) ∧ InclusionInj V (A ∪ V) := by
  have hAX : A ⊆ A ∪ V := Set.subset_union_left
  have hVX : V ⊆ A ∪ V := Set.subset_union_right
  have hIX : A ∩ V ⊆ A ∪ V := Set.inter_subset_left.trans hAX
  have hU'o : IsOpen (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) :=
    hA.preimage continuous_subtype_val
  have hV'o : IsOpen (Subtype.val ⁻¹' V : Set (A ∪ V : Set M)) :=
    hV.preimage continuous_subtype_val
  have hcov : (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∪ Subtype.val ⁻¹' V = Set.univ :=
    Set.eq_univ_of_forall fun y => y.2
  have := pathConnectedSpace_preimage hApc hAX
  have := pathConnectedSpace_preimage hVpc hVX
  have hI : PathConnectedSpace ↑((Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩
      Subtype.val ⁻¹' V) := pathConnectedSpace_preimage hAVpc hIX
  let F := liftTo (A ∪ V) (A ∩ V) hIX f hf
  have hFs : Function.Surjective (FundamentalGroup.map F t₀) :=
    surjective_liftTo (A ∪ V) (A ∩ V) hIX f hf t₀ hsurj
  have hFU : Function.Injective (FundamentalGroup.map ((interToLeft
      (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F) t₀) :=
    (injective_liftTo_iff (A ∪ V) A hAX f (fun t => (hf t).1) t₀).mpr (hfA.2 t₀)
  have hFV : Function.Injective (FundamentalGroup.map ((interToRight
      (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F) t₀) :=
    (injective_liftTo_iff (A ∪ V) V hVX f (fun t => (hf t).2) t₀).mpr (hfV.2 t₀)
  have hl := injective_fundamentalGroup_map_of_comp F _ t₀ hFs hFU
  have hr := injective_fundamentalGroup_map_of_comp F _ t₀ hFs hFV
  exact ⟨inclusionInj_of_preimage hAX hApc _
      (injective_fundamentalGroup_map_left _ _ hU'o hV'o hcov (F t₀) hl hr),
    inclusionInj_of_preimage hVX hVpc _
      (injective_fundamentalGroup_map_right _ _ hU'o hV'o hcov (F t₀) hl hr)⟩

theorem InclusionInj.union_of_hnn {A V N₀ N₁ : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hN : A ∩ V = N₀ ∪ N₁)
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hdisj : Disjoint N₀ N₁)
    (hN₀pc : IsPathConnected N₀) (hN₁pc : IsPathConnected N₁) (f₀ f₁ : C(Torus, M))
    (hf₀ : ∀ t, f₀ t ∈ A ∩ V) (hf₁ : ∀ t, f₁ t ∈ A ∩ V) (t₀ : Torus) (hf₀N : f₀ t₀ ∈ N₀)
    (hf₁N : f₁ t₀ ∈ N₁)
    (hb₀ : Function.Bijective (FundamentalGroup.map (toSubset f₀ (A ∩ V) hf₀) t₀))
    (hb₀V : Function.Bijective (FundamentalGroup.map (toSubset f₀ V (fun t => (hf₀ t).2)) t₀))
    (hs₁ : Function.Surjective (FundamentalGroup.map (toSubset f₁ (A ∩ V) hf₁) t₀))
    (hi₁V : InjInto V f₁) (hi₀A : InjInto A f₀) (hi₁A : InjInto A f₁) :
    InclusionInj A (A ∪ V) := by
  have hAX : A ⊆ A ∪ V := Set.subset_union_left
  have hVX : V ⊆ A ∪ V := Set.subset_union_right
  have hIX : A ∩ V ⊆ A ∪ V := Set.inter_subset_left.trans hAX
  let F₀ := liftTo (A ∪ V) (A ∩ V) hIX f₀ hf₀
  let F₁ := liftTo (A ∪ V) (A ∩ V) hIX f₁ hf₁
  have hF₀ := bijective_liftTo (A ∪ V) (A ∩ V) hIX f₀ hf₀ t₀ hb₀
  have hF₁ := surjective_liftTo (A ∪ V) (A ∩ V) hIX f₁ hf₁ t₀ hs₁
  have hsplit : ∀ y : M, y ∈ A ∩ V → (y ∈ N₀ ↔ y ∉ N₁) := fun y hy => by
    rw [hN] at hy
    rcases hy with h0 | h1
    · exact ⟨fun _ h1 => hdisj.le_bot ⟨h0, h1⟩, fun _ => h0⟩
    · exact ⟨fun h0 => (hdisj.le_bot ⟨h0, h1⟩).elim, fun h => (h h1).elim⟩
  let K : TwoComponentCover (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V) :=
    { left_connected := pathConnectedSpace_preimage hApc hAX
      right_connected := pathConnectedSpace_preimage hVpc hVX
      isOpen_left := hA.preimage continuous_subtype_val
      isOpen_right := hV.preimage continuous_subtype_val
      cover := Set.eq_univ_of_forall fun y => y.2
      base := F₀ t₀
      far := F₁ t₀
      not_joined := not_joined_of_separated
        ⟨fun y : ↑((Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩ Subtype.val ⁻¹' V) => y.1.1,
          continuous_subtype_val.comp continuous_subtype_val⟩ hN₀ hN₁ hdisj
        (fun y => hN ▸ y.2) hf₀N hf₁N
      joined := fun a => by
        have ha : (a : M) ∈ A ∩ V := a.2
        have hsub : ∀ N : Set M, N ⊆ A ∩ V → (Subtype.val ⁻¹' N : Set (A ∪ V : Set M)) ⊆
            (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩ Subtype.val ⁻¹' V :=
          fun N hNs y hy => hNs hy
        have hN₀s : N₀ ⊆ A ∩ V := hN ▸ Set.subset_union_left
        have hN₁s : N₁ ⊆ A ∩ V := hN ▸ Set.subset_union_right
        by_cases h0 : (a : M) ∈ N₀
        · exact Or.inl ((((hN₀pc.preimage_coe (hN₀s.trans hIX)).joinedIn _ hf₀N _ h0).mono
            (hsub N₀ hN₀s)).joined_subtype)
        · have h1 : (a : M) ∈ N₁ := by
            by_contra h1
            exact h0 ((hsplit _ ha).mpr h1)
          exact Or.inr ((((hN₁pc.preimage_coe (hN₁s.trans hIX)).joinedIn _ hf₁N _ h1).mono
            (hsub N₁ hN₁s)).joined_subtype)
      right_bijective := bijective_fundamentalGroup_map_of_comp F₀ _ t₀ hF₀
        (bijective_liftTo (A ∪ V) V hVX f₀ (fun t => (hf₀ t).2) t₀ hb₀V)
      left_injective := injective_fundamentalGroup_map_of_comp F₀ _ t₀ hF₀.2
        ((injective_liftTo_iff (A ∪ V) A hAX f₀ (fun t => (hf₀ t).1) t₀).mpr (hi₀A.2 t₀))
      left_injective_far := injective_fundamentalGroup_map_of_comp F₁ _ t₀ hF₁
        ((injective_liftTo_iff (A ∪ V) A hAX f₁ (fun t => (hf₁ t).1) t₀).mpr (hi₁A.2 t₀))
      right_injective_far := injective_fundamentalGroup_map_of_comp F₁ _ t₀ hF₁
        ((injective_liftTo_iff (A ∪ V) V hVX f₁ (fun t => (hf₁ t).2) t₀).mpr (hi₁V.2 t₀)) }
  exact inclusionInj_of_preimage hAX hApc _ K.injective_fundamentalGroup_map_left

end Regions

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

attribute [local instance] locallyPathConnectedSpace_carrier

section Step
variable {G} {j : Fin G.pairing.count} {K : Finset (Fin G.pairing.count)}

theorem inclusionInj_insert (hj : j ∉ K) (hK : G.SeamLevelsInj K) :
    InclusionInj (G.cutOpen K) (G.cutOpen (insert j K)) := by
  set O := G.cutOpen K
  set O' := G.cutOpen (insert j K)
  set C := G.seamCollar j
  have hO : IsOpen O := G.isOpen_cutOpen K
  have hgap' : C ∩ O = G.negHalf j ∪ G.posHalf j :=
    (G.seamCollar_inter_cutOpen j hj).trans (G.gap_eq j)
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
  set A := pathComponentIn O (G.levelNeg j t₀)
  set B := pathComponentIn O (G.levelPos j t₀)
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
  have hmerged : InclusionInj A O' ∧ InclusionInj B O' := by
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
      have hX := InclusionInj.union_of_hnn hAo hCo hApc (G.isPathConnected_seamCollar j) hN
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
      have hY := inclusionInj_of_isClopen hXO' hXcl
      refine ⟨hX.trans hY, ?_⟩
      rw [hBA]
      exact hX.trans hY
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
      have h1 := InclusionInj.union_of_amalgam hCo hBo (G.isPathConnected_seamCollar j) hBpc
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
      have h2 := InclusionInj.union_of_amalgam hAo (hCo.union hBo) hApc hCBpc
        (hAV ▸ G.isPathConnected_negHalf j) (G.levelNeg j) hf2 t₀
        (surjective_toSubset_of_isClopen hsub2 hcl2 (G.levelNeg j) hf2 t₀
          (G.bijective_gapLevel_neg j t₀).2) hiNeg (hcolNeg.of_inclusionInj h1.1)
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
      have hY := inclusionInj_of_isClopen hXO' hXcl
      exact ⟨h2.1.trans hY, h1.2.trans (h2.2.trans hY)⟩
  refine inclusionInj_of_pathComponentIn hO hOO' fun p _ => ?_
  by_cases hA' : p ∈ A
  · rw [pathComponentIn_congr hA']
    exact hmerged.1
  by_cases hB' : p ∈ B
  · rw [pathComponentIn_congr hB']
    exact hmerged.2
  have hDA : Disjoint (pathComponentIn O p) A := disjoint_pathComponentIn hA'
  have hDB : Disjoint (pathComponentIn O p) B := disjoint_pathComponentIn hB'
  refine inclusionInj_of_isClopen (pathComponentIn_subset.trans hOO')
    (isClopen_preimage_of_cover (D := (O \ pathComponentIn O p) ∪ C) (hO.pathComponentIn p)
      ((isOpen_diff_pathComponentIn hO p).union hCo) (fun y hy => ?_) ?_)
  · rcases hO'cov hy with h | h
    · by_cases hd : y ∈ pathComponentIn O p
      · exact Or.inl hd
      · exact Or.inr (Or.inl ⟨h, hd⟩)
    · exact Or.inr (Or.inr h)
  · rw [Set.disjoint_left]
    rintro y hyD (⟨_, h⟩ | hyC)
    · exact h hyD
    · rcases hCOsub y hyC (pathComponentIn_subset hyD) with h | h
      · exact hDA.le_bot ⟨hyD, hnegA h⟩
      · exact hDB.le_bot ⟨hyD, hposB h⟩

end Step

theorem seamLevelsInj_of_empty (h0 : G.SeamLevelsInj ∅) (K : Finset (Fin G.pairing.count)) :
    G.SeamLevelsInj K := by
  induction K using Finset.induction_on with
  | empty => exact h0
  | insert j K hj ih =>
    exact fun k => ⟨injInto_insert hj ih _ (ih k).1, injInto_insert hj ih _ (ih k).2⟩

theorem inclusionInj_cutOpen (h0 : G.SeamLevelsInj ∅) (K : Finset (Fin G.pairing.count)) :
    InclusionInj (G.cutOpen ∅) (G.cutOpen K) := by
  induction K using Finset.induction_on with
  | empty => exact inclusionInj_refl _
  | insert j K hj ih => exact ih.trans (inclusionInj_insert hj (G.seamLevelsInj_of_empty h0 K))

theorem injective_cutOpen_empty (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (y : G.cutOpen ∅) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient (G.cutOpen ∅)) y) := by
  obtain ⟨h, hinj⟩ := G.inclusionInj_cutOpen (G.seamLevelsInj_empty hext hports) Finset.univ
  have he : subsetToAmbient (G.cutOpen ∅) =
      (subsetToAmbient (G.cutOpen Finset.univ)).comp (inclusionMap h) :=
    ContinuousMap.ext fun _ => rfl
  have hcl : IsClopen (G.cutOpen Finset.univ) := by
    rw [G.cutOpen_univ]
    exact isClopen_univ
  rw [he, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (injective_subsetToAmbient_of_isClopen _ hcl _).comp (hinj y)

theorem injective_comp_cutOpen_empty (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) {X : Type*} [TopologicalSpace X]
    (g : C(X, G.cutOpen ∅)) (x : X) (hg : Function.Injective (FundamentalGroup.map g x)) :
    Function.Injective (FundamentalGroup.map ((subsetToAmbient (G.cutOpen ∅)).comp g) x) := by
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (G.injective_cutOpen_empty hext hports (g x)).comp hg

section Pieces
variable {G}

private theorem mem_block_of_mem_seamSurface {j : Fin G.pairing.count}
    {x : G.cutCarrier.Carrier} (h : G.cutMap x ∈ G.seamSurface j) :
    ∃ k, x ∈ G.pairing.gluing.block k := by
  obtain ⟨t, ht⟩ := h
  rw [seamTorus_eq_cutMap] at ht
  rcases Quotient.exact (G.reconstruction.injective ht) with h | ⟨k, hk, rfl⟩
  · exact ⟨j, Or.inl (h ▸ (G.pairing.leftParam j t).2)⟩
  · exact ⟨k, G.pairing.gluing.flip_mem_block hk⟩

theorem cutMap_mem_cutOpen_empty {x : G.cutCarrier.Carrier}
    (hx : G.cutCarrier.model.IsInteriorPoint x) : G.cutMap x ∈ G.cutOpen ∅ := by
  refine G.mem_cutOpen.mpr fun j _ hj => ?_
  obtain ⟨k, hk⟩ := mem_block_of_mem_seamSurface hj
  have hb : x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier := by
    rw [G.cut_boundary_exhausted]
    exact Or.inl (Set.mem_iUnion.mpr ⟨k, hk⟩)
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint] at hx
  exact hx hb

end Pieces

def cutOpenToInterior (hext : G.externalCount = 0) :
    C(G.cutOpen ∅, (G.cutCarrier.interior : Set G.cutCarrier.Carrier)) :=
  ⟨fun y => ⟨G.cutOpenRetract hext y,
      (G.interiorDiffeomorph.symm ⟨y.1, G.mem_interiorImage hext y.2⟩).2⟩,
    (G.cutOpenRetract hext).continuous.subtype_mk _⟩

def pieceInteriorToCutOpen (i : Fin G.components.count) :
    C(G.cutCarrier.pieceInterior (G.components.piece i), G.cutOpen ∅) :=
  ⟨fun x => ⟨G.cutMap x, G.cutMap_mem_cutOpen_empty x.2.2⟩,
    ((G.reconstruction.continuous.comp G.pairing.quotientMap.continuous).comp
      continuous_subtype_val).subtype_mk _⟩

def pieceInteriorToCarrier (i : Fin G.components.count) :
    C(G.cutCarrier.pieceInterior (G.components.piece i), W.Carrier) :=
  ⟨fun x => G.cutMap x,
    (G.reconstruction.continuous.comp G.pairing.quotientMap.continuous).comp
      continuous_subtype_val⟩

theorem pieceInteriorToCarrier_eq (i : Fin G.components.count) :
    G.pieceInteriorToCarrier i =
      (subsetToAmbient (G.cutOpen ∅)).comp (G.pieceInteriorToCutOpen i) :=
  ContinuousMap.ext fun _ => rfl

theorem injective_pieceInteriorToCutOpen (hext : G.externalCount = 0)
    (i : Fin G.components.count) (x : G.cutCarrier.pieceInterior (G.components.piece i)) :
    Function.Injective (FundamentalGroup.map (G.pieceInteriorToCutOpen i) x) := by
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
  have he : (G.cutOpenToInterior hext).comp (G.pieceInteriorToCutOpen i) = inclusionMap hPI :=
    ContinuousMap.ext fun z => Subtype.ext (G.cutOpenRetract_cutMap hext z.2.2
      (G.cutMap_mem_cutOpen_empty z.2.2))
  apply GC.Topology.injective_inner_of_composite _ (G.cutOpenToInterior hext) x
  rw [he]
  exact injective_inclusion_of_isClopen hPI hcl x

theorem injective_pieceInterior_of_ports (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (i : Fin G.components.count)
    (x : G.cutCarrier.pieceInterior (G.components.piece i)) :
    Function.Injective (FundamentalGroup.map (G.pieceInteriorToCarrier i) x) := by
  rw [G.pieceInteriorToCarrier_eq i]
  exact G.injective_comp_cutOpen_empty hext hports _ x
    (G.injective_pieceInteriorToCutOpen hext i x)

section Closed
variable {P : ConnectedClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier P))

theorem injective_pieceInterior_of_ports_closed
    (hports : ∀ i, (T.pieceBoundaryTori i).incompressible) (i : Fin T.components.count)
    (x : T.cutCarrier.pieceInterior (T.components.piece i)) :
    Function.Injective (FundamentalGroup.map (T.pieceInteriorToCarrier i) x) :=
  T.injective_pieceInterior_of_ports T.externalCount_eq_zero hports i x

end Closed

end TorusPresentation

end GC.Seifert

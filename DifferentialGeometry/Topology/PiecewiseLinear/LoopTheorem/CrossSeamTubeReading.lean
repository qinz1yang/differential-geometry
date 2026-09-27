/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubePages
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceReading
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isOpen_image_crossSeamBox {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {chart : (ℝ × ℝ) × ℝ → M}
    (hchart : ContinuousOn chart spliceCylinder) (hinjc : InjOn chart spliceCylinder) :
    IsOpen (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)) := by
  have hBcyl : (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1 ⊆ spliceCylinder :=
    prod_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) Ioo_subset_Icc_self
  have hBo : IsOpen ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1) :=
    (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo
  have hU : IsOpen (spliceEmbedding '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)) :=
    spliceEmbedding.toHomeomorph.isOpenMap _ hBo
  have hc : ContinuousOn (chart ∘ spliceEmbedding.symm)
      (spliceEmbedding '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)) := by
    refine (hchart.mono hBcyl).comp spliceEmbedding.symm.continuous.continuousOn ?_
    rintro _ ⟨q, hq, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hq
  have hi : InjOn (chart ∘ spliceEmbedding.symm)
      (spliceEmbedding '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)) := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ hqq
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] at hqq
    rw [hinjc (hBcyl hq) (hBcyl hq') hqq]
  have h := isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hU hc hi
  rwa [image_comp, spliceEmbedding.symm_image_image] at h

theorem disjoint_crossSeamPage_of_class {X : Type*} [TopologicalSpace X] [T2Space X]
    {chart : (ℝ × ℝ) × ℝ → X} {f : EuclideanSpace ℝ (Fin 2) → X}
    {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))} (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsClosed Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) {i j : Fin 4} (hij : i ≠ j)
    (hi : Disjoint J₂ (crossSeamPage chart f Dom i))
    (hj : Disjoint J₁ (crossSeamPage chart f Dom j)) :
    Disjoint (crossSeamPage chart f Dom i) (crossSeamPage chart f Dom j) := by
  rw [disjoint_left]
  intro x hxi hxj
  obtain ⟨hxD, q, hq, hqx⟩ := crossSeamPage_subset_preimage hchart hDom hf i hxi
  obtain ⟨-, q', hq', hq'x⟩ := crossSeamPage_subset_preimage hchart hDom hf j hxj
  have hqq : q = q' := hinjc (crossSheetOf_subset_spliceCylinder i hq)
    (crossSheetOf_subset_spliceCylinder j hq') (hqx.trans hq'x.symm)
  rw [← hqq] at hq'
  have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) :=
    ⟨hxD, q, crossSheetOf_inter_subset hij ⟨hq, hq'⟩, hqx⟩
  rw [hJ] at hxJ
  rcases hxJ with h | h
  · exact disjoint_left.mp hj h hxj
  · exact disjoint_left.mp hi h hxi

theorem nonempty_plCrossSeamReading_of_crossSeamPage {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {chart : (ℝ × ℝ) × ℝ → M}
    (hPL : PLSeamTubeChart M chart) (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) {G : SingularTwoCell M}
    {J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : G.domain ∩ ⇑G ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hJ₁ : IsClosed J₁)
    (hJ₂ : IsClosed J₂) (hJJ : Disjoint J₁ J₂) (hinj₁ : InjOn (⇑G) J₁) (hinj₂ : InjOn (⇑G) J₂)
    (hsurj₁ : chart '' spliceCore ⊆ ⇑G '' J₁) (hsurj₂ : chart '' spliceCore ⊆ ⇑G '' J₂)
    (huniq : ∀ x ∈ G.domain, ∀ y ∈ G.domain, G x = G y →
      G x ∈ chart '' (crossingFigure \ spliceCore) → x = y)
    (himage : ∀ x ∈ G.domain, G x ∈ chart '' spliceCylinder → G x ∈ chart '' crossingFigure)
    (hsurj : chart '' crossingFigure ⊆ ⇑G '' G.domain) {BdM : Set M}
    (htube : chart '' spliceCylinder ∩ BdM = chart '' spliceEndDisks)
    (hfront : ∀ x ∈ frontier G.domain, G x ∈ BdM)
    (hbd : ∀ x ∈ G.domain, G x ∈ BdM → G x ∈ chart '' (crossingFigure \ spliceCore) →
      x ∈ frontier G.domain)
    (h0 : J₁ ⊆ crossSeamPage chart G G.domain 0) (h3 : J₁ ⊆ crossSeamPage chart G G.domain 3)
    (h1 : J₂ ⊆ crossSeamPage chart G G.domain 1) (h2 : J₂ ⊆ crossSeamPage chart G G.domain 2) :
    Nonempty (PLCrossSeamReading chart G) := by
  have hDomB := G.isPLBall_domain
  have hDom : IsCompact G.domain := hDomB.isPolyhedron.isCompact
  have hf := G.continuousOn
  have hopen := isOpen_image_crossSeamBox hchart hinjc
  have hψ : IsPiecewiseAffineOn (Function.invFunOn chart spliceCylinder ∘ ⇑G)
      (G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder)) := by
    have h := hPL.piece.isPiecewiseAffineOn_invFunOn_comp G.isPLOn
    rwa [hPL.map_eq, hPL.space_eq] at h
  have hhu : ∀ i, ∀ x ∈ G.domain, ∀ y ∈ G.domain, G x = G y →
      G x ∈ chart '' crossOpenSheetOf i → x = y := fun i x hx y hy hxy hm =>
    huniq x hx y hy hxy (image_mono (show crossOpenSheetOf i ⊆ crossingFigure \ spliceCore from
      fun w hw => ⟨crossSheetOf_subset_crossingFigure i (crossOpenSheetOf_subset_crossSheetOf i hw),
        disjoint_left.mp (disjoint_crossOpenSheetOf_spliceCore i) hw⟩) hm)
  have hsu : ∀ i, chart '' crossOpenSheetOf i ⊆ ⇑G '' G.domain := fun i =>
    (image_mono ((crossOpenSheetOf_subset_crossSheetOf i).trans
      (crossSheetOf_subset_crossingFigure i))).trans hsurj
  have hJ' : G.domain ∩ ⇑G ⁻¹' (chart '' spliceCore) = J₂ ∪ J₁ := by rw [hJ, union_comm]
  have hcne : spliceCore.Nonempty :=
    ⟨(((0 : ℝ), (0 : ℝ)), 0), ⟨mem_singleton _, ⟨le_rfl, zero_le_one⟩⟩⟩
  obtain ⟨y₁, hy₁⟩ := hcne.image chart
  obtain ⟨z₁, hz₁, -⟩ := hsurj₁ hy₁
  obtain ⟨z₂, hz₂, -⟩ := hsurj₂ hy₁
  have hcl₁ : ∀ i, J₁ ⊆ crossSeamPage chart G G.domain i →
      Disjoint J₂ (crossSeamPage chart G G.domain i) := fun i hi =>
    (crossSeamPage_class hchart hinjc hDom hf hJ hJ₁ hJ₂ hJJ hinj₁ hinj₂ hsurj₁ hsurj₂ (hhu i)
      (hsu i)).elim (fun h => h.2) fun h => absurd (hi hz₁) (disjoint_left.mp h.2 hz₁)
  have hcl₂ : ∀ i, J₂ ⊆ crossSeamPage chart G G.domain i →
      Disjoint J₁ (crossSeamPage chart G G.domain i) := fun i hi =>
    (crossSeamPage_class hchart hinjc hDom hf hJ hJ₁ hJ₂ hJJ hinj₁ hinj₂ hsurj₁ hsurj₂ (hhu i)
      (hsu i)).elim (fun h => absurd (hi hz₂) (disjoint_left.mp h.2 hz₂)) fun h => h.2
  have hPLh₁ : ∀ i, J₁ ⊆ crossSeamPage chart G G.domain i →
      IsPLHomeomorphOn (Function.invFunOn chart spliceCylinder ∘ ⇑G)
        (crossSeamPage chart G G.domain i) (crossSheetOf i) := fun i hi =>
    isPLHomeomorphOn_crossSeamPage hchart hinjc hDom hf hJ hinj₁ hsurj₁ (hhu i) (hsu i) hψ hi
      (hcl₁ i hi)
  have hPLh₂ : ∀ i, J₂ ⊆ crossSeamPage chart G G.domain i →
      IsPLHomeomorphOn (Function.invFunOn chart spliceCylinder ∘ ⇑G)
        (crossSeamPage chart G G.domain i) (crossSheetOf i) := fun i hi =>
    isPLHomeomorphOn_crossSeamPage hchart hinjc hDom hf hJ' hinj₂ hsurj₂ (hhu i) (hsu i) hψ hi
      (hcl₂ i hi)
  have hbdy : ∀ i, (J₁ ⊆ crossSeamPage chart G G.domain i ∨
      J₂ ⊆ crossSeamPage chart G G.domain i) → ∀ x ∈ crossSeamPage chart G G.domain i,
      (x ∈ frontier G.domain ↔ ((Function.invFunOn chart spliceCylinder ∘ ⇑G) x).2 = 0 ∨
        ((Function.invFunOn chart spliceCylinder ∘ ⇑G) x).2 = 1) := by
    rintro i (hi | hi) x hx
    · exact mem_frontier_iff_of_mem_crossSeamPage hchart hinjc hDom hf hJ hinj₁ hsurj₁ (hhu i)
        (hsu i) hi (hcl₁ i hi) htube hfront hbd hx
    · exact mem_frontier_iff_of_mem_crossSeamPage hchart hinjc hDom hf hJ' hinj₂ hsurj₂ (hhu i)
        (hsu i) hi (hcl₂ i hi) htube hfront hbd hx
  have hcov : ∀ x ∈ G.domain, G x ∈ chart '' spliceCylinder →
      x ∈ crossSeamPage chart G G.domain 0 ∨ x ∈ crossSeamPage chart G G.domain 1 ∨
        x ∈ crossSeamPage chart G G.domain 2 ∨ x ∈ crossSeamPage chart G G.domain 3 := by
    intro x hx hfx
    obtain ⟨i, hi⟩ := exists_mem_crossSeamPage_of_mem himage hJ ⟨0, h0⟩ ⟨1, h1⟩ hx hfx
    fin_cases i
    exacts [Or.inl hi, Or.inr (Or.inl hi), Or.inr (Or.inr (Or.inl hi)), Or.inr (Or.inr (Or.inr hi))]
  have hsub : ∀ i, crossSeamPage chart G G.domain i ⊆
      G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder) := fun i =>
    (crossSeamPage_subset_preimage hchart hDom.isClosed hf i).trans
      (inter_subset_inter_right _ (preimage_mono (image_mono
        (crossSheetOf_subset_spliceCylinder i))))
  have hsource : (crossSeamPage chart G G.domain 0 ∪ crossSeamPage chart G G.domain 3) ∪
      (crossSeamPage chart G G.domain 2 ∪ crossSeamPage chart G G.domain 1) =
        G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder) := by
    apply Subset.antisymm
    · exact union_subset (union_subset (hsub 0) (hsub 3)) (union_subset (hsub 2) (hsub 1))
    · rintro x ⟨hx, hfx⟩
      rcases hcov x hx hfx with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
  have hfrontier : ∀ z ∈ G.domain, G z ∈ chart '' spliceCylinder →
      (z ∈ frontier G.domain ↔ ((Function.invFunOn chart spliceCylinder ∘ ⇑G) z).2 = 0 ∨
        ((Function.invFunOn chart spliceCylinder ∘ ⇑G) z).2 = 1) := by
    intro z hz hfz
    rcases hcov z hz hfz with h | h | h | h
    · exact hbdy 0 (Or.inl h0) z h
    · exact hbdy 1 (Or.inr h1) z h
    · exact hbdy 2 (Or.inr h2) z h
    · exact hbdy 3 (Or.inl h3) z h
  have hwall₁ : ∀ i, J₁ ⊆ crossSeamPage chart G G.domain i →
      ∀ x ∈ crossSeamPage chart G G.domain i ∩ closure (G.domain \
        ((crossSeamPage chart G G.domain 0 ∪ crossSeamPage chart G G.domain 3) ∪
          (crossSeamPage chart G G.domain 2 ∪ crossSeamPage chart G G.domain 1))),
      (Function.invFunOn chart spliceCylinder ∘ ⇑G) x ∈
        spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 := by
    intro i hi x hx
    rw [hsource] at hx
    exact crossSeamPage_wall hchart hinjc hDomB hf hJ hinj₁ hsurj₁ (hhu i) (hsu i) hi
      (hcl₁ i hi) hopen hfrontier hx.1 hx.2
  have hwall₂ : ∀ i, J₂ ⊆ crossSeamPage chart G G.domain i →
      ∀ x ∈ crossSeamPage chart G G.domain i ∩ closure (G.domain \
        ((crossSeamPage chart G G.domain 0 ∪ crossSeamPage chart G G.domain 3) ∪
          (crossSeamPage chart G G.domain 2 ∪ crossSeamPage chart G G.domain 1))),
      (Function.invFunOn chart spliceCylinder ∘ ⇑G) x ∈
        spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 := by
    intro i hi x hx
    rw [hsource] at hx
    exact crossSeamPage_wall hchart hinjc hDomB hf hJ' hinj₂ hsurj₂ (hhu i) (hsu i) hi
      (hcl₂ i hi) hopen hfrontier hx.1 hx.2
  have hG : ∀ i, EqOn (⇑G) (chart ∘ (Function.invFunOn chart spliceCylinder ∘ ⇑G))
      (crossSeamPage chart G G.domain i) := fun i x hx =>
    (Function.invFunOn_eq (hsub i hx).2).symm
  have hsurjI : ∀ {i j : Fin 4} {J : Set (EuclideanSpace ℝ (Fin 2))}, i ≠ j →
      chart '' spliceCore ⊆ ⇑G '' J → J ⊆ crossSeamPage chart G G.domain i →
      J ⊆ crossSeamPage chart G G.domain j →
      SurjOn (Function.invFunOn chart spliceCylinder ∘ ⇑G)
        (crossSeamPage chart G G.domain i ∩ crossSeamPage chart G G.domain j)
        (crossSheetOf i ∩ crossSheetOf j) := by
    intro i j J hij hsJ hJi hJj q hq
    have hqc := crossSheetOf_inter_subset hij hq
    obtain ⟨x, hx, hxq⟩ := hsJ ⟨q, hqc, rfl⟩
    refine ⟨x, ⟨hJi hx, hJj hx⟩, ?_⟩
    change Function.invFunOn chart spliceCylinder (G x) = q
    rw [hxq]
    exact hinjc.leftInvOn_invFunOn (spliceCore_subset_spliceCylinder hqc)
  exact exists_plCrossSeamReading_of_four_source_pages
    (isPolyhedron_crossSeamPage hchart hinjc hDom hf hψ 0)
    (isPolyhedron_crossSeamPage hchart hinjc hDom hf hψ 2)
    (isPolyhedron_crossSeamPage hchart hinjc hDom hf hψ 1)
    (isPolyhedron_crossSeamPage hchart hinjc hDom hf hψ 3)
    (hPLh₁ 0 h0) (hPLh₂ 2 h2) (hPLh₂ 1 h1) (hPLh₁ 3 h3) rfl rfl
    (disjoint_crossSeamPage_of_class hchart hinjc hDom.isClosed hf hJ (by decide) (hcl₁ 0 h0)
      (hcl₂ 2 h2))
    (disjoint_crossSeamPage_of_class hchart hinjc hDom.isClosed hf hJ (by decide) (hcl₁ 0 h0)
      (hcl₂ 1 h1))
    (disjoint_crossSeamPage_of_class hchart hinjc hDom.isClosed hf hJ' (by decide) (hcl₂ 2 h2)
      (hcl₁ 3 h3))
    (disjoint_crossSeamPage_of_class hchart hinjc hDom.isClosed hf hJ' (by decide) (hcl₂ 1 h1)
      (hcl₁ 3 h3))
    (fun _ _ => rfl) (fun _ _ => rfl) (hsurjI (by decide) hsurj₁ h0 h3)
    (hsurjI (by decide) hsurj₂ h2 h1) (hG 0) (hG 2) (hG 1) (hG 3) hsource
    (hbdy 0 (Or.inl h0)) (hbdy 2 (Or.inr h2)) (hbdy 1 (Or.inr h1)) (hbdy 3 (Or.inl h3))
    (hwall₁ 0 h0) (hwall₂ 2 h2) (hwall₂ 1 h1) (hwall₁ 3 h3)

end DifferentialGeometry.Topology.PiecewiseLinear

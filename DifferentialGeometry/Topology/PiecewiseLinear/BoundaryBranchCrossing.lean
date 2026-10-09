/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBranchSheets

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem eventually_mem_image_iff_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {P S T : Set X} {a : X}
    (haS : a ∈ S) (haT : a ∈ T) (hSP : S ⊆ P) (hTP : T ⊆ P)
    (hS : S ∈ 𝓝[P] a) (hT : T ∈ 𝓝[P] a)
    (hSemb : IsEmbedding (S.domRestrict f)) (hTemb : IsEmbedding (T.domRestrict f)) :
    ∀ᶠ y in 𝓝 (f a), y ∈ f '' S ↔ y ∈ f '' T := by
  have hdir {U V : Set X} (haU : a ∈ U) (hU : U ⊆ P)
      (hV : V ∈ 𝓝[P] a) (hUemb : IsEmbedding (U.domRestrict f)) :
      ∀ᶠ y in 𝓝 (f a), y ∈ f '' U → y ∈ f '' V := by
    have hpre : Subtype.val ⁻¹' V ∈ 𝓝 (⟨a, haU⟩ : U) :=
      preimage_coe_mem_nhds_subtype.mpr (nhdsWithin_mono a hU hV)
    have himage := hUemb.isInducing.image_mem_nhdsWithin hpre
    rw [Set.range_domRestrict] at himage
    apply mem_nhdsWithin_iff_eventually.mp
    exact Filter.mem_of_superset himage fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩
  filter_upwards [hdir haS hSP hT hSemb, hdir haT hTP hS hTemb] with y hST hTS
  exact ⟨hST, hTS⟩

private theorem isEmbedding_comp_chart_source
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {S : Set X} (hS : IsEmbedding (S.domRestrict f))
    (e : OpenPartialHomeomorph Y Z) :
    IsEmbedding ((S ∩ f ⁻¹' e.source).domRestrict (e ∘ f)) := by
  have hrestrict : IsEmbedding ((S ∩ f ⁻¹' e.source).domRestrict f) := by
    simpa only [Set.domRestrict_eq, Function.comp_def] using
      hS.comp (IsEmbedding.inclusion (inter_subset_left : S ∩ f ⁻¹' e.source ⊆ S))
  have hsource : IsEmbedding
      (fun x : ↥(S ∩ f ⁻¹' e.source) => (⟨f x, x.property.2⟩ : e.source)) :=
    hrestrict.codRestrict e.source fun x => x.property.2
  have hemb : IsEmbedding (fun y : e.source => e y) := by
    change IsEmbedding (((↑) : e.target → Z) ∘ e.toHomeomorphSourceTarget)
    exact IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding
  exact hemb.comp hsource

private theorem image_germs_of_sheet_neighborhoods
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {P S T U V : Set X} {a b : X} {y : Y}
    (hSP : S ⊆ P) (hTP : T ⊆ P)
    (hSemb : IsEmbedding (S.domRestrict f)) (hTemb : IsEmbedding (T.domRestrict f))
    (hnear : ∀ x ∈ P, f x = y →
      (x ∈ S ∧ S ∈ 𝓝[P] x) ∨ (x ∈ T ∧ T ∈ 𝓝[P] x))
    (ha : a ∈ U) (hb : b ∈ V) (hab : a ≠ b) (hfa : f a = y) (hfb : f b = y)
    (hUP : U ⊆ P) (hVP : V ⊆ P) (hU : U ∈ 𝓝[P] a) (hV : V ∈ 𝓝[P] b)
    (hUemb : IsEmbedding (U.domRestrict f)) (hVemb : IsEmbedding (V.domRestrict f)) :
    ((∀ᶠ z in 𝓝 y, z ∈ f '' U ↔ z ∈ f '' S) ∧
      (∀ᶠ z in 𝓝 y, z ∈ f '' V ↔ z ∈ f '' T)) ∨
    ((∀ᶠ z in 𝓝 y, z ∈ f '' V ↔ z ∈ f '' S) ∧
      (∀ᶠ z in 𝓝 y, z ∈ f '' U ↔ z ∈ f '' T)) := by
  have hinjS : InjOn f S := Set.injOn_iff_injective.mpr hSemb.injective
  have hinjT : InjOn f T := Set.injOn_iff_injective.mpr hTemb.injective
  rcases hnear a (hUP ha) hfa with ⟨haS, hSa⟩ | ⟨haT, hTa⟩
  · rcases hnear b (hVP hb) hfb with ⟨hbS, hSb⟩ | ⟨hbT, hTb⟩
    · exact (hab (hinjS haS hbS (hfa.trans hfb.symm))).elim
    · refine Or.inl ⟨?_, ?_⟩
      · simpa only [hfa] using
          eventually_mem_image_iff_of_isEmbedding ha haS hUP hSP hU hSa hUemb hSemb
      · simpa only [hfb] using
          eventually_mem_image_iff_of_isEmbedding hb hbT hVP hTP hV hTb hVemb hTemb
  · rcases hnear b (hVP hb) hfb with ⟨hbS, hSb⟩ | ⟨hbT, hTb⟩
    · refine Or.inr ⟨?_, ?_⟩
      · simpa only [hfb] using
          eventually_mem_image_iff_of_isEmbedding hb hbS hVP hSP hV hSb hVemb hSemb
      · simpa only [hfa] using
          eventually_mem_image_iff_of_isEmbedding ha haT hUP hTP hU hTa hUemb hTemb
    · exact (hab (hinjT haT hbT (hfa.trans hfb.symm))).elim

private theorem hasPLBoundaryCrossingAt_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M A B : Set E} {x : E} (hcross : HasPLBoundaryCrossingAt M A B x) :
    HasPLBoundaryCrossingAt M B A x := by
  obtain ⟨U, V, h, P, Q, ℓ, hU, hV, hxU, hh, hhx, hP, hQ, hI, hsup, hin, hlocal⟩ := hcross
  refine ⟨U, V, h, Q, P, ℓ, hU, hV, hxU, hh, hhx, hQ, hP, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun R : Submodule ℝ E => Module.finrank ℝ R) (inf_comm Q P)).trans hI
  · simpa only [sup_comm] using hsup
  · simpa only [inf_comm] using hin
  · filter_upwards [hlocal] with y hy
    exact ⟨hy.1, hy.2.2, hy.2.1⟩

private theorem hasPLCrossingAt_images_of_sheet_neighborhoods
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {P S T : Set E} {y : F}
    (hcross : HasPLDoubleCrossingAt f P y) (hSP : S ⊆ P) (hTP : T ⊆ P)
    (hSemb : IsEmbedding (S.domRestrict f)) (hTemb : IsEmbedding (T.domRestrict f))
    (hnear : ∀ x ∈ P, f x = y →
      (x ∈ S ∧ S ∈ 𝓝[P] x) ∨ (x ∈ T ∧ T ∈ 𝓝[P] x)) :
    HasPLCrossingAt (f '' S) (f '' T) y := by
  obtain ⟨a, b, U, V, ha, hb, hfa, hfb, hUP, hVP, hUV, hU, hV, hfU, hfV,
    hcross, _⟩ := hcross
  have hab : a ≠ b := by
    intro hab
    exact Set.disjoint_left.mp hUV ha (hab.symm ▸ hb)
  have hUemb : IsEmbedding (U.domRestrict f) := by
    change IsEmbedding (((↑) : (f '' U) → F) ∘ hfU.homeomorph)
    exact IsEmbedding.subtypeVal.comp hfU.homeomorph.isEmbedding
  have hVemb : IsEmbedding (V.domRestrict f) := by
    change IsEmbedding (((↑) : (f '' V) → F) ∘ hfV.homeomorph)
    exact IsEmbedding.subtypeVal.comp hfV.homeomorph.isEmbedding
  rcases image_germs_of_sheet_neighborhoods hSP hTP hSemb hTemb hnear ha hb hab
    hfa hfb hUP hVP hU hV hUemb hVemb with ⟨hS, hT⟩ | ⟨hS, hT⟩
  · exact hcross.congr hS hT
  · exact hcross.symm.congr hS hT

private theorem hasPLBoundaryCrossingAt_images_of_sheet_neighborhoods
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {P S T : Set E} {M : Set F} {y : F}
    (hcross : HasPLBoundaryDoubleCrossingAt f P M y) (hSP : S ⊆ P) (hTP : T ⊆ P)
    (hSemb : IsEmbedding (S.domRestrict f)) (hTemb : IsEmbedding (T.domRestrict f))
    (hnear : ∀ x ∈ P, f x = y →
      (x ∈ S ∧ S ∈ 𝓝[P] x) ∨ (x ∈ T ∧ T ∈ 𝓝[P] x)) :
    HasPLBoundaryCrossingAt M (f '' S) (f '' T) y := by
  obtain ⟨a, b, U, V, ha, hb, hfa, hfb, hUP, hVP, hUV, hU, hV, hfU, hfV,
    hcross, _⟩ := hcross
  have hab : a ≠ b := by
    intro hab
    exact Set.disjoint_left.mp hUV ha (hab.symm ▸ hb)
  have hUemb : IsEmbedding (U.domRestrict f) := by
    change IsEmbedding (((↑) : (f '' U) → F) ∘ hfU.homeomorph)
    exact IsEmbedding.subtypeVal.comp hfU.homeomorph.isEmbedding
  have hVemb : IsEmbedding (V.domRestrict f) := by
    change IsEmbedding (((↑) : (f '' V) → F) ∘ hfV.homeomorph)
    exact IsEmbedding.subtypeVal.comp hfV.homeomorph.isEmbedding
  rcases image_germs_of_sheet_neighborhoods hSP hTP hSemb hTemb hnear ha hb hab
    hfa hfb hUP hVP hU hV hUemb hVemb with ⟨hS, hT⟩ | ⟨hS, hT⟩
  · exact hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hS hT
  · exact (hasPLBoundaryCrossingAt_symm hcross).congr
      (Filter.Eventually.of_forall fun _ => Iff.rfl) hS hT

namespace NormalSingularCellData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_polyhedral_crossing_sheets_of_boundaryBranch
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C S T : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) A (hD.singularSet.branchComplex c).space ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) C (hD.singularSet.branchComplex c).space ∧
        IsPolyhedron S ∧ IsPolyhedron T ∧ S ⊆ D.domain ∧ T ⊆ D.domain ∧
        A ⊆ S ∧ C ⊆ T ∧ Disjoint S T ∧
        (∀ x ∈ A, S ∈ 𝓝[D.domain] x) ∧ (∀ x ∈ C, T ∈ 𝓝[D.domain] x) ∧
        IsPLOn 2 3 D S ∧ IsPLOn 2 3 D T ∧
        IsEmbedding (S.domRestrict D) ∧ IsEmbedding (T.domRestrict D) ∧
        ∃ W : Set M, IsOpen W ∧ hD.singularSet.branchCarrier c ⊆ W ∧
          (∀ y ∈ W, D.domain ∩ D ⁻¹' {y} ⊆ S ∪ T) ∧
          (∀ y ∈ W, y ∈ doublePointSet D D.domain ↔ y ∈ D '' S ∩ D '' T) ∧
          ∀ y ∈ hD.singularSet.branchCarrier c,
            ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
              ((y ∈ BdM ∧ ∃ N : Set (EuclideanSpace ℝ (Fin 3)),
                HasPLBoundaryCrossingAt N
                  ((e ∘ D) '' (S ∩ D ⁻¹' e.source))
                  ((e ∘ D) '' (T ∩ D ⁻¹' e.source)) (e y)) ∨
              (y ∉ BdM ∧ HasPLCrossingAt
                ((e ∘ D) '' (S ∩ D ⁻¹' e.source))
                ((e ∘ D) '' (T ∩ D ⁻¹' e.source)) (e y))) := by
  obtain ⟨A, C, S, T, hA, hC, hAC, hcover, hAcoord, hCcoord, hS, hT, hSP, hTP,
    hAS, hCT, hST, hSneigh, hTneigh, hSpl, hTpl, hSemb, hTemb,
    W, hW, hbranchW, hfiber, hdouble⟩ :=
    hD.exists_polyhedral_sheet_neighborhoods_of_boundaryBranch hc
  refine ⟨A, C, S, T, hA, hC, hAC, hcover, hAcoord, hCcoord, hS, hT, hSP, hTP,
    hAS, hCT, hST, hSneigh, hTneigh, hSpl, hTpl, hSemb, hTemb,
    W, hW, hbranchW, hfiber, hdouble, ?_⟩
  intro y hy
  obtain ⟨e, he, hye, hcross⟩ := hD.crossing y
    (hD.singularSet.branchCarrier_subset_doublePointSet c hy)
  have hSsource : S ∩ D ⁻¹' e.source ⊆ D.domain ∩ D ⁻¹' e.source :=
    fun _ hx => ⟨hSP hx.1, hx.2⟩
  have hTsource : T ∩ D ⁻¹' e.source ⊆ D.domain ∩ D ⁻¹' e.source :=
    fun _ hx => ⟨hTP hx.1, hx.2⟩
  have hScoord := isEmbedding_comp_chart_source hSemb e
  have hTcoord := isEmbedding_comp_chart_source hTemb e
  have hnear : ∀ x ∈ D.domain ∩ D ⁻¹' e.source, (e ∘ D) x = e y →
      (x ∈ S ∩ D ⁻¹' e.source ∧
        S ∩ D ⁻¹' e.source ∈ 𝓝[D.domain ∩ D ⁻¹' e.source] x) ∨
      (x ∈ T ∩ D ⁻¹' e.source ∧
        T ∩ D ⁻¹' e.source ∈ 𝓝[D.domain ∩ D ⁻¹' e.source] x) := by
    intro x hx hxy
    have hDx : D x = y := e.injOn hx.2 hye hxy
    have hxbranch : x ∈ hD.branchPreimage c := by
      refine ⟨hx.1, ?_⟩
      change D x ∈ hD.singularSet.branchCarrier c
      rw [hDx]
      exact hy
    rcases hcover.subset hxbranch with hxA | hxC
    · refine Or.inl ⟨⟨hAS hxA, hx.2⟩, Filter.inter_mem ?_ ?_⟩
      · exact nhdsWithin_mono x inter_subset_left (hSneigh x hxA)
      · exact Filter.mem_of_superset self_mem_nhdsWithin inter_subset_right
    · refine Or.inr ⟨⟨hCT hxC, hx.2⟩, Filter.inter_mem ?_ ?_⟩
      · exact nhdsWithin_mono x inter_subset_left (hTneigh x hxC)
      · exact Filter.mem_of_superset self_mem_nhdsWithin inter_subset_right
  have hBd : e y ∈ e '' (e.source ∩ BdM) ↔ y ∈ BdM := by
    constructor
    · rintro ⟨z, ⟨hz, hzB⟩, hzy⟩
      exact e.injOn hz hye hzy ▸ hzB
    · exact fun hyB => ⟨y, ⟨hye, hyB⟩, rfl⟩
  refine ⟨e, he, hye, ?_⟩
  rcases hcross with ⟨hyB, N, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hBd.mp hyB, N,
      hasPLBoundaryCrossingAt_images_of_sheet_neighborhoods hcross
        hSsource hTsource hScoord hTcoord hnear⟩
  · exact Or.inr ⟨fun h => hyB (hBd.mpr h),
      hasPLCrossingAt_images_of_sheet_neighborhoods hcross
        hSsource hTsource hScoord hTcoord hnear⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear

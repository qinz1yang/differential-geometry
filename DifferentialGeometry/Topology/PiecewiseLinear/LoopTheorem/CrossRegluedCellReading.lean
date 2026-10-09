/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubeReading
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubeTransverse
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellPredicate
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCellProperness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem false_of_three_mem_fiber {α β : Type*} {f : α → β} {Dom : Set α}
    (hfib : ∀ y, (Dom ∩ f ⁻¹' {y}).encard ≤ 2) {x y z : α} (hx : x ∈ Dom) (hy : y ∈ Dom)
    (hz : z ∈ Dom) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hfy : f y = f x)
    (hfz : f z = f x) : False := by
  have hsub : ({x, y, z} : Set α) ⊆ Dom ∩ f ⁻¹' {f x} := by
    rintro w (rfl | rfl | rfl)
    · exact ⟨hx, rfl⟩
    · exact ⟨hy, hfy⟩
    · exact ⟨hz, hfz⟩
  have hnot : x ∉ ({y, z} : Set α) := by
    rintro (h | h)
    · exact hxy h
    · exact hxz h
  have hcard : ({x, y, z} : Set α).encard = 3 := by
    rw [encard_insert_of_notMem hnot, encard_pair hyz]
    rfl
  have hle := (encard_le_encard hsub).trans (hfib (f x))
  rw [hcard] at hle
  exact absurd hle (by decide)

theorem false_of_isOpen_inter_subset {O W V K : Set (EuclideanSpace ℝ (Fin 2))}
    {x : EuclideanSpace ℝ (Fin 2)} (hO : IsOpen O) (hxO : x ∈ O) (hV : IsPLBall 2 V)
    (hxV : x ∈ V) (hOW : O ∩ V ⊆ W) (hWV : W ∩ V ⊆ K) (hK : interior K = ∅) : False := by
  have hxcl : x ∈ closure (interior V) := by
    rw [IsPLBall.closure_interior (n := 1) hV]
    exact hxV
  obtain ⟨z, hzO, hzV⟩ := mem_closure_iff.mp hxcl O hO hxO
  have hsub : O ∩ interior V ⊆ K := fun w hw =>
    hWV ⟨hOW ⟨hw.1, interior_subset hw.2⟩, interior_subset hw.2⟩
  have hzK : z ∈ interior K := interior_maximal hsub (hO.inter isOpen_interior) ⟨hzO, hzV⟩
  rw [hK] at hzK
  exact hzK

section Helpers

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

theorem isPreconnected_inter_preimage_crossOpenSheetOf (hchart : ContinuousOn chart spliceCylinder)
    (hDom : IsCompact Dom) (hf : ContinuousOn f Dom) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) :
    IsPreconnected (Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i)) := by
  have hcont : ContinuousOn (Function.invFunOn f Dom ∘ chart) (crossOpenSheetOf i) :=
    (continuousOn_invFunOn_of_isCompact_of_forall_eq hDom hf hsurj huniq).comp
      (hchart.mono (crossOpenSheetOf_subset_spliceCylinder i)) fun q hq => ⟨q, hq, rfl⟩
  have heq : Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i) =
      (Function.invFunOn f Dom ∘ chart) '' crossOpenSheetOf i := by
    ext x
    constructor
    · rintro ⟨hx, q, hq, hqx⟩
      refine ⟨q, hq, ?_⟩
      have hex : ∃ a ∈ Dom, f a = chart q := ⟨x, hx, hqx.symm⟩
      exact huniq _ (Function.invFunOn_mem hex) x hx ((Function.invFunOn_eq hex).trans hqx)
        (by rw [Function.invFunOn_eq hex]; exact ⟨q, hq, rfl⟩)
    · rintro ⟨q, hq, rfl⟩
      have hex : ∃ a ∈ Dom, f a = chart q := hsurj ⟨q, hq, rfl⟩
      exact ⟨Function.invFunOn_mem hex, q, hq, (Function.invFunOn_eq hex).symm⟩
  rw [heq]
  exact (convex_crossOpenSheetOf i).isPreconnected.image _ hcont

omit [TopologicalSpace X] [T2Space X] in
theorem nonempty_inter_preimage_crossOpenSheetOf {i : Fin 4}
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) :
    (Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i)).Nonempty := by
  have hq : ((1 : ℝ) • crossDirOf i, (0 : ℝ)) ∈ crossOpenSheetOf i :=
    smul_crossDirOf_mem_crossOpenSheetOf i one_pos le_rfl ⟨le_rfl, zero_le_one⟩
  obtain ⟨x, hx, hxq⟩ := hsurj ⟨_, hq, rfl⟩
  exact ⟨x, hx, _, hq, hxq.symm⟩

omit [TopologicalSpace X] [T2Space X] in
theorem disjoint_inter_preimage_crossOpenSheetOf (hinjc : InjOn chart spliceCylinder)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (i : Fin 4) :
    Disjoint (Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i)) (J₁ ∪ J₂) := by
  rw [← hJ, disjoint_left]
  rintro x ⟨-, q, hq, hqx⟩ ⟨-, q', hq', hq'x⟩
  have hqq : q = q' := hinjc (crossOpenSheetOf_subset_spliceCylinder i hq)
    (spliceCore_subset_spliceCylinder hq') (hqx.trans hq'x.symm)
  rw [hqq] at hq
  exact disjoint_left.mp (disjoint_crossOpenSheetOf_spliceCore i) hq hq'

theorem crossSeamPage_subset_of_three_closed (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) {U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2))}
    (hU₁ : IsClosed U₁) (hU₂ : IsClosed U₂) (hU₃ : IsClosed U₃) (hcover : Dom ⊆ U₁ ∪ U₂ ∪ U₃)
    (h₁₂ : U₁ ∩ U₂ ⊆ J₁ ∪ J₂) (h₂₃ : U₂ ∩ U₃ ⊆ J₁ ∪ J₂) (h₁₃ : Disjoint U₁ U₃) :
    crossSeamPage chart f Dom i ⊆ U₁ ∨ crossSeamPage chart f Dom i ⊆ U₂ ∨
      crossSeamPage chart f Dom i ⊆ U₃ := by
  have hconn := isPreconnected_inter_preimage_crossOpenSheetOf hchart hDom hf huniq hsurj
  have hdJ := disjoint_inter_preimage_crossOpenSheetOf hinjc hJ i
  rcases subset_or_disjoint_of_isPreconnected_of_three_closed hU₁ hU₂ hU₃ hconn
    (inter_subset_left.trans hcover) (hdJ.mono_right h₁₂) (hdJ.mono_right h₂₃) with hd | hs
  · have h13 : Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i) ⊆ U₁ ∪ U₃ := by
      intro x hx
      rcases hcover hx.1 with (h | h) | h
      · exact Or.inl h
      · exact absurd h (disjoint_left.mp hd hx)
      · exact Or.inr h
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn U₁ U₃ hU₁ hU₃ h13
      (by rw [h₁₃.inter_eq, inter_empty]) with h | h
    · exact Or.inl (closure_minimal h hU₁)
    · exact Or.inr (Or.inr (closure_minimal h hU₃))
  · exact Or.inr (Or.inl (closure_minimal hs hU₂))

omit [T2Space X] in
theorem exists_isOpen_forall_mem_crossSeamPage (hf : ContinuousOn f Dom)
    (hopen : IsOpen (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)))
    (himage : ∀ x ∈ Dom, f x ∈ chart '' spliceCylinder → f x ∈ chart '' crossingFigure)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂)
    (hJ₁page : ∃ i, J₁ ⊆ crossSeamPage chart f Dom i)
    (hJ₂page : ∃ i, J₂ ⊆ crossSeamPage chart f Dom i)
    (hclass : ∀ i, J₁ ⊆ crossSeamPage chart f Dom i ∨ Disjoint J₁ (crossSeamPage chart f Dom i))
    {x₁ : EuclideanSpace ℝ (Fin 2)} (hx₁ : x₁ ∈ J₁) (hx₁D : x₁ ∈ Dom)
    (hfx₁ : f x₁ ∈ chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)) :
    ∃ O : Set (EuclideanSpace ℝ (Fin 2)), IsOpen O ∧ x₁ ∈ O ∧
      ∀ y ∈ O ∩ Dom, ∃ i, J₁ ⊆ crossSeamPage chart f Dom i ∧ y ∈ crossSeamPage chart f Dom i := by
  obtain ⟨O₀, hO₀, hx₁O₀, hO₀sub⟩ := mem_nhdsWithin.mp (hf x₁ hx₁D (hopen.mem_nhds hfx₁))
  have hTc : IsClosed (⋃ j ∈ {j : Fin 4 | Disjoint J₁ (crossSeamPage chart f Dom j)},
      crossSeamPage chart f Dom j) :=
    (toFinite _).isClosed_biUnion fun _ _ => isClosed_closure
  refine ⟨O₀ \ ⋃ j ∈ {j : Fin 4 | Disjoint J₁ (crossSeamPage chart f Dom j)},
    crossSeamPage chart f Dom j, hO₀.sdiff hTc, ⟨hx₁O₀, ?_⟩, ?_⟩
  · simp only [mem_iUnion, mem_ofPred_eq, not_exists]
    exact fun j hj => disjoint_left.mp hj hx₁
  · rintro y ⟨⟨hyO, hyT⟩, hyD⟩
    have hfy : f y ∈ chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1) :=
      hO₀sub ⟨hyO, hyD⟩
    have hfy' : f y ∈ chart '' spliceCylinder := image_mono
      (prod_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) Ioo_subset_Icc_self) hfy
    obtain ⟨i, hi⟩ := exists_mem_crossSeamPage_of_mem himage hJ hJ₁page hJ₂page hyD hfy'
    rcases hclass i with h | h
    · exact ⟨i, h, hi⟩
    · exact absurd (mem_biUnion (x := i) h hi) hyT

end Helpers

theorem crossSeamPage_comp_crossQuarterTurn {X : Type*} (chart : (ℝ × ℝ) × ℝ → X)
    (f : EuclideanSpace ℝ (Fin 2) → X) (Dom : Set (EuclideanSpace ℝ (Fin 2))) (i : Fin 4) :
    crossSeamPage (chart ∘ crossQuarterTurn) f Dom i = crossSeamPage chart f Dom (i + 1) := by
  rw [crossSeamPage, crossSeamPage, image_comp, image_crossQuarterTurn_crossOpenSheetOf]

theorem nonempty_plCrossSeamReading_comp_crossQuarterTurn {M : Type u} [TopologicalSpace M]
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
    (h1 : J₁ ⊆ crossSeamPage chart G G.domain 1) (h0 : J₁ ⊆ crossSeamPage chart G G.domain 0)
    (h2 : J₂ ⊆ crossSeamPage chart G G.domain 2) (h3 : J₂ ⊆ crossSeamPage chart G G.domain 3) :
    Nonempty (PLCrossSeamReading (chart ∘ crossQuarterTurn) G) := by
  obtain ⟨hPL'⟩ := nonempty_plSeamTubeChart_comp_crossQuarterTurn hPL
  have hcore : (chart ∘ crossQuarterTurn) '' spliceCore = chart '' spliceCore := by
    rw [image_comp, image_crossQuarterTurn_spliceCore]
  have hfig : (chart ∘ crossQuarterTurn) '' crossingFigure = chart '' crossingFigure := by
    rw [image_comp, image_crossQuarterTurn_crossingFigure]
  have hcyl : (chart ∘ crossQuarterTurn) '' spliceCylinder = chart '' spliceCylinder := by
    rw [image_comp, image_crossQuarterTurn_spliceCylinder]
  have hend : (chart ∘ crossQuarterTurn) '' spliceEndDisks = chart '' spliceEndDisks := by
    rw [image_comp, image_crossQuarterTurn_spliceEndDisks]
  have hfc : (chart ∘ crossQuarterTurn) '' (crossingFigure \ spliceCore) =
      chart '' (crossingFigure \ spliceCore) := by
    rw [image_comp, image_sdiff injective_crossQuarterTurn, image_crossQuarterTurn_crossingFigure,
      image_crossQuarterTurn_spliceCore]
  refine nonempty_plCrossSeamReading_of_crossSeamPage hPL'
    (hchart.comp continuous_crossQuarterTurn.continuousOn mapsTo_crossQuarterTurn_spliceCylinder)
    (hinjc.comp injective_crossQuarterTurn.injOn mapsTo_crossQuarterTurn_spliceCylinder)
    (by rw [hcore]; exact hJ) hJ₁ hJ₂ hJJ hinj₁ hinj₂ (by rw [hcore]; exact hsurj₁)
    (by rw [hcore]; exact hsurj₂) (by rw [hfc]; exact huniq)
    (by rw [hcyl, hfig]; exact himage) (by rw [hfig]; exact hsurj) (by rw [hcyl, hend]; exact htube)
    hfront (by rw [hfc]; exact hbd) ?_ ?_ ?_ ?_
  · rw [crossSeamPage_comp_crossQuarterTurn]
    exact h1
  · rw [crossSeamPage_comp_crossQuarterTurn]
    exact h0
  · rw [crossSeamPage_comp_crossQuarterTurn]
    exact h2
  · rw [crossSeamPage_comp_crossQuarterTurn]
    exact h3

theorem exists_plCrossSeamReading_of_isCrossRegluedCell
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch} (T : CrossSeamTubeData hD c U)
    (hchart : PLSeamTubeChart M T.chart)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks)
    {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    Nonempty (PLCrossSeamReading T.chart G) ∨
      Nonempty (PLCrossSeamReading (T.chart ∘ crossQuarterTurn) G) := by
  have hGim := hD.image_subset_of_isCrossRegluedCell hG
  have hGdps := hD.doublePointSet_eq_of_isCrossRegluedCell hG
  have hGfr := hD.image_frontier_eq_of_isCrossRegluedCell hG
  obtain ⟨A, C, U₁, U₂, U₃, P, Q, P', Q', A', _, _, _, _, _, _, _, _, g, f₁, f₂, h, f₃, H, hA, hC,
    hAC, hpre, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃, hdisj₁₃, hP, hQ,
    hHdomain, hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, hA'def, -, hA'seam, -, -, hP', hQ',
    hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃, -⟩ := hG
  have hcc : ContinuousOn T.chart spliceCylinder := T.isTube.continuousOn_chart
  have hci : InjOn T.chart spliceCylinder := T.isTube.injOn_chart
  have hcore : T.chart '' spliceCore = hD.singularSet.branchCarrier c := T.isTube.image_spliceCore
  have hfig : T.chart '' crossingFigure = ⇑D '' D.domain ∩ T.chart '' spliceCylinder :=
    T.isTube.image_crossingFigure
  have hdps : doublePointSet (⇑D) D.domain ∩ T.chart '' spliceCylinder =
      hD.singularSet.branchCarrier c := T.doublePointSet_inter_image_spliceCylinder
  have hopen := isOpen_image_crossSeamBox hcc hci
  have hDdom : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hDc := D.continuousOn
  have hGdom : IsCompact G.domain := G.isPLBall_domain.isPolyhedron.isCompact
  have hGc := G.continuousOn
  have hAcl : IsClosed A := hA.isPolyhedron.isCompact.isClosed
  have hCcl : IsClosed C := hC.isPolyhedron.isCompact.isClosed
  have hU₁b : IsPLBall 2 U₁ := hP.of_isPLHomeomorphOn hf₁
  have hU₂b : IsPLBall 2 U₂ := hQ.of_isPLHomeomorphOn hf₂
  have hU₃b : IsPLBall 2 U₃ := hQ'.of_isPLHomeomorphOn hf₃
  have hU₁c : IsClosed U₁ := hU₁b.isPolyhedron.isCompact.isClosed
  have hU₂c : IsClosed U₂ := hU₂b.isPolyhedron.isCompact.isClosed
  have hU₃c : IsClosed U₃ := hU₃b.isPolyhedron.isCompact.isClosed
  have hPc : IsClosed P := hP.isPolyhedron.isCompact.isClosed
  have hQc : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hP'c : IsClosed P' := hP'.isPolyhedron.isCompact.isClosed
  have hQ'c : IsClosed Q' := hQ'.isPolyhedron.isCompact.isClosed
  have hU₁D : U₁ ⊆ D.domain := by
    rw [← hdomains]
    exact subset_union_left.trans subset_union_left
  have hU₂D : U₂ ⊆ D.domain := by
    rw [← hdomains]
    exact subset_union_right.trans subset_union_left
  have hU₃D : U₃ ⊆ D.domain := by
    rw [← hdomains]
    exact subset_union_right
  have hAU₁ : A ⊆ U₁ := by
    rw [← hinter₁₂]
    exact inter_subset_left
  have hAU₂ : A ⊆ U₂ := by
    rw [← hinter₁₂]
    exact inter_subset_right
  have hCU₂ : C ⊆ U₂ := by
    rw [← hinter₂₃]
    exact inter_subset_left
  have hCU₃ : C ⊆ U₃ := by
    rw [← hinter₂₃]
    exact inter_subset_right
  have hAD : A ⊆ D.domain := hAU₁.trans hU₁D
  have hCD : C ⊆ D.domain := hCU₃.trans hU₃D
  have hAint : interior A = ∅ := hA.interior_eq_empty_of_lt_finrank (by simp)
  have hCint : interior C = ∅ := hC.interior_eq_empty_of_lt_finrank (by simp)
  have hinjA : InjOn (⇑D) A := by
    intro x hx y hy hxy
    by_contra hne
    have hgx := hg.bijOn.mapsTo hx
    refine false_of_three_mem_fiber hD.fiber_le_two (hAD hx) (hAD hy) (hCD hgx) hne
      (fun he => disjoint_left.mp hAC hx (by rw [he]; exact hgx))
      (fun he => disjoint_left.mp hAC hy (by rw [he]; exact hgx)) hxy.symm (hcompat hx).symm
  have hinjC : InjOn (⇑D) C := by
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨x', hx', rfl⟩ := hg.bijOn.surjOn hx
    refine false_of_three_mem_fiber hD.fiber_le_two (hCD hx) (hCD hy) (hAD hx') hne
      (fun he => disjoint_left.mp hAC hx' (by rw [← he]; exact hx))
      (fun he => disjoint_left.mp hAC hx' (by rw [← he]; exact hy)) hxy.symm (hcompat hx')
  have hAcar : ∀ y ∈ A, D y ∈ hD.singularSet.branchCarrier c := by
    intro y hy
    have hm : y ∈ hD.branchPreimage c := by
      rw [hpre]
      exact Or.inl hy
    exact hm.2
  have hCcar : ∀ y ∈ C, D y ∈ hD.singularSet.branchCarrier c := by
    intro y hy
    have hm : y ∈ hD.branchPreimage c := by
      rw [hpre]
      exact Or.inr hy
    exact hm.2
  have hJD : D.domain ∩ ⇑D ⁻¹' (T.chart '' spliceCore) = A ∪ C := by
    rw [hcore]
    exact hpre
  have hsurjA : T.chart '' spliceCore ⊆ ⇑D '' A := by
    rw [hcore]
    intro y hy
    obtain ⟨x, hx, -, -, -, hxy, -⟩ := hD.singularSet.branchCarrier_subset_doublePointSet c hy
    have hxAC : x ∈ A ∪ C := by
      rw [← hpre]
      exact ⟨hx, by rw [mem_preimage, hxy]; exact hy⟩
    rcases hxAC with hxA | hxC
    · exact ⟨x, hxA, hxy⟩
    · obtain ⟨x', hx', rfl⟩ := hg.bijOn.surjOn hxC
      exact ⟨x', hx', (hcompat hx').trans hxy⟩
  have hsurjC : T.chart '' spliceCore ⊆ ⇑D '' C := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurjA hy
    exact ⟨g x, hg.bijOn.mapsTo hx, (hcompat hx).symm⟩
  have hnotcore : ∀ y ∈ T.chart '' (crossingFigure \ spliceCore),
      y ∉ hD.singularSet.branchCarrier c := by
    rintro y ⟨q, hq, rfl⟩ hy
    rw [← hcore] at hy
    exact hq.2 (mem_of_apply_mem_image_of_injOn hci spliceCore_subset_spliceCylinder
      (crossingFigure_subset_spliceCylinder hq.1) hy)
  have hfigcyl : T.chart '' (crossingFigure \ spliceCore) ⊆ T.chart '' spliceCylinder :=
    image_mono (sdiff_subset.trans crossingFigure_subset_spliceCylinder)
  have huniqD : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D x = D y →
      D x ∈ T.chart '' (crossingFigure \ spliceCore) → x = y := by
    intro x hx y hy hxy hm
    by_contra hne
    apply hnotcore _ hm
    rw [← hdps]
    exact ⟨⟨x, hx, y, hy, hne, rfl, hxy.symm⟩, hfigcyl hm⟩
  have himageD : ∀ x ∈ D.domain, D x ∈ T.chart '' spliceCylinder →
      D x ∈ T.chart '' crossingFigure := fun x hx hfx => by
    rw [hfig]
    exact ⟨⟨x, hx, rfl⟩, hfx⟩
  have hsurjD : T.chart '' crossingFigure ⊆ ⇑D '' D.domain := by
    rw [hfig]
    exact inter_subset_left
  have hmidcore : (((0 : ℝ), (0 : ℝ)), (1 / 2 : ℝ)) ∈ spliceCore :=
    ⟨mem_singleton _, by norm_num, by norm_num⟩
  have hmid : T.chart (((0 : ℝ), (0 : ℝ)), 1 / 2) ∈ hD.singularSet.branchCarrier c := by
    rw [← hcore]
    exact ⟨_, hmidcore, rfl⟩
  have hmidBd : T.chart (((0 : ℝ), (0 : ℝ)), 1 / 2) ∉ BdM := by
    intro hB
    have hm : T.chart (((0 : ℝ), (0 : ℝ)), 1 / 2) ∈ T.chart '' spliceEndDisks := by
      rw [← htubeBdM]
      exact ⟨⟨_, spliceCore_subset_spliceCylinder hmidcore, rfl⟩, hB⟩
    have hq := (mem_of_apply_mem_image_of_injOn hci spliceEndDisks_subset_spliceCylinder
      (spliceCore_subset_spliceCylinder hmidcore) hm).2
    rcases hq with hq | hq <;> norm_num at hq
  obtain ⟨e, -, hze, hcross⟩ := hD.hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary
    (hD.singularSet.branchCarrier_subset_doublePointSet c hmid) hmidBd
  obtain ⟨k, hAk, hAk2, hCk1, hCk3⟩ := exists_opposite_crossSeamPage hcc hci hDdom hDc hJD hAcl
    hCcl hAC hinjA hinjC hsurjA hsurjC huniqD himageD hsurjD hopen hze hcross
  have hhuD : ∀ i, ∀ x ∈ D.domain, ∀ y ∈ D.domain, D x = D y →
      D x ∈ T.chart '' crossOpenSheetOf i → x = y := fun i x hx y hy hxy hm =>
    huniqD x hx y hy hxy (image_mono (crossOpenSheetOf_subset_sdiff i) hm)
  have hsuD : ∀ i, T.chart '' crossOpenSheetOf i ⊆ ⇑D '' D.domain := fun i =>
    (image_mono ((crossOpenSheetOf_subset_sdiff i).trans sdiff_subset)).trans hsurjD
  have hclassD := fun i => crossSeamPage_class hcc hci hDdom hDc hJD hAcl hCcl hAC hinjA hinjC
    hsurjA hsurjC (hhuD i) (hsuD i)
  have hplaceD : ∀ i, crossSeamPage T.chart D D.domain i ⊆ U₁ ∨
      crossSeamPage T.chart D D.domain i ⊆ U₂ ∨ crossSeamPage T.chart D D.domain i ⊆ U₃ :=
    fun i => crossSeamPage_subset_of_three_closed hcc hci hDdom hDc hJD (hhuD i) (hsuD i) hU₁c
      hU₂c hU₃c hdomains.symm.subset (by rw [hinter₁₂]; exact subset_union_left)
      (by rw [hinter₂₃]; exact subset_union_right) hdisj₁₃
  have hpick : ∀ i, ∀ y ∈ D.domain ∩ ⇑D ⁻¹' (T.chart '' crossOpenSheetOf i),
      (y ∈ U₁ → crossSeamPage T.chart D D.domain i ⊆ U₁) ∧
      (y ∈ U₂ → crossSeamPage T.chart D D.domain i ⊆ U₂) ∧
      (y ∈ U₃ → crossSeamPage T.chart D D.domain i ⊆ U₃) := by
    intro i y hy
    have hyZ : y ∈ crossSeamPage T.chart D D.domain i := subset_closure hy
    have hyAC : y ∉ A ∪ C :=
      disjoint_left.mp (disjoint_inter_preimage_crossOpenSheetOf hci hJD i) hy
    refine ⟨fun hy1 => ?_, fun hy2 => ?_, fun hy3 => ?_⟩
    · rcases hplaceD i with h1 | h2 | h3
      · exact h1
      · exact absurd (Or.inl (hinter₁₂.subset ⟨hy1, h2 hyZ⟩)) hyAC
      · exact absurd (h3 hyZ) (disjoint_left.mp hdisj₁₃ hy1)
    · rcases hplaceD i with h1 | h2 | h3
      · exact absurd (Or.inl (hinter₁₂.subset ⟨h1 hyZ, hy2⟩)) hyAC
      · exact h2
      · exact absurd (Or.inr (hinter₂₃.subset ⟨hy2, h3 hyZ⟩)) hyAC
    · rcases hplaceD i with h1 | h2 | h3
      · exact absurd hy3 (disjoint_left.mp hdisj₁₃ (h1 hyZ))
      · exact absurd (Or.inr (hinter₂₃.subset ⟨h2 hyZ, hy3⟩)) hyAC
      · exact h3
  have hAone : ∀ i, A ⊆ crossSeamPage T.chart D D.domain i →
      crossSeamPage T.chart D D.domain i ⊆ U₁ ∨ crossSeamPage T.chart D D.domain i ⊆ U₂ := by
    intro i hi
    rcases hplaceD i with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · obtain ⟨x, hx⟩ := hA.nonempty
      exact absurd (h3 (hi hx)) (disjoint_left.mp hdisj₁₃ (hAU₁ hx))
  have hCone : ∀ i, C ⊆ crossSeamPage T.chart D D.domain i →
      crossSeamPage T.chart D D.domain i ⊆ U₂ ∨ crossSeamPage T.chart D D.domain i ⊆ U₃ := by
    intro i hi
    rcases hplaceD i with h1 | h2 | h3
    · obtain ⟨x, hx⟩ := hC.nonempty
      exact absurd (hCU₃ hx) (disjoint_left.mp hdisj₁₃ (h1 (hi hx)))
    · exact Or.inl h2
    · exact Or.inr h3
  have hfour : ∀ i k : Fin 4, i = k ∨ i = k + 1 ∨ i = k + 2 ∨ i = k + 3 := by decide
  have hAnC : ∀ i, A ⊆ crossSeamPage T.chart D D.domain i →
      C ⊆ crossSeamPage T.chart D D.domain i → False := by
    intro i hAi hCi
    obtain ⟨x, hx⟩ := hA.nonempty
    obtain ⟨y, hy⟩ := hC.nonempty
    rcases hclassD i with ⟨-, hd⟩ | ⟨-, hd⟩
    · exact disjoint_left.mp hd hy (hCi hy)
    · exact disjoint_left.mp hd hx (hAi hx)
  have hAonly : ∀ i, A ⊆ crossSeamPage T.chart D D.domain i → i = k ∨ i = k + 2 := by
    intro i hi
    rcases hfour i k with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hAnC _ hi hCk1).elim
    · exact Or.inr rfl
    · exact (hAnC _ hi hCk3).elim
  have hConly : ∀ i, C ⊆ crossSeamPage T.chart D D.domain i → i = k + 1 ∨ i = k + 3 := by
    intro i hi
    rcases hfour i k with rfl | rfl | rfl | rfl
    · exact (hAnC _ hAk hi).elim
    · exact Or.inl rfl
    · exact (hAnC _ hAk2 hi).elim
    · exact Or.inr rfl
  have hBox : ∀ y : M, y = T.chart (((0 : ℝ), (0 : ℝ)), 1 / 2) →
      y ∈ T.chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1) := by
    rintro y rfl
    exact ⟨_, ⟨⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, ⟨by norm_num,
      by norm_num⟩⟩, rfl⟩
  obtain ⟨a₀, ha₀A, ha₀⟩ := hsurjA ⟨_, hmidcore, rfl⟩
  obtain ⟨c₀, hc₀C, hc₀⟩ := hsurjC ⟨_, hmidcore, rfl⟩
  have hJD' : D.domain ∩ ⇑D ⁻¹' (T.chart '' spliceCore) = C ∪ A := by rw [hJD, union_comm]
  obtain ⟨OA, hOA, ha₀OA, hOAsub⟩ := exists_isOpen_forall_mem_crossSeamPage hDc hopen himageD
    hJD ⟨k, hAk⟩ ⟨k + 1, hCk1⟩
    (fun i => (hclassD i).elim (fun hi => Or.inl hi.1) fun hi => Or.inr hi.2) ha₀A (hAD ha₀A)
    (hBox _ ha₀)
  obtain ⟨OC, hOC, hc₀OC, hOCsub⟩ := exists_isOpen_forall_mem_crossSeamPage hDc hopen himageD
    hJD' ⟨k + 1, hCk1⟩ ⟨k, hAk⟩
    (fun i => (hclassD i).elim (fun hi => Or.inr hi.2) fun hi => Or.inl hi.1) hc₀C (hCD hc₀C)
    (hBox _ hc₀)
  have hplA : (crossSeamPage T.chart D D.domain k ⊆ U₁ ∧
      crossSeamPage T.chart D D.domain (k + 2) ⊆ U₂) ∨
      (crossSeamPage T.chart D D.domain k ⊆ U₂ ∧
        crossSeamPage T.chart D D.domain (k + 2) ⊆ U₁) := by
    have hboth : ∀ V, crossSeamPage T.chart D D.domain k ⊆ V →
        crossSeamPage T.chart D D.domain (k + 2) ⊆ V → OA ∩ D.domain ⊆ V := by
      intro V hk hk2 y hy
      obtain ⟨i, hi, hyi⟩ := hOAsub y hy
      rcases hAonly i hi with rfl | rfl
      · exact hk hyi
      · exact hk2 hyi
    rcases hAone k hAk with h1 | h1 <;> rcases hAone (k + 2) hAk2 with h2 | h2
    · exact (false_of_isOpen_inter_subset hOA ha₀OA hU₂b (hAU₂ ha₀A)
        (fun y hy => hboth U₁ h1 h2 ⟨hy.1, hU₂D hy.2⟩) hinter₁₂.subset hAint).elim
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact (false_of_isOpen_inter_subset hOA ha₀OA hU₁b (hAU₁ ha₀A)
        (fun y hy => hboth U₂ h1 h2 ⟨hy.1, hU₁D hy.2⟩)
        (fun y hy => hinter₁₂.subset ⟨hy.2, hy.1⟩) hAint).elim
  have hplC : (crossSeamPage T.chart D D.domain (k + 1) ⊆ U₂ ∧
      crossSeamPage T.chart D D.domain (k + 3) ⊆ U₃) ∨
      (crossSeamPage T.chart D D.domain (k + 1) ⊆ U₃ ∧
        crossSeamPage T.chart D D.domain (k + 3) ⊆ U₂) := by
    have hboth : ∀ V, crossSeamPage T.chart D D.domain (k + 1) ⊆ V →
        crossSeamPage T.chart D D.domain (k + 3) ⊆ V → OC ∩ D.domain ⊆ V := by
      intro V hk hk2 y hy
      obtain ⟨i, hi, hyi⟩ := hOCsub y hy
      rcases hConly i hi with rfl | rfl
      · exact hk hyi
      · exact hk2 hyi
    rcases hCone (k + 1) hCk1 with h1 | h1 <;> rcases hCone (k + 3) hCk3 with h2 | h2
    · exact (false_of_isOpen_inter_subset hOC hc₀OC hU₃b (hCU₃ hc₀C)
        (fun y hy => hboth U₂ h1 h2 ⟨hy.1, hU₃D hy.2⟩) hinter₂₃.subset hCint).elim
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact (false_of_isOpen_inter_subset hOC hc₀OC hU₂b (hCU₂ hc₀C)
        (fun y hy => hboth U₃ h1 h2 ⟨hy.1, hU₂D hy.2⟩)
        (fun y hy => hinter₂₃.subset ⟨hy.2, hy.1⟩) hCint).elim
  have hhc : ContinuousOn h P' := hh.isPiecewiseAffineOn.continuousOn
  have hhP' : ∀ x ∈ P', h x ∈ P ∪ Q := fun x hx => by
    rw [← hHdomain]
    exact hh.bijOn.mapsTo hx
  have hA'Q : A' ⊆ Q := by
    rw [hA'def]
    rintro _ ⟨y, hy, rfl⟩
    exact Function.invFunOn_mem (hf₂.bijOn.surjOn (hAU₂ hy))
  have hf₂A' : ∀ x ∈ A', f₂ x ∈ A := by
    rw [hA'def]
    rintro _ ⟨y, hy, rfl⟩
    rw [Function.invFunOn_eq (hf₂.bijOn.surjOn (hAU₂ hy))]
    exact hy
  have hA'P : Disjoint A' P :=
    disjoint_left.mpr fun x hx hxP => disjoint_left.mp hA'seam hx ⟨hxP, hA'Q hx⟩
  have hJSA' : ∀ x ∈ P' ∩ Q', h x ∈ A' := fun x hx => by
    rw [← hhseam]
    exact ⟨x, hx, rfl⟩
  have hGL : ∀ x ∈ P', h x ∈ P → G x = D (f₁ (h x)) := fun x hx hxP =>
    (hGH hx).trans (hH₁ hxP)
  have hGM : ∀ x ∈ P', h x ∈ Q → G x = D (f₂ (h x)) := fun x hx hxQ =>
    (hGH hx).trans (hH₂ hxQ)
  have hGR : ∀ x ∈ Q', G x = D (f₃ x) := fun x hx => hG₃ hx
  have hJG : G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCore) = (P' ∩ h ⁻¹' (P ∩ Q)) ∪ (P' ∩ Q') := by
    rw [hcore]
    apply Subset.antisymm
    · rintro x ⟨hxG, hxc⟩
      have hmemAC : ∀ y ∈ D.domain, D y ∈ hD.singularSet.branchCarrier c → y ∈ A ∪ C :=
        fun y hy hyc => by
          rw [← hpre]
          exact ⟨hy, hyc⟩
      rw [hGdomain] at hxG
      rcases hxG with hxP' | hxQ'
      · rcases hhP' x hxP' with hxP | hxQ
        · have hm := hmemAC _ (hU₁D (hf₁.bijOn.mapsTo hxP))
            (by rw [← hGL x hxP' hxP]; exact hxc)
          rcases hm with hmA | hmC
          · rw [← hf₁seam] at hmA
            obtain ⟨u, hu, hue⟩ := hmA
            have hux := hf₁.bijOn.injOn hu.1 hxP hue
            rw [hux] at hu
            exact Or.inl ⟨hxP', hu⟩
          · exact absurd (hCU₃ hmC) (disjoint_left.mp hdisj₁₃ (hf₁.bijOn.mapsTo hxP))
        · have hm := hmemAC _ (hU₂D (hf₂.bijOn.mapsTo hxQ))
            (by rw [← hGM x hxP' hxQ]; exact hxc)
          rcases hm with hmA | hmC
          · have hxA' : h x ∈ A' := by
              rw [hA'def]
              exact ⟨f₂ (h x), hmA, hf₂.bijOn.injOn.leftInvOn_invFunOn hxQ⟩
            rw [← hhseam] at hxA'
            obtain ⟨u, hu, hue⟩ := hxA'
            have hux := hh.bijOn.injOn hu.1 hxP' hue
            rw [hux] at hu
            exact Or.inr hu
          · rw [← hf₂seam] at hmC
            obtain ⟨u, hu, hue⟩ := hmC
            have hux := hf₂.bijOn.injOn hu.2 hxQ hue
            rw [hux] at hu
            exact Or.inl ⟨hxP', hu⟩
      · have hm := hmemAC _ (hU₃D (hf₃.bijOn.mapsTo hxQ')) (by rw [← hGR x hxQ']; exact hxc)
        rcases hm with hmA | hmC
        · exact absurd (hf₃.bijOn.mapsTo hxQ') (disjoint_left.mp hdisj₁₃ (hAU₁ hmA))
        · rw [← hf₃seam] at hmC
          obtain ⟨u, hu, hue⟩ := hmC
          have hux := hf₃.bijOn.injOn hu.2 hxQ' hue
          rw [hux] at hu
          exact Or.inr hu
    · rintro x (⟨hxP', hxPQ⟩ | ⟨hxP', hxQ'⟩)
      · refine ⟨by rw [hGdomain]; exact Or.inl hxP', ?_⟩
        rw [mem_preimage, hGL x hxP' hxPQ.1]
        exact hAcar _ (by rw [← hf₁seam]; exact ⟨h x, hxPQ, rfl⟩)
      · refine ⟨by rw [hGdomain]; exact Or.inr hxQ', ?_⟩
        rw [mem_preimage, hGR x hxQ']
        exact hCcar _ (by rw [← hf₃seam]; exact ⟨x, ⟨hxP', hxQ'⟩, rfl⟩)
  have hJFc : IsClosed (P' ∩ h ⁻¹' (P ∩ Q)) :=
    hhc.preimage_isClosed_of_isClosed hP'c (hPc.inter hQc)
  have hJSc : IsClosed (P' ∩ Q') := hP'c.inter hQ'c
  have hJFS : Disjoint (P' ∩ h ⁻¹' (P ∩ Q)) (P' ∩ Q') :=
    disjoint_left.mpr fun x hxF hxS => disjoint_left.mp hA'seam (hJSA' x hxS) hxF.2
  have hinjF : InjOn (⇑G) (P' ∩ h ⁻¹' (P ∩ Q)) := by
    intro x hx y hy hxy
    rw [hGL x hx.1 hx.2.1, hGL y hy.1 hy.2.1] at hxy
    have hxA : f₁ (h x) ∈ A := by
      rw [← hf₁seam]
      exact ⟨h x, hx.2, rfl⟩
    have hyA : f₁ (h y) ∈ A := by
      rw [← hf₁seam]
      exact ⟨h y, hy.2, rfl⟩
    exact hh.bijOn.injOn hx.1 hy.1 (hf₁.bijOn.injOn hx.2.1 hy.2.1 (hinjA hxA hyA hxy))
  have hinjS : InjOn (⇑G) (P' ∩ Q') := by
    intro x hx y hy hxy
    rw [hGR x hx.2, hGR y hy.2] at hxy
    have hxC : f₃ x ∈ C := by
      rw [← hf₃seam]
      exact ⟨x, hx, rfl⟩
    have hyC : f₃ y ∈ C := by
      rw [← hf₃seam]
      exact ⟨y, hy, rfl⟩
    exact hf₃.bijOn.injOn hx.2 hy.2 (hinjC hxC hyC hxy)
  have hsurjF : T.chart '' spliceCore ⊆ ⇑G '' (P' ∩ h ⁻¹' (P ∩ Q)) := by
    intro y hy
    obtain ⟨a', ha', rfl⟩ := hsurjA hy
    rw [← hf₁seam] at ha'
    obtain ⟨u, hu, rfl⟩ := ha'
    have huH : u ∈ H.domain := by
      rw [hHdomain]
      exact Or.inl hu.1
    obtain ⟨x, hx, rfl⟩ := hh.bijOn.surjOn huH
    exact ⟨x, ⟨hx, hu⟩, hGL x hx hu.1⟩
  have hsurjS : T.chart '' spliceCore ⊆ ⇑G '' (P' ∩ Q') := by
    intro y hy
    obtain ⟨c', hc', rfl⟩ := hsurjC hy
    rw [← hf₃seam] at hc'
    obtain ⟨x, hx, rfl⟩ := hc'
    exact ⟨x, hx, hGR x hx.2⟩
  have huniqG : ∀ x ∈ G.domain, ∀ y ∈ G.domain, G x = G y →
      G x ∈ T.chart '' (crossingFigure \ spliceCore) → x = y := by
    intro x hx y hy hxy hm
    by_contra hne
    apply hnotcore _ hm
    rw [← hdps, ← hGdps]
    exact ⟨⟨x, hx, y, hy, hne, rfl, hxy.symm⟩, hfigcyl hm⟩
  have hDG : ⇑D '' D.domain ⊆ ⇑G '' G.domain := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hdomains] at hx
    rcases hx with (hx | hx) | hx
    · rw [← hf₁.bijOn.image_eq] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      have huH : u ∈ H.domain := by
        rw [hHdomain]
        exact Or.inl hu
      obtain ⟨z, hz, rfl⟩ := hh.bijOn.surjOn huH
      exact ⟨z, by rw [hGdomain]; exact Or.inl hz, hGL z hz hu⟩
    · rw [← hf₂.bijOn.image_eq] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      have huH : u ∈ H.domain := by
        rw [hHdomain]
        exact Or.inr hu
      obtain ⟨z, hz, rfl⟩ := hh.bijOn.surjOn huH
      exact ⟨z, by rw [hGdomain]; exact Or.inl hz, hGM z hz hu⟩
    · rw [← hf₃.bijOn.image_eq] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, by rw [hGdomain]; exact Or.inr hz, hGR z hz⟩
  have himageG : ∀ x ∈ G.domain, G x ∈ T.chart '' spliceCylinder →
      G x ∈ T.chart '' crossingFigure := fun x hx hfx => by
    rw [hfig]
    exact ⟨hGim ⟨x, hx, rfl⟩, hfx⟩
  have hsurjG : T.chart '' crossingFigure ⊆ ⇑G '' G.domain := by
    rw [hfig]
    exact inter_subset_left.trans hDG
  have hfrontG : ∀ x ∈ frontier G.domain, G x ∈ BdM := by
    intro x hx
    have hm : G x ∈ ⇑D '' frontier D.domain := by
      rw [← hGfr]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hm
    rw [← hyx]
    have hyB : y ∈ D.domain ∩ ⇑D ⁻¹' BdM := by
      rw [hD.preimage_boundary_eq_frontier]
      exact hy
    exact hyB.2
  have hbdG : ∀ x ∈ G.domain, G x ∈ BdM → G x ∈ T.chart '' (crossingFigure \ spliceCore) →
      x ∈ frontier G.domain := by
    intro x hx hxB hxf
    have hrange : G x ∈ Set.range D.boundary := by
      rw [← hD.image_inter_boundary]
      exact ⟨hGim ⟨x, hx, rfl⟩, hxB⟩
    obtain ⟨⟨y, hy⟩, hyx⟩ := hrange
    have hm : G x ∈ ⇑G '' frontier G.domain := by
      rw [hGfr]
      exact ⟨y, hy, hyx⟩
    obtain ⟨x', hx', hx'x⟩ := hm
    have hxx' := huniqG x' (G.frontier_subset_domain hx') x hx hx'x (by rw [hx'x]; exact hxf)
    rw [← hxx']
    exact hx'
  have hhuG : ∀ i, ∀ x ∈ G.domain, ∀ y ∈ G.domain, G x = G y →
      G x ∈ T.chart '' crossOpenSheetOf i → x = y := fun i x hx y hy hxy hm =>
    huniqG x hx y hy hxy (image_mono (crossOpenSheetOf_subset_sdiff i) hm)
  have hsuG : ∀ i, T.chart '' crossOpenSheetOf i ⊆ ⇑G '' G.domain := fun i =>
    (image_mono ((crossOpenSheetOf_subset_sdiff i).trans sdiff_subset)).trans hsurjG
  have hVLc : IsClosed (P' ∩ h ⁻¹' P) := hhc.preimage_isClosed_of_isClosed hP'c hPc
  have hVMc : IsClosed (P' ∩ h ⁻¹' Q) := hhc.preimage_isClosed_of_isClosed hP'c hQc
  have hLR : Disjoint (P' ∩ h ⁻¹' P) Q' :=
    disjoint_left.mpr fun x hxL hxR => disjoint_left.mp hA'P (hJSA' x ⟨hxL.1, hxR⟩) hxL.2
  have hplaceG : ∀ i, crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' P ∨
      crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' Q ∨
        crossSeamPage T.chart G G.domain i ⊆ Q' := fun i =>
    crossSeamPage_subset_of_three_closed hcc hci hGdom hGc hJG (hhuG i) (hsuG i) hVLc hVMc hQ'c
      (by
        rw [hGdomain]
        rintro x (hx | hx)
        · rcases hhP' x hx with h1 | h2
          · exact Or.inl (Or.inl ⟨hx, h1⟩)
          · exact Or.inl (Or.inr ⟨hx, h2⟩)
        · exact Or.inr hx)
      (fun x hx => Or.inl ⟨hx.1.1, hx.1.2, hx.2.2⟩) (fun x hx => Or.inr ⟨hx.1.1, hx.2⟩) hLR
  have hcorr : ∀ i, (crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' P →
        crossSeamPage T.chart D D.domain i ⊆ U₁) ∧
      (crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' Q →
        crossSeamPage T.chart D D.domain i ⊆ U₂) ∧
      (crossSeamPage T.chart G G.domain i ⊆ Q' → crossSeamPage T.chart D D.domain i ⊆ U₃) := by
    intro i
    obtain ⟨z, hzG, hzW⟩ := nonempty_inter_preimage_crossOpenSheetOf (hsuG i)
    have hzZ : z ∈ crossSeamPage T.chart G G.domain i := subset_closure ⟨hzG, hzW⟩
    have hPi : ∀ y ∈ D.domain, D y = G z → y ∈ D.domain ∩ ⇑D ⁻¹' (T.chart '' crossOpenSheetOf i) :=
      fun y hy hyz => ⟨hy, by rw [mem_preimage, hyz]; exact hzW⟩
    refine ⟨fun hsub => ?_, fun hsub => ?_, fun hsub => ?_⟩
    · have hzL := hsub hzZ
      have hy := hf₁.bijOn.mapsTo hzL.2
      exact (hpick i _ (hPi _ (hU₁D hy) (hGL z hzL.1 hzL.2).symm)).1 hy
    · have hzM := hsub hzZ
      have hy := hf₂.bijOn.mapsTo hzM.2
      exact (hpick i _ (hPi _ (hU₂D hy) (hGM z hzM.1 hzM.2).symm)).2.1 hy
    · have hzR := hsub hzZ
      have hy := hf₃.bijOn.mapsTo hzR
      exact (hpick i _ (hPi _ (hU₃D hy) (hGR z hzR).symm)).2.2 hy
  have hclassG := fun i => crossSeamPage_class hcc hci hGdom hGc hJG hJFc hJSc hJFS hinjF hinjS
    hsurjF hsurjS (hhuG i) (hsuG i)
  obtain ⟨zF, hzF, -⟩ := hsurjF ⟨_, hmidcore, rfl⟩
  obtain ⟨zS, hzS, -⟩ := hsurjS ⟨_, hmidcore, rfl⟩
  have hUU : ∀ i {V W : Set (EuclideanSpace ℝ (Fin 2))}, V ∩ W ⊆ A ∪ C →
      crossSeamPage T.chart D D.domain i ⊆ V → crossSeamPage T.chart D D.domain i ⊆ W →
      False := by
    intro i V W hVW hV hW
    obtain ⟨x, hx⟩ := nonempty_inter_preimage_crossOpenSheetOf (hsuD i)
    exact disjoint_left.mp (disjoint_inter_preimage_crossOpenSheetOf hci hJD i) hx
      (hVW ⟨hV (subset_closure hx), hW (subset_closure hx)⟩)
  have h12 : U₁ ∩ U₂ ⊆ A ∪ C := hinter₁₂.subset.trans subset_union_left
  have h23 : U₂ ∩ U₃ ⊆ A ∪ C := hinter₂₃.subset.trans subset_union_right
  have h13 : U₁ ∩ U₃ ⊆ A ∪ C := by rw [hdisj₁₃.inter_eq]; exact empty_subset _
  have hFM : ∀ i, crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' Q →
      (fun x => f₂ (h x)) '' crossSeamPage T.chart G G.domain i ⊆
        crossSeamPage T.chart D D.domain i := by
    intro i hsub
    have hcont : ContinuousOn (fun x => f₂ (h x)) (crossSeamPage T.chart G G.domain i) :=
      (hf₂.isPiecewiseAffineOn.continuousOn.comp (hhc.mono inter_subset_left)
        fun x hx => hx.2).mono hsub
    refine (hcont.image_closure).trans (closure_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    have hxM := hsub (subset_closure hx)
    refine ⟨hU₂D (hf₂.bijOn.mapsTo hxM.2), ?_⟩
    rw [mem_preimage, ← hGM x hxM.1 hxM.2]
    exact hx.2
  have hG1 : ∀ i, crossSeamPage T.chart D D.domain i ⊆ U₁ →
      P' ∩ h ⁻¹' (P ∩ Q) ⊆ crossSeamPage T.chart G G.domain i := by
    intro i hi
    have hL : crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' P := by
      rcases hplaceG i with h1 | h2 | h3
      · exact h1
      · exact (hUU i h12 hi ((hcorr i).2.1 h2)).elim
      · exact (hUU i h13 hi ((hcorr i).2.2 h3)).elim
    rcases hclassG i with ⟨hs, -⟩ | ⟨hs, -⟩
    · exact hs
    · exact (disjoint_left.mp hLR (hL (hs hzS)) hzS.2).elim
  have hG2 : ∀ i, crossSeamPage T.chart D D.domain i ⊆ U₃ →
      P' ∩ Q' ⊆ crossSeamPage T.chart G G.domain i := by
    intro i hi
    have hR : crossSeamPage T.chart G G.domain i ⊆ Q' := by
      rcases hplaceG i with h1 | h2 | h3
      · exact (hUU i h13 ((hcorr i).1 h1) hi).elim
      · exact (hUU i h23 ((hcorr i).2.1 h2) hi).elim
      · exact h3
    rcases hclassG i with ⟨hs, -⟩ | ⟨hs, -⟩
    · exact (disjoint_left.mp hLR ⟨hzF.1, hzF.2.1⟩ (hR (hs hzF))).elim
    · exact hs
  have hMid : ∀ i, crossSeamPage T.chart D D.domain i ⊆ U₂ →
      crossSeamPage T.chart G G.domain i ⊆ P' ∩ h ⁻¹' Q := by
    intro i hi
    rcases hplaceG i with h1 | h2 | h3
    · exact (hUU i h12 ((hcorr i).1 h1) hi).elim
    · exact h2
    · exact (hUU i h23 hi ((hcorr i).2.2 h3)).elim
  have hG3 : ∀ i, A ⊆ crossSeamPage T.chart D D.domain i →
      crossSeamPage T.chart D D.domain i ⊆ U₂ → P' ∩ Q' ⊆ crossSeamPage T.chart G G.domain i := by
    intro i hAi hi
    rcases hclassG i with ⟨hs, -⟩ | ⟨hs, -⟩
    · have hC' : f₂ (h zF) ∈ C := by
        rw [← hf₂seam]
        exact ⟨h zF, hzF.2, rfl⟩
      have hmem := hFM i (hMid i hi) ⟨zF, hs hzF, rfl⟩
      rcases hclassD i with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact absurd hmem (disjoint_left.mp hd hC')
      · obtain ⟨x, hx⟩ := hA.nonempty
        exact absurd (hAi hx) (disjoint_left.mp hd hx)
    · exact hs
  have hG4 : ∀ i, C ⊆ crossSeamPage T.chart D D.domain i →
      crossSeamPage T.chart D D.domain i ⊆ U₂ →
        P' ∩ h ⁻¹' (P ∩ Q) ⊆ crossSeamPage T.chart G G.domain i := by
    intro i hCi hi
    rcases hclassG i with ⟨hs, -⟩ | ⟨hs, -⟩
    · exact hs
    · have hA'' : f₂ (h zS) ∈ A := hf₂A' _ (hJSA' zS hzS)
      have hmem := hFM i (hMid i hi) ⟨zS, hs hzS, rfl⟩
      rcases hclassD i with ⟨-, hd⟩ | ⟨-, hd⟩
      · obtain ⟨x, hx⟩ := hC.nonempty
        exact absurd (hCi hx) (disjoint_left.mp hd hx)
      · exact absurd hmem (disjoint_left.mp hd hA'')
  obtain ⟨α, γ, hα, hγ, hFα, hFγ, hSα, hSγ⟩ : ∃ α γ : Fin 4, (α = k ∨ α = k + 2) ∧
      (γ = k + 1 ∨ γ = k + 3) ∧
      P' ∩ h ⁻¹' (P ∩ Q) ⊆ crossSeamPage T.chart G G.domain α ∧
      P' ∩ h ⁻¹' (P ∩ Q) ⊆ crossSeamPage T.chart G G.domain γ ∧
      P' ∩ Q' ⊆ crossSeamPage T.chart G G.domain (α + 2) ∧
      P' ∩ Q' ⊆ crossSeamPage T.chart G G.domain (γ + 2) := by
    have e22 : k + 2 + 2 = k := by
      have key : ∀ x : Fin 4, x + 2 + 2 = x := by decide
      exact key k
    have e12 : k + 1 + 2 = k + 3 := by
      have key : ∀ x : Fin 4, x + 1 + 2 = x + 3 := by decide
      exact key k
    have e32 : k + 3 + 2 = k + 1 := by
      have key : ∀ x : Fin 4, x + 3 + 2 = x + 1 := by decide
      exact key k
    rcases hplA with ⟨hk, hk2⟩ | ⟨hk, hk2⟩ <;> rcases hplC with ⟨hk1, hk3⟩ | ⟨hk1, hk3⟩
    · exact ⟨k, k + 1, Or.inl rfl, Or.inl rfl, hG1 k hk, hG4 (k + 1) hCk1 hk1,
        hG3 (k + 2) hAk2 hk2, by rw [e12]; exact hG2 (k + 3) hk3⟩
    · exact ⟨k, k + 3, Or.inl rfl, Or.inr rfl, hG1 k hk, hG4 (k + 3) hCk3 hk3,
        hG3 (k + 2) hAk2 hk2, by rw [e32]; exact hG2 (k + 1) hk1⟩
    · exact ⟨k + 2, k + 1, Or.inr rfl, Or.inl rfl, hG1 (k + 2) hk2, hG4 (k + 1) hCk1 hk1,
        by rw [e22]; exact hG3 k hAk hk, by rw [e12]; exact hG2 (k + 3) hk3⟩
    · exact ⟨k + 2, k + 3, Or.inr rfl, Or.inr rfl, hG1 (k + 2) hk2, hG4 (k + 3) hCk3 hk3,
        by rw [e22]; exact hG3 k hAk hk, by rw [e32]; exact hG2 (k + 1) hk1⟩
  have hJG' : G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCore) = (P' ∩ Q') ∪ (P' ∩ h ⁻¹' (P ∩ Q)) := by
    rw [hJG, union_comm]
  have hcases : ∀ k α γ : Fin 4, (α = k ∨ α = k + 2) → (γ = k + 1 ∨ γ = k + 3) →
      (α = 0 ∧ γ = 3) ∨ (α = 3 ∧ γ = 0) ∨ (α = 1 ∧ γ = 2) ∨ (α = 2 ∧ γ = 1) ∨
        (α = 0 ∧ γ = 1) ∨ (α = 1 ∧ γ = 0) ∨ (α = 2 ∧ γ = 3) ∨ (α = 3 ∧ γ = 2) := by decide
  rcases hcases k α γ hα hγ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (nonempty_plCrossSeamReading_of_crossSeamPage hchart hcc hci hJG hJFc hJSc hJFS
      hinjF hinjS hsurjF hsurjS huniqG himageG hsurjG htubeBdM hfrontG hbdG hFα hFγ hSγ hSα)
  · exact Or.inl (nonempty_plCrossSeamReading_of_crossSeamPage hchart hcc hci hJG hJFc hJSc hJFS
      hinjF hinjS hsurjF hsurjS huniqG himageG hsurjG htubeBdM hfrontG hbdG hFγ hFα hSα hSγ)
  · exact Or.inl (nonempty_plCrossSeamReading_of_crossSeamPage hchart hcc hci hJG' hJSc hJFc
      hJFS.symm hinjS hinjF hsurjS hsurjF huniqG himageG hsurjG htubeBdM hfrontG hbdG hSγ hSα hFα
      hFγ)
  · exact Or.inl (nonempty_plCrossSeamReading_of_crossSeamPage hchart hcc hci hJG' hJSc hJFc
      hJFS.symm hinjS hinjF hsurjS hsurjF huniqG himageG hsurjG htubeBdM hfrontG hbdG hSα hSγ hFγ
      hFα)
  · exact Or.inr (nonempty_plCrossSeamReading_comp_crossQuarterTurn hchart hcc hci hJG hJFc hJSc
      hJFS hinjF hinjS hsurjF hsurjS huniqG himageG hsurjG htubeBdM hfrontG hbdG hFγ hFα hSα hSγ)
  · exact Or.inr (nonempty_plCrossSeamReading_comp_crossQuarterTurn hchart hcc hci hJG hJFc hJSc
      hJFS hinjF hinjS hsurjF hsurjS huniqG himageG hsurjG htubeBdM hfrontG hbdG hFα hFγ hSγ hSα)
  · exact Or.inr (nonempty_plCrossSeamReading_comp_crossQuarterTurn hchart hcc hci hJG' hJSc
      hJFc hJFS.symm hinjS hinjF hsurjS hsurjF huniqG himageG hsurjG htubeBdM hfrontG hbdG hSγ hSα
      hFα hFγ)
  · exact Or.inr (nonempty_plCrossSeamReading_comp_crossQuarterTurn hchart hcc hci hJG' hJSc
      hJFc hJFS.symm hinjS hinjF hsurjS hsurjF huniqG himageG hsurjG htubeBdM hfrontG hbdG hSα hSγ
      hFγ hFα)

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Homeomorph.Lemmas

open Set Bornology

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem exists_component_cover_sdiff_homeomorph_segment
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {a b : Schoenflies.Plane} (hab : a ≠ b) {D : Set Schoenflies.Plane}
    (hD : IsOpen D) (hconn : IsPreconnected D)
    (ha : F a ∉ D) (hb : F b ∉ D)
    (hseg : F '' (segment ℝ a b \ {a, b}) ⊆ D) :
    ∃ x ∈ D \ F '' segment ℝ a b, ∃ y ∈ D \ F '' segment ℝ a b,
      ∀ z ∈ D \ F '' segment ℝ a b,
        z ∈ connectedComponentIn (D \ F '' segment ℝ a b) x ∨
          z ∈ connectedComponentIn (D \ F '' segment ℝ a b) y := by
  let U := F ⁻¹' D
  have hU : IsOpen U := hD.preimage F.continuous
  have hUconn : IsPreconnected U := F.isPreconnected_preimage.mpr hconn
  have hsegU : segment ℝ a b \ {a, b} ⊆ U := fun z hz => hseg ⟨z, hz, rfl⟩
  obtain ⟨x, hx, y, hy, hcover⟩ :=
    Schoenflies.segment_crosscut_at_most_two hab hU hUconn ha hb hsegU
  have himage : F '' (U \ segment ℝ a b) = D \ F '' segment ℝ a b := by
    rw [image_sdiff F.injective, F.image_preimage]
  have hcomp {z : Schoenflies.Plane} (hz : z ∈ U \ segment ℝ a b) :
      F '' connectedComponentIn (U \ segment ℝ a b) z =
        connectedComponentIn (D \ F '' segment ℝ a b) (F z) := by
    rw [F.image_connectedComponentIn hz, himage]
  refine ⟨F x, himage ▸ mem_image_of_mem F hx, F y, himage ▸ mem_image_of_mem F hy, ?_⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := himage.symm ▸ hz
  rcases hcover w hw with hm | hm
  · exact Or.inl (hcomp hx ▸ mem_image_of_mem F hm)
  · exact Or.inr (hcomp hy ▸ mem_image_of_mem F hm)

private theorem exterior_inter_nonempty {C D : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hD : Schoenflies.IsSeparating D) :
    (Schoenflies.outside C ∩ Schoenflies.outside D).Nonempty := by
  by_contra h
  have hdisj : Disjoint (Schoenflies.outside C) (Schoenflies.outside D) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  have hsub : Schoenflies.outside C ⊆ Schoenflies.inside D ∪ D := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inr hzD
    · have hz' : z ∈ Schoenflies.inside D ∪ Schoenflies.outside D := by
        rw [Schoenflies.inside_union_outside]
        exact hzD
      exact Or.inl (hz'.resolve_right (fun ho => Set.disjoint_left.mp hdisj hz ho))
  exact hC.not_isBounded_outside
    ((hD.isBounded_inside.union hD.isJordanCurve.isCompact.isBounded).subset hsub)

private theorem isArcBetween_image_homeomorph_segment
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {a b : Schoenflies.Plane} (hab : a ≠ b) :
    Schoenflies.IsArcBetween (F '' segment ℝ a b) (F a) (F b) := by
  obtain ⟨f, hfc, hfi, himage, hleft, hright⟩ := Schoenflies.isArcBetween_segment hab
  refine ⟨F ∘ f, F.continuous.comp_continuousOn hfc,
    fun x hx y hy hxy => hfi hx hy (F.injective hxy), ?_, congrArg F hleft, congrArg F hright⟩
  rw [image_comp, himage]

theorem exists_cut_regions_of_homeomorph_segment
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {a b : Schoenflies.Plane} (hab : a ≠ b) (ha : F a ∈ C) (hb : F b ∈ C)
    (havoid : F '' (segment ℝ a b \ {a, b}) ⊆ Cᶜ) :
    ∃ A₀ A₁ : Set Schoenflies.Plane, Schoenflies.IsCutPair C (F a) (F b) A₀ A₁ ∧
      Schoenflies.IsJordanCurve (A₀ ∪ F '' segment ℝ a b) ∧
      Schoenflies.IsJordanCurve (A₁ ∪ F '' segment ℝ a b) ∧
      ∃ Ω V₀ V₁ : Set Schoenflies.Plane,
        F '' (segment ℝ a b \ {a, b}) ⊆ Ω ∧
        Ω \ F '' segment ℝ a b = V₀ ∪ V₁ ∧ Disjoint V₀ V₁ ∧
        V₀.Nonempty ∧ V₁.Nonempty ∧
        (∀ z ∈ V₀, connectedComponentIn (Ω \ F '' segment ℝ a b) z = V₀) ∧
        (∀ z ∈ V₁, connectedComponentIn (Ω \ F '' segment ℝ a b) z = V₁) ∧
        closure V₀ ∩ C = A₀ ∧ closure V₁ ∩ C = A₁ ∧
        ((Ω = Schoenflies.inside C ∧
          V₀ = Schoenflies.inside (A₀ ∪ F '' segment ℝ a b) ∧
          V₁ = Schoenflies.inside (A₁ ∪ F '' segment ℝ a b)) ∨
         (Ω = Schoenflies.outside C ∧
          V₀ = Schoenflies.outside (A₀ ∪ F '' segment ℝ a b) ∧
          V₁ = Schoenflies.inside (A₁ ∪ F '' segment ℝ a b) ∧
          Schoenflies.inside C ⊆ Schoenflies.inside (A₀ ∪ F '' segment ℝ a b)) ∨
         (Ω = Schoenflies.outside C ∧
          V₀ = Schoenflies.inside (A₀ ∪ F '' segment ℝ a b) ∧
          V₁ = Schoenflies.outside (A₁ ∪ F '' segment ℝ a b) ∧
          Schoenflies.inside C ⊆ Schoenflies.inside (A₁ ∪ F '' segment ℝ a b))) := by
  let P := F '' segment ℝ a b
  have hP := isArcBetween_image_homeomorph_segment F hab
  have hPdiff : F '' (segment ℝ a b \ {a, b}) = P \ {F a, F b} := by
    rw [image_sdiff F.injective, image_pair]
  have hmeet : P ∩ C = {F a, F b} := by
    apply Subset.antisymm
    · intro z hz
      by_contra hn
      exact havoid (hPdiff.symm ▸ ⟨hz.1, hn⟩) hz.2
    · exact pair_subset ⟨hP.left_mem, ha⟩ ⟨hP.right_mem, hb⟩
  obtain ⟨A₀, A₁, hcut⟩ := Schoenflies.exists_isCutPair hC ha hb (F.injective.ne hab)
  have hJ (A : Set Schoenflies.Plane) (hA : Schoenflies.IsArcBetween A (F a) (F b)) (hAC : A ⊆ C) :
      Schoenflies.IsJordanCurve (A ∪ P) := by
    apply Schoenflies.isJordanCurve_union hA hP
    intro z hzA hzP
    have hm : z ∈ ({F a, F b} : Set Schoenflies.Plane) := hmeet ▸ ⟨hzP, hAC hzA⟩
    exact hm
  have hJ₀ := hJ A₀ hcut.fst hcut.fst_subset
  have hJ₁ := hJ A₁ hcut.snd hcut.snd_subset
  have hCsep := Schoenflies.jordan_curve_theorem hC
  have hJ₀sep := Schoenflies.jordan_curve_theorem hJ₀
  have hJ₁sep := Schoenflies.jordan_curve_theorem hJ₁
  obtain ⟨hconn, hne⟩ := hP.preconnected_diff
  have hdisj : Disjoint (P \ {F a, F b}) C :=
    disjoint_left.mpr (fun z hz hzC => havoid (hPdiff.symm ▸ hz) hzC)
  obtain ⟨Ω, Ω', hΩ, hPΩ⟩ := hCsep.exists_isRegionPair_subset hconn hne hdisj
  have hfar (A : Set Schoenflies.Plane) (hAC : A ⊆ C) : Disjoint Ω' (A ∪ P) := by
    apply disjoint_left.mpr
    intro z hz hzAP
    rcases hzAP with hzA | hzP
    · exact hΩ.right.subset_compl hz (hAC hzA)
    · by_cases hpq : z ∈ ({F a, F b} : Set Schoenflies.Plane)
      · exact hΩ.right.subset_compl hz ((pair_subset ha hb) hpq)
      · exact disjoint_left.mp hΩ.disjoint (hPΩ ⟨hzP, hpq⟩) hz
  obtain ⟨W₀, V₀, hWV₀, hfar₀⟩ := hJ₀sep.exists_isRegionPair_subset
    (hΩ.right.isConnected hCsep).isPreconnected (hΩ.right.isConnected hCsep).nonempty
    (hfar A₀ hcut.fst_subset)
  obtain ⟨W₁, V₁, hWV₁, hfar₁⟩ := hJ₁sep.exists_isRegionPair_subset
    (hΩ.right.isConnected hCsep).isPreconnected (hΩ.right.isConnected hCsep).nonempty
    (hfar A₁ hcut.snd_subset)
  obtain ⟨⟨hV₀sub, hV₀comp⟩, ⟨hV₁sub, hV₁comp⟩, hVne, hclosure₀, hclosure₁⟩ :=
    Schoenflies.crosscut_cells hCsep hJ₀sep hJ₁sep hcut.fst_subset hcut.snd_subset
      (hmeet ▸ pair_subset hcut.fst.left_mem hcut.fst.right_mem)
      (hmeet ▸ pair_subset hcut.snd.left_mem hcut.snd.right_mem) hcut.ne hΩ hWV₀ hfar₀ hWV₁ hfar₁
  have hnonempty₀ := (hWV₀.right.isConnected hJ₀sep).nonempty
  have hnonempty₁ := (hWV₁.right.isConnected hJ₁sep).nonempty
  obtain ⟨v₀, hv₀⟩ := hnonempty₀
  obtain ⟨v₁, hv₁⟩ := hnonempty₁
  have hvcomp : connectedComponentIn (Ω \ P) v₀ ≠ connectedComponentIn (Ω \ P) v₁ := by
    rw [hV₀comp v₀ hv₀, hV₁comp v₁ hv₁]
    exact hVne
  have haΩ : F a ∉ Ω := fun hz => hΩ.left.subset_compl hz ha
  have hbΩ : F b ∉ Ω := fun hz => hΩ.left.subset_compl hz hb
  obtain ⟨x, _, y, _, hcover⟩ := exists_component_cover_sdiff_homeomorph_segment F hab
    (hΩ.left.isOpen hCsep) (hΩ.left.isConnected hCsep).isPreconnected haΩ hbΩ (hPdiff ▸ hPΩ)
  have hcover' :=
    Schoenflies.covered_by_two_components_of_ne hcover (hV₀sub hv₀) (hV₁sub hv₁) hvcomp
  have hcovereq : Ω \ P = V₀ ∪ V₁ := by
    apply Subset.antisymm
    · intro z hz
      have hm := hcover' z hz
      rwa [hV₀comp v₀ hv₀, hV₁comp v₁ hv₁] at hm
    · exact union_subset hV₀sub hV₁sub
  have hVdisj : Disjoint V₀ V₁ := by
    apply disjoint_left.mpr
    intro z hz₀ hz₁
    exact hVne ((hV₀comp z hz₀).symm.trans (hV₁comp z hz₁))
  refine ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hPdiff ▸ hPΩ, hcovereq,
    hVdisj, ⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩, hV₀comp, hV₁comp, hclosure₀, hclosure₁, ?_⟩
  rcases hΩ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hV₀ : V₀ = Schoenflies.inside (A₀ ∪ P) := by
      rcases hWV₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hCsep.not_isBounded_outside (hJ₀sep.isBounded_inside.subset hfar₀)).elim
      · rfl
    have hV₁ : V₁ = Schoenflies.inside (A₁ ∪ P) := by
      rcases hWV₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hCsep.not_isBounded_outside (hJ₁sep.isBounded_inside.subset hfar₁)).elim
      · rfl
    exact Or.inl ⟨rfl, hV₀, hV₁⟩
  · rcases hWV₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hWV₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨z, hz₀, hz₁⟩ := exterior_inter_nonempty hJ₀sep hJ₁sep
      exact (disjoint_left.mp hVdisj hz₀ hz₁).elim
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, hfar₀⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, hfar₁⟩)
    · have hbounded : IsBounded ((Schoenflies.inside (A₀ ∪ P) ∪ Schoenflies.inside (A₁ ∪ P)) ∪ P) :=
        (hJ₀sep.isBounded_inside.union hJ₁sep.isBounded_inside).union hP.isArc.isCompact.isBounded
      apply (hCsep.not_isBounded_outside (hbounded.subset ?_)).elim
      intro z hz
      by_cases hzP : z ∈ P
      · exact Or.inr hzP
      · exact Or.inl (hcovereq ▸ ⟨hz, hzP⟩)


theorem exists_cut_regions_of_band
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane)
    (ha : B (-1, 0) ∈ C) (hb : B (1, 0) ∈ C)
    (havoid : B '' (Ioo (-1 : ℝ) 1 ×ˢ {0}) ⊆ Cᶜ) :
    ∃ A₀ A₁ : Set Schoenflies.Plane, Schoenflies.IsCutPair C (B (-1, 0)) (B (1, 0)) A₀ A₁ ∧
      Schoenflies.IsJordanCurve (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      Schoenflies.IsJordanCurve (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      ∃ Ω V₀ V₁ : Set Schoenflies.Plane,
        B '' (Ioo (-1 : ℝ) 1 ×ˢ {0}) ⊆ Ω ∧
        Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}) = V₀ ∪ V₁ ∧ Disjoint V₀ V₁ ∧
        V₀.Nonempty ∧ V₁.Nonempty ∧
        (∀ z ∈ V₀, connectedComponentIn (Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₀) ∧
        (∀ z ∈ V₁, connectedComponentIn (Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₁) ∧
        closure V₀ ∩ C = A₀ ∧ closure V₁ ∩ C = A₁ ∧
        (∀ r : ℝ, 0 < r → r < 1 → ∃ ε : ℝ, 0 < ε ∧
          B '' (Ioo (-r) r ×ˢ Ioo 0 ε) ⊆ V₀ ∧
          B '' (Ioo (-r) r ×ˢ Ioo (-ε) 0) ⊆ V₁) ∧
        ((Ω = Schoenflies.inside C ∧
          V₀ = Schoenflies.inside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          V₁ = Schoenflies.inside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}))) ∨
         (Ω = Schoenflies.outside C ∧
          V₀ = Schoenflies.outside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          V₁ = Schoenflies.inside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          Schoenflies.inside C ⊆ Schoenflies.inside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}))) ∨
         (Ω = Schoenflies.outside C ∧
          V₀ = Schoenflies.inside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          V₁ = Schoenflies.outside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          Schoenflies.inside C ⊆ Schoenflies.inside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})))) := by
  let L : Schoenflies.Plane ≃L[ℝ] (ℝ × ℝ) :=
    Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.trans Complex.equivRealProdCLM
  have hLi (z : ℝ × ℝ) : L.symm z = Schoenflies.Plane.mk z.1 z.2 := by
    ext i
    fin_cases i <;> simp [L]
  have hL (x y : ℝ) : L (Schoenflies.Plane.mk x y) = (x, y) := by
    rw [← hLi (x, y), L.apply_symm_apply]
  let a := Schoenflies.Plane.mk (-1) 0
  let b := Schoenflies.Plane.mk 1 0
  have hab : a ≠ b := by
    intro heq
    have hh := congrArg (fun z => z 0) heq
    norm_num [a, b] at hh
  let F := L.toHomeomorph.trans B
  have hFa : F a = B (-1, 0) := by change B (L a) = _; rw [hL]
  have hFb : F b = B (1, 0) := by change B (L b) = _; rw [hL]
  have hseg : L '' segment ℝ a b = Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ) := by
    rw [show L '' segment ℝ a b = segment ℝ (L a) (L b) from
      image_segment ℝ L.toLinearEquiv.toLinearMap.toAffineMap a b, hL, hL, segment_eq_image]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul,
        mul_zero, add_zero, mem_prod, mem_Icc, mem_singleton_iff]
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, trivial⟩
    · rintro ⟨hz, hz0⟩
      refine ⟨(z.1 + 1) / 2, ⟨by linarith [hz.1], by linarith [hz.2]⟩, ?_⟩
      apply Prod.ext
      · change (1 - (z.1 + 1) / 2) * (-1) + (z.1 + 1) / 2 * 1 = z.1
        ring
      · change (1 - (z.1 + 1) / 2) * 0 + (z.1 + 1) / 2 * 0 = z.2
        simpa using (mem_singleton_iff.mp hz0).symm
  have himage : F '' segment ℝ a b = B '' (Icc (-1 : ℝ) 1 ×ˢ {0}) := by
    change (B ∘ L) '' segment ℝ a b = _
    rw [image_comp, hseg]
  have hopen : F '' (segment ℝ a b \ {a, b}) = B '' (Ioo (-1 : ℝ) 1 ×ˢ {0}) := by
    have hdiff : (Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ)) \ {(-1, 0), (1, 0)} =
        Ioo (-1 : ℝ) 1 ×ˢ {0} := by
      ext z
      constructor
      · rintro ⟨⟨hz, hz0⟩, hne⟩
        refine ⟨⟨lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_⟩, hz0⟩
        · intro heq
          exact hne (Or.inl (Prod.ext heq.symm hz0))
        · intro heq
          exact hne (Or.inr (Prod.ext heq hz0))
      · rintro ⟨hz, hz0⟩
        refine ⟨⟨⟨hz.1.le, hz.2.le⟩, hz0⟩, ?_⟩
        rintro (heq | heq)
        · exact hz.1.ne' (congrArg Prod.fst heq)
        · exact hz.2.ne (congrArg Prod.fst heq)
    rw [image_sdiff F.injective, image_pair, hFa, hFb, himage,
      ← image_pair, ← image_sdiff B.injective, hdiff]
  have hh := exists_cut_regions_of_homeomorph_segment hC F hab
    (hFa.symm ▸ ha) (hFb.symm ▸ hb) (hopen.symm ▸ havoid)
  rw [hFa, hFb, himage, hopen] at hh
  obtain ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hPΩ, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hcases⟩ := hh
  have hCsep := Schoenflies.jordan_curve_theorem hC
  have hJ₀sep := Schoenflies.jordan_curve_theorem hJ₀
  have hΩ : Schoenflies.IsRegionOf C Ω := by
    rcases hcases with hc | hc | hc
    · exact Or.inl hc.1
    · exact Or.inr hc.1
    · exact Or.inr hc.1
  have hV₀ : Schoenflies.IsRegionOf (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) V₀ := by
    rcases hcases with hc | hc | hc
    · exact Or.inl hc.2.1
    · exact Or.inr hc.2.1
    · exact Or.inl hc.2.1
  obtain ⟨W, hWV⟩ : ∃ W, Schoenflies.IsRegionPair (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) V₀ W := by
    rcases hV₀ with hV₀ | hV₀
    · exact ⟨_, Or.inl ⟨hV₀, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨hV₀, rfl⟩⟩
  have hstrip (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ∃ ε : ℝ, 0 < ε ∧
      ((B '' (Ioo (-r) r ×ˢ Ioo 0 ε) ⊆ V₀ ∧ B '' (Ioo (-r) r ×ˢ Ioo (-ε) 0) ⊆ V₁) ∨
       (B '' (Ioo (-r) r ×ˢ Ioo 0 ε) ⊆ V₁ ∧ B '' (Ioo (-r) r ×ˢ Ioo (-ε) 0) ⊆ V₀)) := by
    have hcompact : IsCompact (Icc (-r) r ×ˢ ({0} : Set ℝ)) :=
      isCompact_Icc.prod isCompact_singleton
    have hsub : Icc (-r) r ×ˢ ({0} : Set ℝ) ⊆ B ⁻¹' Ω := by
      intro z hz
      exact hPΩ ⟨z, ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩, rfl⟩
    obtain ⟨ε, hε, hεsub⟩ := hcompact.exists_thickening_subset_open
      ((hΩ.isOpen hCsep).preimage B.continuous) hsub
    have htube : B '' (Ioo (-r) r ×ˢ Ioo (-ε) ε) ⊆ Ω := by
      rintro _ ⟨z, hz, rfl⟩
      apply hεsub
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(z.1, 0), ⟨⟨hz.1.1.le, hz.1.2.le⟩, rfl⟩, ?_⟩
      simpa only [Prod.dist_eq, dist_self, dist_zero_right, Real.norm_eq_abs,
        max_eq_right (abs_nonneg z.2)]
        using abs_lt.mpr hz.2
    have hcurve : ∀ z ∈ Ioo (-r) r ×ˢ Ioo (-ε) ε,
        B z ∈ A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}) ↔ z.2 = 0 := by
      intro z hz
      constructor
      · rintro (hA | ⟨w, hw, heq⟩)
        · exact (hΩ.subset_compl (htube ⟨z, hz, rfl⟩) (hcut.fst_subset hA)).elim
        · have hzw := B.injective heq
          exact hzw ▸ hw.2
      · intro hz0
        exact Or.inr ⟨z, ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz0⟩, rfl⟩
    have hother {S : Set (ℝ × ℝ)}
        (hS : S ⊆ Ioo (-r) r ×ˢ Ioo (-ε) ε)
        (hne : ∀ z ∈ S, z.2 ≠ 0) (hW : B '' S ⊆ W) : B '' S ⊆ V₁ := by
      rintro _ ⟨z, hz, rfl⟩
      have hP : B z ∉ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}) := by
        rintro ⟨w, hw, heq⟩
        exact hne z hz (B.injective heq ▸ hw.2)
      have hm : B z ∈ V₀ ∪ V₁ := hcover ▸ ⟨htube ⟨z, hS hz, rfl⟩, hP⟩
      exact hm.resolve_left (fun hv => disjoint_left.mp hWV.disjoint hv (hW ⟨z, hz, rfl⟩))
    have hpossub : Ioo (-r) r ×ˢ Ioo (0 : ℝ) ε ⊆ Ioo (-r) r ×ˢ Ioo (-ε) ε :=
      fun z hz => ⟨hz.1, ⟨by linarith [hz.2.1], hz.2.2⟩⟩
    have hnegsub : Ioo (-r) r ×ˢ Ioo (-ε) (0 : ℝ) ⊆ Ioo (-r) r ×ˢ Ioo (-ε) ε :=
      fun z hz => ⟨hz.1, ⟨hz.2.1, by linarith [hz.2.2]⟩⟩
    obtain hs | hs := flowBox_halves_in_opposite_regions
      (hWV.left.isOpen hJ₀sep) (hWV.right.isOpen hJ₀sep) hWV.disjoint hWV.union_eq
      (hWV.left.frontier_eq hJ₀sep) (hWV.right.frontier_eq hJ₀sep)
      B.toOpenPartialHomeomorph (by linarith) hε (by simp) hcurve
    · exact ⟨ε, hε, Or.inl ⟨hs.1, hother hnegsub (fun z hz => hz.2.2.ne) hs.2⟩⟩
    · exact ⟨ε, hε, Or.inr ⟨hother hpossub (fun z hz => hz.2.1.ne') hs.1, hs.2⟩⟩
  obtain ⟨ε₀, hε₀, hs₀⟩ := hstrip (1 / 2) (by norm_num) (by norm_num)
  have horient (U V : Set Schoenflies.Plane) (hUV : Disjoint U V)
      (hseed : B '' (Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ioo 0 ε₀) ⊆ U)
      (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
      (hwrong : B '' (Ioo (-r) r ×ˢ Ioo 0 ε) ⊆ V) : False := by
    let z : ℝ × ℝ := (0, min ε₀ ε / 2)
    have hy : 0 < z.2 := half_pos (lt_min hε₀ hε)
    have hy₀ : z.2 < ε₀ := by dsimp [z]; have := min_le_left ε₀ ε; linarith
    have hyε : z.2 < ε := by dsimp [z]; have := min_le_right ε₀ ε; linarith
    exact disjoint_left.mp hUV (hseed ⟨z, ⟨⟨by norm_num [z], by norm_num [z]⟩, hy, hy₀⟩, rfl⟩)
      (hwrong ⟨z, ⟨⟨by dsimp [z]; linarith, hr⟩, hy, hyε⟩, rfl⟩)
  rcases hs₀ with hs₀ | hs₀
  · refine ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hPΩ, hcover, hdisj,
      hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, ?_, hcases⟩
    intro r hr hr1
    obtain ⟨ε, hε, hs⟩ := hstrip r hr hr1
    rcases hs with hs | hs
    · exact ⟨ε, hε, hs⟩
    · exact (horient V₀ V₁ hdisj hs₀.1 r ε hr hε hs.1).elim
  · refine ⟨A₁, A₀, hcut.symm, hJ₁, hJ₀, Ω, V₁, V₀, hPΩ,
      hcover.trans (union_comm _ _), hdisj.symm, hn₁, hn₀, hcomp₁, hcomp₀, hcl₁, hcl₀, ?_, ?_⟩
    · intro r hr hr1
      obtain ⟨ε, hε, hs⟩ := hstrip r hr hr1
      rcases hs with hs | hs
      · exact (horient V₁ V₀ hdisj.symm hs₀.1 r ε hr hε hs.1).elim
      · exact ⟨ε, hε, hs⟩
    · rcases hcases with hc | hc | hc
      · exact Or.inl ⟨hc.1, hc.2.2, hc.2.1⟩
      · exact Or.inr (Or.inr ⟨hc.1, hc.2.2.1, hc.2.1, hc.2.2.2⟩)
      · exact Or.inr (Or.inl ⟨hc.1, hc.2.2.1, hc.2.1, hc.2.2.2⟩)


theorem exists_cut_regions_of_attached_band
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane)
    {h : ℝ} (hh : 0 < h)
    (hedges : ∀ a ∈ ({-1, 1} : Set ℝ), (fun u => B (a, u)) '' Ioo (-h) h ⊆ C)
    (havoid : B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h) ⊆ Cᶜ) :
    ∃ A₀ A₁ : Set Schoenflies.Plane, Schoenflies.IsCutPair C (B (-1, 0)) (B (1, 0)) A₀ A₁ ∧
      Schoenflies.IsJordanCurve (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      Schoenflies.IsJordanCurve (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      ∃ Ω V₀ V₁ : Set Schoenflies.Plane,
        B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h) ⊆ Ω ∧
        Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}) = V₀ ∪ V₁ ∧ Disjoint V₀ V₁ ∧
        V₀.Nonempty ∧ V₁.Nonempty ∧
        (∀ z ∈ V₀, connectedComponentIn (Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₀) ∧
        (∀ z ∈ V₁, connectedComponentIn (Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₁) ∧
        closure V₀ ∩ C = A₀ ∧ closure V₁ ∩ C = A₁ ∧
        B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 h) ⊆ V₀ ∧
        B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) 0) ⊆ V₁ ∧
        (∀ a ∈ ({-1, 1} : Set ℝ),
          (fun u => B (a, u)) '' Ioo 0 h ⊆ A₀ ∧
          (fun u => B (a, u)) '' Ioo (-h) 0 ⊆ A₁) ∧
        ((Ω = Schoenflies.inside C ∧
          V₀ = Schoenflies.inside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          V₁ = Schoenflies.inside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}))) ∨
         (Ω = Schoenflies.outside C ∧
          V₀ = Schoenflies.outside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          V₁ = Schoenflies.inside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          Schoenflies.inside C ⊆ Schoenflies.inside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0}))) ∨
         (Ω = Schoenflies.outside C ∧
          V₀ = Schoenflies.inside (A₀ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          V₁ = Schoenflies.outside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
          Schoenflies.inside C ⊆ Schoenflies.inside (A₁ ∪ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})))) := by
  have hzero : (0 : ℝ) ∈ Ioo (-h) h := ⟨neg_neg_of_pos hh, hh⟩
  have ha : B (-1, 0) ∈ C := hedges (-1) (by simp) ⟨0, hzero, rfl⟩
  have hb : B (1, 0) ∈ C := hedges 1 (by simp) ⟨0, hzero, rfl⟩
  have hcore : B '' (Ioo (-1 : ℝ) 1 ×ˢ {0}) ⊆ Cᶜ := by
    apply Subset.trans _ havoid
    exact image_mono (prod_mono Subset.rfl (singleton_subset_iff.mpr hzero))
  obtain ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hPΩ, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hsigned, hcases⟩ :=
      exists_cut_regions_of_band hC B ha hb hcore
  have hΩ : Schoenflies.IsRegionOf C Ω := by
    rcases hcases with hc | hc | hc
    · exact Or.inl hc.1
    · exact Or.inr hc.1
    · exact Or.inr hc.1
  have hSconn : IsPreconnected (B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h)) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image B B.continuous.continuousOn
  have hzeroΩ : B (0, 0) ∈ Ω := hPΩ ⟨(0, 0), ⟨⟨by norm_num, by norm_num⟩, rfl⟩, rfl⟩
  have hSΩ : B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h) ⊆ Ω := by
    rw [← hΩ.connectedComponentIn_eq (Schoenflies.jordan_curve_theorem hC) hzeroΩ]
    exact hSconn.subset_connectedComponentIn
      ⟨(0, 0), ⟨⟨by norm_num, by norm_num⟩, hzero⟩, rfl⟩ havoid
  obtain ⟨ε, hε, hpos, hneg⟩ := hsigned (1 / 2) (by norm_num) (by norm_num)
  let u := min h ε / 2
  have hu : 0 < u := half_pos (lt_min hh hε)
  have huh : u < h := by dsimp [u]; have := min_le_left h ε; linarith
  have huε : u < ε := by dsimp [u]; have := min_le_right h ε; linarith
  have hposseed : B (0, u) ∈ V₀ := hpos ⟨(0, u), ⟨⟨by norm_num, by norm_num⟩, hu, huε⟩, rfl⟩
  have hnegseed : B (0, -u) ∈ V₁ := hneg ⟨(0, -u),
    ⟨⟨by norm_num, by norm_num⟩, by linarith, neg_neg_of_pos hu⟩, rfl⟩
  have hhalf (J : Set ℝ) (hJ : IsPreconnected J) (hJh : J ⊆ Ioo (-h) h) (hJ0 : 0 ∉ J)
      (v : ℝ) (hv : v ∈ J) (V : Set Schoenflies.Plane)
      (hcomp : connectedComponentIn (Ω \ B '' (Icc (-1 : ℝ) 1 ×ˢ {0})) (B (0, v)) = V) :
      B '' (Ioo (-1 : ℝ) 1 ×ˢ J) ⊆ V := by
    rw [← hcomp]
    apply ((isPreconnected_Ioo.prod hJ).image B
      B.continuous.continuousOn).subset_connectedComponentIn
      ⟨(0, v), ⟨⟨by norm_num, by norm_num⟩, hv⟩, rfl⟩
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hSΩ ⟨z, ⟨hz.1, hJh hz.2⟩, rfl⟩, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hzero' : z.2 = 0 := B.injective heq ▸ hw.2
    exact hJ0 (hzero' ▸ hz.2)
  have hupper : B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 h) ⊆ V₀ := by
    apply hhalf _ isPreconnected_Ioo
      (fun v hv => ⟨by linarith [hv.1], hv.2⟩) (by simp) u ⟨hu, huh⟩ V₀ (hcomp₀ _ hposseed)
  have hlower : B '' (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) 0) ⊆ V₁ := by
    apply hhalf _ isPreconnected_Ioo
      (fun v hv => ⟨hv.1, by linarith [hv.2]⟩) (by simp) (-u) ⟨by linarith, neg_neg_of_pos hu⟩ V₁
      (hcomp₁ _ hnegseed)
  refine ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hSΩ, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hupper, hlower, ?_, hcases⟩
  have hedgearc (J : Set ℝ) (hJh : J ⊆ Ioo (-h) h) (V A : Set Schoenflies.Plane)
      (hsub : B '' (Ioo (-1 : ℝ) 1 ×ˢ J) ⊆ V) (hcl : closure V ∩ C = A)
      (a : ℝ) (ha : a ∈ ({-1, 1} : Set ℝ)) : (fun u => B (a, u)) '' J ⊆ A := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← hcl]
    refine ⟨closure_mono hsub ?_, hedges a ha ⟨v, hJh hv, rfl⟩⟩
    rw [← B.image_closure, closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    refine ⟨(a, v), ⟨?_, subset_closure hv⟩, rfl⟩
    rcases mem_insert_iff.mp ha with rfl | ha
    · norm_num
    · obtain rfl := mem_singleton_iff.mp ha
      norm_num
  intro a ha
  exact ⟨hedgearc _ (fun v hv => ⟨by linarith [hv.1], hv.2⟩) V₀ A₀ hupper hcl₀ a ha,
    hedgearc _ (fun v hv => ⟨hv.1, by linarith [hv.2]⟩) V₁ A₁ hlower hcl₁ a ha⟩

end DifferentialGeometry.Topology.PlanarJordan

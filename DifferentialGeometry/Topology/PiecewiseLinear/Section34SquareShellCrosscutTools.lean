import DifferentialGeometry.Topology.PiecewiseLinear.Section34SquareShellArcs
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem square_shell_paths_disjoint_of_disjoint_base_images {c : ℝ} (hc : 0 < c)
    {γ δ : ℝ → ℝ × ℝ}
    (hγ : MapsTo γ (Icc 0 c) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hδ : MapsTo δ (Icc 0 c) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hdis : Disjoint (γ '' Icc 0 c) (δ '' Icc 0 c)) :
    Disjoint ((fun t : ℝ => section34SquareShellFlatten c (γ t, t)) '' Icc 0 c)
      ((fun t : ℝ => section34SquareShellFlatten c (δ t, t)) '' Icc 0 c) := by
  apply disjoint_left.mpr
  rintro y ⟨s, hs, hsy⟩ ⟨t, ht, hty⟩
  have heq := (isPLHomeomorphOn_section34SquareShellFlatten hc).bijOn.injOn
    (Or.inr ⟨hγ hs, hs⟩) (Or.inr ⟨hδ ht, ht⟩) (hsy.trans hty.symm)
  exact disjoint_left.mp hdis (mem_image_of_mem _ hs)
    ⟨t, ht, (congrArg Prod.fst heq).symm⟩

theorem exists_PL_arc_of_two_external_arcs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A P U₀ U₁ : Set E} {δ η₀ η₁ : ℝ → E} {c : ℝ} (hc : 0 < c)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hAP : A ⊆ P)
    (hη₀ : IsPLHomeomorphOn η₀ (Icc 0 c) U₀)
    (hη₁ : IsPLHomeomorphOn η₁ (Icc 0 c) U₁)
    (hzero₀ : η₀ 0 = δ 0) (hzero₁ : η₁ 0 = δ 1)
    (hU₀ : U₀ ∩ P = {δ 0}) (hU₁ : U₁ ∩ P = {δ 1}) (hdis : Disjoint U₀ U₁) :
    ∃ α : ℝ → E, IsPLHomeomorphOn α (Icc 0 1) (A ∪ (U₀ ∪ U₁)) ∧
      α 0 = η₀ c ∧ α 1 = η₁ c := by
  have hscale : IsPLHomeomorphOn (fun t : ℝ => c * t) (Icc 0 1) (Icc 0 c) := by
    simpa only [add_zero] using
      (isPLHomeomorphOn_mul_add_Icc hc (show c * 0 + 0 = 0 by ring)
        (show c * 1 + 0 = c by ring))
  have hα₀ := isPLHomeomorphOn_comp_one_sub (hscale.trans hη₀)
  have hα₁ := hscale.trans hη₁
  have hmeet₀ : U₀ ∩ A = {δ 0} := Subset.antisymm
    (fun _ h => hU₀.subset ⟨h.1, hAP h.2⟩)
    (fun _ h => by
      have heq : _ = δ 0 := h
      rw [heq]
      exact ⟨(hU₀.symm.subset rfl).1, hδ.bijOn.mapsTo (by norm_num)⟩)
  have hmeet₁ : A ∩ U₁ = {δ 1} := Subset.antisymm
    (fun _ h => hU₁.subset ⟨h.2, hAP h.1⟩)
    (fun _ h => by
      have heq : _ = δ 1 := h
      rw [heq]
      exact ⟨hδ.bijOn.mapsTo (by norm_num), (hU₁.symm.subset rfl).1⟩)
  obtain ⟨l, hl, hlzero, -, hlone⟩ := exists_isPLHomeomorphOn_Icc_concat hα₀ hδ
    (by simp only [Function.comp_apply, sub_self, mul_zero, hzero₀])
    (by simpa only [Function.comp_apply, sub_self, mul_zero, hzero₀] using hmeet₀)
  have hmeet : (U₀ ∪ A) ∩ U₁ = {l 1} := by
    rw [union_inter_distrib_right, hdis.inter_eq, empty_union, hmeet₁, hlone]
  obtain ⟨α, hα, hαzero, -, hαone⟩ := exists_isPLHomeomorphOn_Icc_concat hl hα₁
    (by simpa only [Function.comp_apply, mul_zero, hzero₁] using hlone.symm) hmeet
  refine ⟨α, ?_, ?_, ?_⟩
  · simpa only [union_assoc, union_left_comm U₀ A U₁] using hα
  · simpa only [Function.comp_apply, sub_zero, mul_one] using hαzero.trans hlzero
  · simpa only [Function.comp_apply, mul_one] using hαone

theorem inter_two_external_arc_unions
    {E : Type*} {A B P U₀ U₁ V₀ V₁ : Set E} {p₀ p₁ : E}
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : A ∩ B = {p₀, p₁})
    (hU₀ : U₀ ∩ P = {p₀}) (hU₁ : U₁ ∩ P = {p₁})
    (hV₀ : V₀ ∩ P = {p₀}) (hV₁ : V₁ ∩ P = {p₁})
    (h₀ : U₀ ∩ V₀ = {p₀}) (h₁ : U₁ ∩ V₁ = {p₁})
    (h01 : Disjoint U₀ V₁) (h10 : Disjoint U₁ V₀) :
    (A ∪ (U₀ ∪ U₁)) ∩ (B ∪ (V₀ ∪ V₁)) = {p₀, p₁} := by
  apply Subset.antisymm
  · rintro x ⟨ha | hu₀ | hu₁, hb | hv₀ | hv₁⟩
    · exact hAB.subset ⟨ha, hb⟩
    · exact Or.inl (hV₀.subset ⟨hv₀, hAP ha⟩)
    · exact Or.inr (hV₁.subset ⟨hv₁, hAP ha⟩)
    · exact Or.inl (hU₀.subset ⟨hu₀, hBP hb⟩)
    · exact Or.inl (h₀.subset ⟨hu₀, hv₀⟩)
    · exact (disjoint_left.mp h01 hu₀ hv₁).elim
    · exact Or.inr (hU₁.subset ⟨hu₁, hBP hb⟩)
    · exact (disjoint_left.mp h10 hu₁ hv₀).elim
    · exact Or.inr (h₁.subset ⟨hu₁, hv₁⟩)
  · intro x hx
    obtain ⟨hxA, hxB⟩ := hAB.symm.subset hx
    exact ⟨Or.inl hxA, Or.inl hxB⟩

end DifferentialGeometry.Topology.PiecewiseLinear

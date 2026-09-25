import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem concat_with_half_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} {α β : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hjoin : β 0 = α 1) (hAB : A ∩ B = {α 1}) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) (A ∪ B) ∧
      γ 0 = α 0 ∧ γ (1 / 2) = α 1 ∧ γ 1 = β 1 ∧
      γ '' Icc (0 : ℝ) (1 / 2) = A ∧ γ '' Icc (1 / 2 : ℝ) 1 = B := by
  have h₀ := isPLHomeomorphOn_mul_add_Icc (two_pos : (0 : ℝ) < 2)
    (show (2 : ℝ) * 0 + 0 = 0 by ring) (show (2 : ℝ) * (1 / 2) + 0 = 1 by ring)
  have h₁ := isPLHomeomorphOn_mul_add_Icc (two_pos : (0 : ℝ) < 2)
    (show (2 : ℝ) * (1 / 2) + -1 = 0 by ring) (show (2 : ℝ) * 1 + -1 = 1 by ring)
  have hfirst := h₀.trans hα
  have hsecond := h₁.trans hβ
  have hinter : Icc (0 : ℝ) (1 / 2) ∩ Icc (1 / 2) 1 = {1 / 2} := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, h₀⟩, h₁, -⟩
      exact le_antisymm h₀ h₁
    · rintro rfl
      norm_num
  obtain ⟨γ, hγ, hleft, hright⟩ := exists_isPLHomeomorphOn_union
    isHPolytope_Icc.isPolyhedron isHPolytope_Icc.isPolyhedron hfirst hsecond
    (by
      rw [hinter]
      rintro t rfl
      simpa using hjoin.symm)
    (by
      rw [hinter, hAB]
      rintro y rfl
      exact ⟨1 / 2, rfl, by norm_num⟩)
  rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at hγ
  refine ⟨γ, hγ, ?_, ?_, ?_, hleft.image_eq.trans hfirst.image_eq,
    hright.image_eq.trans hsecond.image_eq⟩
  · simpa using hleft (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2))
  · simpa using hleft (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 (1 / 2))
  · have h := hright (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 1)
    norm_num [Function.comp_apply] at h
    exact h

theorem exists_seam_arc_and_disjoint_compensation_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} {δ ε : ℝ → E}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hε : IsPLHomeomorphOn ε (Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1) (hAB : A ∩ B = {δ 0, δ 1}) :
    ∃ γ : ℝ → E,
      IsPLHomeomorphOn γ (Icc 0 1) (ε '' Icc (0 : ℝ) (1 / 4) ∪ δ '' Icc (0 : ℝ) (1 / 4)) ∧
      γ 0 = ε (1 / 4) ∧ γ (1 / 2) = δ 0 ∧ γ 1 = δ (1 / 4) ∧
      γ '' Icc (0 : ℝ) (1 / 2) = ε '' Icc (0 : ℝ) (1 / 4) ∧
      γ '' Icc (1 / 2 : ℝ) 1 = δ '' Icc (0 : ℝ) (1 / 4) ∧
      Disjoint (γ '' Icc (0 : ℝ) 1) (δ '' Icc (1 / 2 : ℝ) (3 / 4)) ∧
      δ 1 ∉ γ '' Icc (0 : ℝ) 1 ∧
      Disjoint (δ '' Icc (1 / 2 : ℝ) (3 / 4)) ({δ 0, δ 1} : Set E) := by
  have hδs := isPLHomeomorphOn_comp_mul_add_Icc hδ (a := 0) (b := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have hεs := isPLHomeomorphOn_comp_mul_add_Icc hε (a := 0) (b := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have hδin {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 4)) : t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hδmid {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) : t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hcross {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (heq : ε s = δ t) : t = 0 ∨ t = 1 := by
    have hm := hAB.subset ⟨hδ.bijOn.mapsTo ht, heq ▸ hε.bijOn.mapsTo hs⟩
    rcases hm with h | h
    · exact Or.inl (hδ.bijOn.injOn ht (by norm_num) h)
    · exact Or.inr (hδ.bijOn.injOn ht (by norm_num) h)
  have hinter : ε '' Icc (0 : ℝ) (1 / 4) ∩ δ '' Icc (0 : ℝ) (1 / 4) = {δ 0} := by
    apply Subset.antisymm
    · rintro z ⟨⟨s, hs, rfl⟩, t, ht, heq⟩
      rcases hcross (hδin hs) (hδin ht) heq.symm with h | h
      · exact heq.symm.trans (congrArg δ h)
      · linarith [ht.2]
    · rintro z rfl
      exact ⟨⟨0, by norm_num, hεzero⟩, ⟨0, by norm_num, rfl⟩⟩
  obtain ⟨γ, hγ, hγzero, hγmid, hγone, hγleft, hγright⟩ := concat_with_half_images
    (isPLHomeomorphOn_comp_one_sub hεs) hδs (by simpa using hεzero.symm)
    (by simpa [hεzero] using hinter)
  refine ⟨γ, hγ, ?_, ?_, ?_, hγleft, hγright, ?_, ?_, ?_⟩
  · simpa using hγzero
  · simpa [hεzero] using hγmid
  · simpa using hγone
  · rw [hγ.image_eq]
    apply disjoint_left.mpr
    rintro z (hz | hz) ⟨t, ht, rfl⟩
    · obtain ⟨s, hs, heq⟩ := hz
      rcases hcross (hδin hs) (hδmid ht) heq with h | h <;> linarith [ht.1, ht.2]
    · obtain ⟨s, hs, heq⟩ := hz
      have he := hδ.bijOn.injOn (hδin hs) (hδmid ht) heq
      linarith [hs.2, ht.1]
  · rw [hγ.image_eq]
    rintro (⟨t, ht, heq⟩ | ⟨t, ht, heq⟩)
    · have he := hε.bijOn.injOn (hδin ht) (by norm_num) (heq.trans hεone.symm)
      linarith [ht.2]
    · have he := hδ.bijOn.injOn (hδin ht) (by norm_num) heq
      linarith [ht.2]
  · apply disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ (h | h)
    · have he := hδ.bijOn.injOn (hδmid ht) (by norm_num) h
      linarith [ht.1]
    · have he := hδ.bijOn.injOn (hδmid ht) (by norm_num) h
      linarith [ht.2]

end DifferentialGeometry.Topology.PiecewiseLinear

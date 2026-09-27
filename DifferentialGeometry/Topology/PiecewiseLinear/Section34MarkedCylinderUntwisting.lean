import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.precomp_preserving_caps [FiniteDimensional ℝ E]
    {g : E × ℝ → F} {P : Set E} {S : Set F} (hg : IsCylindricalDiagram g P S)
    {H : E × ℝ → E × ℝ}
    (hH : IsPLHomeomorphOn H (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1))
    (hcap : ∀ a ∈ ({0, 1} : Set ℝ), H '' (P ×ˢ {a}) = P ×ˢ {a}) :
    IsCylindricalDiagram (g ∘ H) P S := by
  have hlevel (a : ℝ) (ha : a ∈ ({0, 1} : Set ℝ)) {x : E × ℝ}
      (hx : x ∈ P ×ˢ Icc (0 : ℝ) 1) (hxa : (H x).2 = a) : x.2 = a := by
    have hmem : H x ∈ P ×ˢ {a} := ⟨(hH.bijOn.mapsTo hx).1, hxa⟩
    obtain ⟨z, hz, heq⟩ := (hcap a ha).symm.subset hmem
    have haI : a ∈ Icc (0 : ℝ) 1 := by rcases ha with rfl | rfl <;> norm_num
    have hzI : z ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hz.1, hz.2.symm ▸ haI⟩
    exact (congrArg Prod.snd (hH.bijOn.injOn hx hzI heq.symm)).trans hz.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hg.isPiecewiseAffineOn.comp hH.isPiecewiseAffineOn
    rwa [inter_eq_left.mpr (show P ×ˢ Icc (0 : ℝ) 1 ⊆ H ⁻¹' (P ×ˢ Icc 0 1) from
      hH.bijOn.mapsTo)] at h
  · rw [image_comp, hH.image_eq, hg.image_eq]
  · rw [image_comp, image_comp, hcap 0 (by simp), hcap 1 (by simp)]
    exact hg.image_top_eq_bottom
  · intro x hx y hy hxy
    rcases hg.eq_or_endpoints (H x) (hH.bijOn.mapsTo hx) (H y) (hH.bijOn.mapsTo hy) hxy
      with heq | hends | hends
    · exact Or.inl (hH.bijOn.injOn hx hy heq)
    · exact Or.inr (Or.inl
        ⟨hlevel 0 (by simp) hx hends.1, hlevel 1 (by simp) hy hends.2⟩)
    · exact Or.inr (Or.inr
        ⟨hlevel 1 (by simp) hx hends.1, hlevel 0 (by simp) hy hends.2⟩)

theorem IsCylindricalDiagram.untwist_with_marked_pseudoisotopy [FiniteDimensional ℝ E]
    {g : E × ℝ → F} {P : Set E} {S : Set F} (hg : IsCylindricalDiagram g P S)
    {u : E → E} (hu : IsPLHomeomorphOn u P P)
    (hends : ∀ x ∈ P, g (x, 0) = g (u x, 1)) {H : E × ℝ → E × ℝ}
    (hH : IsPLHomeomorphOn H (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1))
    (hzero : ∀ x ∈ P, H (x, 0) = (x, 0))
    (hone : ∀ x ∈ P, H (x, 1) = (u x, 1)) :
    IsCylindricalDiagram (g ∘ H) P S ∧
      (∀ x ∈ P, (g ∘ H) (x, 0) = (g ∘ H) (x, 1)) ∧
      (∀ x ∈ P, (g ∘ H) (x, 0) = g (x, 0)) ∧
      ∀ X : Set E, H '' (X ×ˢ Icc (0 : ℝ) 1) = X ×ˢ Icc (0 : ℝ) 1 →
        (g ∘ H) '' (X ×ˢ Icc (0 : ℝ) 1) = g '' (X ×ˢ Icc (0 : ℝ) 1) := by
  have hcap : ∀ a ∈ ({0, 1} : Set ℝ), H '' (P ×ˢ {a}) = P ×ˢ {a} := by
    intro a ha
    rcases ha with rfl | rfl
    · have heq : EqOn H id (P ×ˢ ({0} : Set ℝ)) := by
        rintro ⟨x, t⟩ ⟨hx, rfl⟩
        exact hzero x hx
      exact heq.image_eq.trans (image_id _)
    · have heq : EqOn H (Prod.map u id) (P ×ˢ ({1} : Set ℝ)) := by
        rintro ⟨x, t⟩ ⟨hx, rfl⟩
        exact hone x hx
      rw [heq.image_eq, prodMap_image_prod, hu.image_eq, image_id]
  refine ⟨hg.precomp_preserving_caps hH hcap, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Function.comp_apply, hzero x hx, hone x hx, hends x hx]
  · intro x hx
    rw [Function.comp_apply, hzero x hx]
  · intro X hX
    rw [image_comp, hX]

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.precomp_base_equivalence
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {f : E × ℝ → F} {P : Set E} {P' : Set E'} {S : Set F}
    (hf : IsCylindricalDiagram f P S) {φ : E' → E} (hφ : IsPLHomeomorphOn φ P' P) :
    IsCylindricalDiagram (f ∘ Prod.map φ id) P' S := by
  have hprod := hφ.prodMap
    (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron.isPLHomeomorphOn_id
  have hc := hf.isPiecewiseAffineOn.comp hprod.isPiecewiseAffineOn
  have heq : (P' ×ˢ Icc (0 : ℝ) 1) ∩ (Prod.map φ id) ⁻¹' (P ×ˢ Icc (0 : ℝ) 1) =
      P' ×ˢ Icc (0 : ℝ) 1 := inter_eq_left.mpr hprod.bijOn.mapsTo
  rw [heq] at hc
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [image_comp, prodMap_image_prod, hφ.image_eq, image_id, hf.image_eq]
  · rw [image_comp, image_comp, prodMap_image_prod, prodMap_image_prod, hφ.image_eq,
      image_id, image_id]
    exact hf.image_top_eq_bottom
  · intro x hx y hy hxy
    rcases hf.eq_or_endpoints _ (hprod.bijOn.mapsTo hx) _ (hprod.bijOn.mapsTo hy) hxy with
      heq | hend | hend
    · exact Or.inl (hprod.bijOn.injOn hx hy heq)
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr hend)

theorem IsCylindricalDiagram.precomp_base [FiniteDimensional ℝ E]
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) {φ : E → E} (hφ : IsPLHomeomorphOn φ P P) :
    IsCylindricalDiagram (f ∘ Prod.map φ id) P S :=
  hf.precomp_base_equivalence hφ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem image_cylindrical_region_of_conjugacy {f : E × ℝ → F} {P A : Set E}
    {φ : E → E} {H : F → F} (hA : A ⊆ P)
    (hconj : ∀ x ∈ P ×ˢ Icc (0 : ℝ) 1, H (f x) = f (φ x.1, x.2)) :
    H '' (f '' (A ×ˢ Icc (0 : ℝ) 1)) = f '' ((φ '' A) ×ˢ Icc (0 : ℝ) 1) := by
  rw [image_image]
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨(φ x.1, x.2), ⟨⟨x.1, hx.1, rfl⟩, hx.2⟩, (hconj x ⟨hA hx.1, hx.2⟩).symm⟩
  · rintro _ ⟨⟨y, t⟩, ⟨⟨x, hx, rfl⟩, ht⟩, rfl⟩
    exact ⟨(x, t), ⟨hx, ht⟩, hconj (x, t) ⟨hA hx, ht⟩⟩

theorem IsCylindricalDiagram.exists_supported_base_motion
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P L : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hLP : L ⊆ P)
    (hfront : frontier S ⊆ f '' (L ×ˢ Icc (0 : ℝ) 1))
    {φ : E → E} (hφ : IsPLHomeomorphOn φ P P) (hfix : EqOn φ id L) :
    ∃ H : F ≃ₜ F, IsPLHomeomorphOn H univ univ ∧ EqOn H id Sᶜ ∧
      (∀ x ∈ P ×ˢ Icc (0 : ℝ) 1, H (f x) = f (φ x.1, x.2)) ∧
      ∀ A ⊆ P, H '' (f '' (A ×ˢ Icc (0 : ℝ) 1)) =
        f '' ((φ '' A) ×ˢ Icc (0 : ℝ) 1) := by
  let g := f ∘ Prod.map φ id
  have hg : IsCylindricalDiagram g P S := hf.precomp_base hφ
  have hgends (x : E) (hx : x ∈ P) : g (x, 0) = g (x, 1) :=
    hends (φ x) (hφ.bijOn.mapsTo hx)
  obtain ⟨H, hH, hconj⟩ := exists_isPLHomeomorphOn_of_eq_endMap hP hf hg
    hP.isPLHomeomorphOn_id hends hgends
  have hS : IsPolyhedron S := by
    rw [← hf.image_strip_union (a := 1 / 2) (by norm_num)]
    have h₀ := hf.isPLHomeomorphOn_strip hP (a := 0) (b := 1 / 2) le_rfl
      (by norm_num) (Or.inr (by norm_num))
    have h₁ := hf.isPLHomeomorphOn_strip hP (a := 1 / 2) (b := 1)
      (by norm_num) le_rfl (Or.inl (by norm_num))
    exact ((hP.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      h₀.isPiecewiseAffineOn h₀.bijOn.injOn).union
      ((hP.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
        h₁.isPiecewiseAffineOn h₁.bijOn.injOn)
  have hHfix : EqOn H id (frontier S) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hfront hz
    rw [hconj x ⟨hLP hx.1, hx.2⟩]
    change f (φ x.1, x.2) = f x
    rw [hfix hx.1]
    rfl
  obtain ⟨Ψ, hΨ, hΨH, hoff⟩ := hH.exists_extension_of_eqOn_frontier hS hHfix
  have hΨconj (x : E × ℝ) (hx : x ∈ P ×ˢ Icc (0 : ℝ) 1) :
      Ψ (f x) = f (φ x.1, x.2) :=
    (hΨH (hf.image_eq ▸ ⟨x, hx, rfl⟩)).trans (hconj x hx)
  exact ⟨Ψ, hΨ, hoff, hΨconj, fun A hA => image_cylindrical_region_of_conjugacy hA hΨconj⟩

end DifferentialGeometry.Topology.PiecewiseLinear

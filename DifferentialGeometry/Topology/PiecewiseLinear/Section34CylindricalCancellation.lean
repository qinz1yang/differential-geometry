import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalMotion
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.inter_images_base_regions {f : E × ℝ → F} {P A B : Set E}
    {S : Set F} (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hAP : A ⊆ P) (hBP : B ⊆ P) :
    f '' (A ×ˢ Icc (0 : ℝ) 1) ∩ f '' (B ×ˢ Icc (0 : ℝ) 1) =
      f '' ((A ∩ B) ×ˢ Icc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    have hxy := (hf.eq_iff_fst_eq_and_circle_eq hends
      ⟨hBP hy.1, hy.2⟩ ⟨hAP hx.1, hx.2⟩).mp hyx
    exact ⟨x, ⟨⟨hx.1, hxy.1 ▸ hy.1⟩, hx.2⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩, ⟨x, ⟨hx.1.2, hx.2⟩, rfl⟩⟩

theorem IsCylindricalDiagram.disjoint_fibers {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {x y : E} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : x ≠ y) : Disjoint (f '' ({x} ×ˢ Icc (0 : ℝ) 1))
      (f '' ({y} ×ˢ Icc (0 : ℝ) 1)) := by
  rw [disjoint_iff_inter_eq_empty, hf.inter_images_base_regions hends
    (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hy)]
  have heq : ({x} : Set E) ∩ {y} = ∅ := disjoint_iff_inter_eq_empty.mp
    (disjoint_singleton.mpr hxy)
  rw [heq, empty_prod, image_empty]

theorem IsCylindricalDiagram.exists_supported_crosscut_replacement
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P L B B' : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hrim : r '' stdSimplexBoundary 2 = L)
    (hfront : frontier S ⊆ f '' (L ×ˢ Icc (0 : ℝ) 1))
    {γ γ' : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) B)
    (hBP : B ⊆ P) (hBL : B ∩ L = {γ 0, γ 1})
    (hγ' : IsPLHomeomorphOn γ' (Icc 0 1) B')
    (hB'P : B' ⊆ P) (hB'L : B' ∩ L = {γ' 0, γ' 1})
    (hzero : γ 0 = γ' 0) (hone : γ 1 = γ' 1) :
    ∃ H : F ≃ₜ F, IsPLHomeomorphOn H univ univ ∧ EqOn H id Sᶜ ∧
      H '' (f '' (B ×ˢ Icc (0 : ℝ) 1)) = f '' (B' ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ A ⊆ P, f '' (A ×ˢ Icc (0 : ℝ) 1) ∩ H '' (f '' (B ×ˢ Icc (0 : ℝ) 1)) =
        f '' ((A ∩ B') ×ˢ Icc (0 : ℝ) 1) := by
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hL : IsPLSphere 1 L := hrim ▸ hr.isPLSphere_image_stdSimplexBoundary
  have hLP : L ⊆ P := by
    rw [← hrim]
    exact (image_mono (show stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) from
      inter_subset_left)).trans hr.bijOn.mapsTo.image_subset
  obtain ⟨φ, hφ, hφfix, hφB⟩ := exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary
    hr hrim hr hrim hγ hBP hBL hγ' hB'P hB'L hL.isPolyhedron.isPLHomeomorphOn_id hzero hone
  obtain ⟨H, hH, hoff, -, himage⟩ :=
    hf.exists_supported_base_motion hP.isPolyhedron hends hLP hfront hφ hφfix
  have hB : H '' (f '' (B ×ˢ Icc (0 : ℝ) 1)) = f '' (B' ×ˢ Icc (0 : ℝ) 1) := by
    rw [himage B hBP, hφB]
  refine ⟨H, hH, hoff, hB, ?_⟩
  intro A hAP
  rw [hB, hf.inter_images_base_regions hends hAP hB'P]

end DifferentialGeometry.Topology.PiecewiseLinear

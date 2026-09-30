import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSides
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_annulus_chart_of_base_arc_with_levels
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P B : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P) :
    ∃ ρ : (Fin 3 → ℝ) × ℝ → F,
      IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' (B ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ρ (stdTriangleLoop t, r) = f (γ r, t)) ∧
      ∀ Q ⊆ Icc (0 : ℝ) 1,
        ρ '' (stdSimplexBoundary 2 ×ˢ Q) = f '' ((γ '' Q) ×ˢ Icc (0 : ℝ) 1) := by
  have hB : IsPolyhedron B :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ).isPolyhedron
  have hg := (hf.restrict_base_of_eq_ends hB hBP hends).precomp_base_equivalence hγ
  obtain ⟨ρ, hρ, hconj⟩ := hg.exists_isPLHomeomorphOn_annulus_of_eq_ends
    (fun x hx => hends (γ x) (hBP (hγ.bijOn.mapsTo hx)))
  refine ⟨ρ, hρ, hconj, ?_⟩
  intro Q hQ
  apply Subset.antisymm
  · rintro _ ⟨⟨z, r⟩, ⟨hz, hr⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    exact ⟨(γ r, t), ⟨mem_image_of_mem γ hr, ht⟩, (hconj r (hQ hr) t ht).symm⟩
  · rintro _ ⟨⟨z, t⟩, ⟨⟨r, hr, rfl⟩, ht⟩, rfl⟩
    exact ⟨(stdTriangleLoop t, r),
      ⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht), hr⟩,
      hconj r (hQ hr) t ht⟩

private theorem spoke_param_isPLHomeomorphOn (i : Fin 4) :
    IsPLHomeomorphOn (fun r : ℝ => r • fourSpokeModelLeaf i) (Icc 0 1)
      (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) := by
  have himage : (fun r : ℝ => r • fourSpokeModelLeaf i) '' Icc 0 1 =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) := by
    simpa using (segment_eq_image ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)).symm
  rw [← himage]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (fourSpokeModelLeaf i)).toAffineMap
      isHPolytope_Icc)
    (smul_left_injective ℝ (fourSpokeModelLeaf_ne_zero i)).injOn.bijOn_image

open Classical in
theorem IsCylindricalDiagram.exists_crossing_ribbon_annulus_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) :
    ∃ ρ : Fin 4 → (Fin 3 → ℝ) × ℝ → E,
      (∀ i, IsPLHomeomorphOn (ρ i) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' section34MarkedRibbon i)) ∧
      (∀ i r, r ∈ Icc (0 : ℝ) 1 → ∀ t ∈ Icc (0 : ℝ) 1,
        ρ i (stdTriangleLoop t, r) = f (r • fourSpokeModelLeaf i, t)) ∧
      (∀ i j z, z ∈ stdSimplexBoundary 2 → ρ i (z, 0) = ρ j (z, 0)) ∧
      (∀ i, ρ i '' (stdSimplexBoundary 2 ×ˢ {0}) = f '' section34MarkedAxis) ∧
      (∀ i, ρ i '' (stdSimplexBoundary 2 ×ˢ {1}) =
        f '' ({fourSpokeModelLeaf i} ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ i r s, 0 ≤ r → s ≤ 1 →
        IsPLHomeomorphOn (ρ i) (stdSimplexBoundary 2 ×ˢ Icc r s)
          (f '' (((fun t : ℝ => t • fourSpokeModelLeaf i) '' Icc r s) ×ˢ Icc (0 : ℝ) 1)) := by
  have hex (i : Fin 4) := hf.exists_annulus_chart_of_base_arc_with_levels hends
    (spoke_param_isPLHomeomorphOn i) (segment_zero_fourSpokeModelLeaf_subset i)
  choose ρ hρ hconj hlevels using hex
  refine ⟨ρ, hρ, hconj, ?_, ?_, ?_, ?_⟩
  · intro i j z hz
    obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    rw [hconj i 0 (by norm_num) t ht, hconj j 0 (by norm_num) t ht]
    simp
  · intro i
    simpa [section34MarkedAxis] using hlevels i {0} (by norm_num)
  · intro i
    simpa using hlevels i {1} (by norm_num)
  · intro i r s hr hs
    have hsub : Icc r s ⊆ Icc (0 : ℝ) 1 := fun _ ht => ⟨hr.trans ht.1, ht.2.trans hs⟩
    have hrestrict := (hρ i).restrict
      (isPolyhedron_stdSimplexBoundary_two.prod isHPolytope_Icc.isPolyhedron)
      (prod_mono_right hsub)
    rwa [hlevels i (Icc r s) hsub] at hrestrict

end DifferentialGeometry.Topology.PiecewiseLinear

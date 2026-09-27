import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalMotion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCylinder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.restrict_base_of_eq_ends
    {f : E × ℝ → F} {P Q : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) :
    IsCylindricalDiagram f Q (f '' (Q ×ˢ Icc (0 : ℝ) 1)) := by
  refine ⟨hf.isPiecewiseAffineOn.mono_of_isPolyhedron
    (hQ.prod isHPolytope_Icc.isPolyhedron) (prod_mono_left hQP), rfl, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht1 : t = 1 := ht
      subst t
      exact ⟨(x, 0), ⟨hx, rfl⟩, hends x (hQP hx)⟩
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(x, 1), ⟨hx, rfl⟩, (hends x (hQP hx)).symm⟩
  · exact fun x hx y hy hxy => hf.eq_or_endpoints x ⟨hQP hx.1, hx.2⟩ y ⟨hQP hy.1, hy.2⟩ hxy

theorem IsCylindricalDiagram.exists_annulus_chart_of_base_arc
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P B : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P) :
    ∃ ρ : (Fin 3 → ℝ) × ℝ → F,
      IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' (B ×ˢ Icc (0 : ℝ) 1)) ∧
      ρ '' (stdSimplexBoundary 2 ×ˢ {0}) = f '' ({γ 0} ×ˢ Icc (0 : ℝ) 1) ∧
      ρ '' (stdSimplexBoundary 2 ×ˢ {1}) = f '' ({γ 1} ×ˢ Icc (0 : ℝ) 1) := by
  have hB : IsPolyhedron B :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ).isPolyhedron
  have hg := (hf.restrict_base_of_eq_ends hB hBP hends).precomp_base_equivalence hγ
  obtain ⟨ρ, hρ, hconj⟩ := hg.exists_isPLHomeomorphOn_annulus_of_eq_ends
    (fun x hx => hends (γ x) (hBP (hγ.bijOn.mapsTo hx)))
  have hlevel (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ρ '' (stdSimplexBoundary 2 ×ˢ {s}) = f '' ({γ s} ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have hts : t = s := ht
      subst t
      obtain ⟨r, hr, rfl⟩ := stdTriangleLoop_image.symm.subset hz
      exact ⟨(γ s, r), ⟨rfl, hr⟩, (hconj s hs r hr).symm⟩
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have hzs : z = γ s := hz
      subst z
      exact ⟨(stdTriangleLoop t, s),
        ⟨stdTriangleLoop_image.subset ⟨t, ht, rfl⟩, rfl⟩, hconj s hs t ht⟩
  exact ⟨ρ, hρ, hlevel 0 (by norm_num), hlevel 1 (by norm_num)⟩

theorem IsCylindricalDiagram.isAnnulusOn_base_arc
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P B : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P) :
    IsAnnulusOn (f '' (B ×ˢ Icc (0 : ℝ) 1))
      (f '' ({γ 0} ×ˢ Icc (0 : ℝ) 1)) (f '' ({γ 1} ×ˢ Icc (0 : ℝ) 1)) := by
  obtain ⟨ρ, hρ, hzero, hone⟩ := hf.exists_annulus_chart_of_base_arc hends hγ hBP
  have h := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn.injOn
  rwa [hρ.image_eq, hzero, hone] at h

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
private theorem eq_on_fiber_of_end_identification
    {P : Set E} {S : Set F} {f : E × ℝ → F} {g : E × ℝ → G}
    (hf : IsCylindricalDiagram f P S)
    (he : ∀ x ∈ P, ∀ y ∈ P, f (x, 0) = f (y, 1) → g (x, 0) = g (y, 1))
    {x y : E × ℝ} (hx : x ∈ P ×ˢ Icc 0 1) (hy : y ∈ P ×ˢ Icc 0 1)
    (hxy : f x = f y) : g x = g y := by
  rcases hf.eq_or_endpoints x hx y hy hxy with hxy | hends | hends
  · rw [hxy]
  · have h0 : (x.1, (0 : ℝ)) = x := Prod.ext rfl hends.1.symm
    have h1 : (y.1, (1 : ℝ)) = y := Prod.ext rfl hends.2.symm
    have h := he x.1 hx.1 y.1 hy.1 (by rwa [h0, h1])
    rwa [h0, h1] at h
  · have h0 : (y.1, (0 : ℝ)) = y := Prod.ext rfl hends.2.symm
    have h1 : (x.1, (1 : ℝ)) = x := Prod.ext rfl hends.1.symm
    have h := he y.1 hy.1 x.1 hx.1 (by simpa only [h0, h1] using hxy.symm)
    rw [h0, h1] at h
    exact h.symm

theorem IsCylindricalDiagram.exists_isPLHomeomorphOn_of_end_identification
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {P : Set E} (hP : IsPolyhedron P) {S : Set F} {T : Set G}
    {f : E × ℝ → F} {g : E × ℝ → G}
    (hf : IsCylindricalDiagram f P S) (hg : IsCylindricalDiagram g P T)
    (he : ∀ x ∈ P, ∀ y ∈ P, f (x, 0) = f (y, 1) ↔ g (x, 0) = g (y, 1)) :
    ∃ H : F → G, IsPLHomeomorphOn H S T ∧ ∀ x ∈ P ×ˢ Icc 0 1, H (f x) = g x := by
  let Q₀ := P ×ˢ Icc (0 : ℝ) (1 / 2)
  let Q₁ := P ×ˢ Icc (1 / 2 : ℝ) 1
  have hQ₀ : IsPolyhedron Q₀ := hP.prod isHPolytope_Icc.isPolyhedron
  have hQ₁ : IsPolyhedron Q₁ := hP.prod isHPolytope_Icc.isPolyhedron
  have hsub₀ : Q₀ ⊆ P ×ˢ Icc 0 1 :=
    fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans (by norm_num)⟩
  have hsub₁ : Q₁ ⊆ P ×ˢ Icc 0 1 :=
    fun _ hx => ⟨hx.1, (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hx.2.1, hx.2.2⟩
  have hf₀ : IsPLHomeomorphOn f Q₀ (f '' Q₀) :=
    hf.isPLHomeomorphOn_strip hP le_rfl (by norm_num) (Or.inr (by norm_num))
  have hf₁ : IsPLHomeomorphOn f Q₁ (f '' Q₁) :=
    hf.isPLHomeomorphOn_strip hP (by norm_num) le_rfl (Or.inl (by norm_num))
  have hg₀ : IsPLHomeomorphOn g Q₀ (g '' Q₀) :=
    hg.isPLHomeomorphOn_strip hP le_rfl (by norm_num) (Or.inr (by norm_num))
  have hg₁ : IsPLHomeomorphOn g Q₁ (g '' Q₁) :=
    hg.isPLHomeomorphOn_strip hP (by norm_num) le_rfl (Or.inl (by norm_num))
  let u := g ∘ Function.invFunOn f Q₀
  let v := g ∘ Function.invFunOn f Q₁
  have hu : IsPLHomeomorphOn u (f '' Q₀) (g '' Q₀) := hf₀.symm.trans hg₀
  have hv : IsPLHomeomorphOn v (f '' Q₁) (g '' Q₁) := hf₁.symm.trans hg₁
  have hfg {x y : E × ℝ} (hx : x ∈ P ×ˢ Icc 0 1) (hy : y ∈ P ×ˢ Icc 0 1) :
      f x = f y ↔ g x = g y :=
    ⟨eq_on_fiber_of_end_identification hf (fun _ hx _ hy => (he _ hx _ hy).mp) hx hy,
      eq_on_fiber_of_end_identification hg (fun _ hx _ hy => (he _ hx _ hy).mpr) hx hy⟩
  have huv : EqOn u v (f '' Q₀ ∩ f '' Q₁) := by
    intro z hz
    have h0 := hf₀.bijOn.surjOn.mapsTo_invFunOn hz.1
    have h1 := hf₁.bijOn.surjOn.mapsTo_invFunOn hz.2
    exact (hfg (hsub₀ h0) (hsub₁ h1)).mp
      ((hf₀.bijOn.invOn_invFunOn.2 hz.1).trans (hf₁.bijOn.invOn_invFunOn.2 hz.2).symm)
  have hinter : SurjOn u (f '' Q₀ ∩ f '' Q₁) (g '' Q₀ ∩ g '' Q₁) := by
    rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    have hxy : f x = f y := (hfg (hsub₀ hx) (hsub₁ hy)).mpr hyx.symm
    refine ⟨f x, ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩, ?_⟩
    exact congrArg g (hf₀.bijOn.invOn_invFunOn.1 hx)
  obtain ⟨H, hH, hHu, hHv⟩ := exists_isPLHomeomorphOn_union
    (hQ₀.image_of_isPiecewiseAffineOn hf₀.isPiecewiseAffineOn hf₀.bijOn.injOn)
    (hQ₁.image_of_isPiecewiseAffineOn hf₁.isPiecewiseAffineOn hf₁.bijOn.injOn)
    hu hv huv hinter
  have hfcover := hf.image_strip_union (a := 1 / 2) (by norm_num)
  have hgcover := hg.image_strip_union (a := 1 / 2) (by norm_num)
  change f '' Q₀ ∪ f '' Q₁ = S at hfcover
  change g '' Q₀ ∪ g '' Q₁ = T at hgcover
  rw [hfcover, hgcover] at hH
  refine ⟨H, hH, ?_⟩
  intro x hx
  by_cases hxhalf : x.2 ≤ 1 / 2
  · have hx₀ : x ∈ Q₀ := ⟨hx.1, hx.2.1, hxhalf⟩
    exact (hHu ⟨x, hx₀, rfl⟩).trans (congrArg g (hf₀.bijOn.invOn_invFunOn.1 hx₀))
  · have hx₁ : x ∈ Q₁ := ⟨hx.1, (le_of_not_ge hxhalf), hx.2.2⟩
    exact (hHv ⟨x, hx₁, rfl⟩).trans (congrArg g (hf₁.bijOn.invOn_invFunOn.1 hx₁))

end DifferentialGeometry.Topology.PiecewiseLinear

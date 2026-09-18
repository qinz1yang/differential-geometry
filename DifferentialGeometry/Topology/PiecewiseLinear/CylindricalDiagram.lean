import DifferentialGeometry.Topology.PiecewiseLinear.PrismDiskPair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure IsCylindricalDiagram (f : E × ℝ → F) (P : Set E) (S : Set F) : Prop where
  isPiecewiseAffineOn : IsPiecewiseAffineOn f (P ×ˢ Icc 0 1)
  image_eq : f '' (P ×ˢ Icc 0 1) = S
  image_top_eq_bottom : f '' (P ×ˢ {1}) = f '' (P ×ˢ {0})
  eq_or_endpoints : ∀ x ∈ P ×ˢ Icc 0 1, ∀ y ∈ P ×ˢ Icc 0 1, f x = f y →
    x = y ∨ (x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0)

open Classical in
theorem isCylindricalDiagram_piecewise [FiniteDimensional ℝ E]
    {P : Set E} (hP : IsPolyhedron P) {A B D₀ D₁ : Set F} {f g : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc 0 (1 / 2)) A)
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc (1 / 2) 1) B)
    (hf₀ : f '' (P ×ˢ {0}) = D₀) (hg₁ : g '' (P ×ˢ {1}) = D₀)
    (hfm : f '' (P ×ˢ {1 / 2}) = D₁)
    (hfg : EqOn f g (P ×ˢ {1 / 2})) (hinter : A ∩ B = D₀ ∪ D₁) :
    IsCylindricalDiagram ((P ×ˢ Icc 0 (1 / 2)).piecewise f g) P (A ∪ B) := by
  classical
  let Q₀ := P ×ˢ Icc (0 : ℝ) (1 / 2)
  let Q₁ := P ×ˢ Icc (1 / 2 : ℝ) 1
  let φ := Q₀.piecewise f g
  have hcover : Q₀ ∪ Q₁ = P ×ˢ Icc 0 1 := by
    ext x
    simp only [Q₀, Q₁, mem_union, mem_prod, mem_Icc]
    constructor
    · rintro (⟨hx, h0, hm⟩ | ⟨hx, hm, h1⟩)
      · exact ⟨hx, h0, by linarith⟩
      · exact ⟨hx, by linarith, h1⟩
    · rintro ⟨hx, h0, h1⟩
      by_cases hm : x.2 ≤ 1 / 2
      · exact Or.inl ⟨hx, h0, hm⟩
      · exact Or.inr ⟨hx, by linarith, h1⟩
  have hφf : EqOn φ f Q₀ := Q₀.piecewise_eqOn f g
  have hφg : EqOn φ g Q₁ := by
    intro x hx
    by_cases hx₀ : x ∈ Q₀
    · exact (hφf hx₀).trans (hfg ⟨hx.1, le_antisymm hx₀.2.2 hx.2.1⟩)
    · exact Q₀.piecewise_eq_of_notMem f g hx₀
  have hzero : P ×ˢ {0} ⊆ Q₀ := fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, by norm_num⟩⟩
  have hone : P ×ˢ {1} ⊆ Q₁ := fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩
  have hmid₀ : P ×ˢ {1 / 2} ⊆ Q₀ := fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩
  have hmid₁ : P ×ˢ {1 / 2} ⊆ Q₁ := fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, by norm_num⟩⟩
  have hcross {x y : E × ℝ} (hx : x ∈ Q₀) (hy : y ∈ Q₁) (hxy : f x = g y) :
      x = y ∨ (x.2 = 0 ∧ y.2 = 1) := by
    have hxI : f x ∈ D₀ ∪ D₁ := hinter ▸ ⟨hf.bijOn.mapsTo hx, hxy.symm ▸ hg.bijOn.mapsTo hy⟩
    rcases hxI with hxD | hxD
    · obtain ⟨u, hu, huf⟩ := hf₀.symm ▸ hxD
      obtain ⟨v, hv, hvg⟩ := hg₁.symm ▸ hxD
      have hux := hf.bijOn.injOn (hzero hu) hx huf
      have hvy := hg.bijOn.injOn (hone hv) hy (hvg.trans hxy)
      exact Or.inr ⟨(congrArg Prod.snd hux).symm.trans hu.2,
        (congrArg Prod.snd hvy).symm.trans hv.2⟩
    · obtain ⟨z, hz, hzf⟩ := hfm.symm ▸ hxD
      have hzx := hf.bijOn.injOn (hmid₀ hz) hx hzf
      have hzy := hg.bijOn.injOn (hmid₁ hz) hy ((hfg hz).symm.trans (hzf.trans hxy))
      exact Or.inl (hzx.symm.trans hzy)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcover]
    exact (hf.isPiecewiseAffineOn.congr hφf).union_of_isClosed
      (hg.isPiecewiseAffineOn.congr hφg) (hP.isClosed.prod isClosed_Icc) (hP.isClosed.prod isClosed_Icc)
  · rw [← hcover, image_union, hφf.image_eq, hφg.image_eq, hf.image_eq, hg.image_eq]
  · exact ((hφg.mono hone).image_eq.trans hg₁).trans ((hφf.mono hzero).image_eq.trans hf₀).symm
  · intro x hx y hy hxy
    change φ x = φ y at hxy
    rw [← hcover] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hφf hx, hφf hy] at hxy
      exact Or.inl (hf.bijOn.injOn hx hy hxy)
    · rw [hφf hx, hφg hy] at hxy
      exact (hcross hx hy hxy).imp_right Or.inl
    · rw [hφg hx, hφf hy] at hxy
      rcases hcross hy hx hxy.symm with heq | hend
      · exact Or.inl heq.symm
      · exact Or.inr (Or.inr ⟨hend.2, hend.1⟩)
    · rw [hφg hx, hφg hy] at hxy
      exact Or.inl (hg.bijOn.injOn hx hy hxy)

open Classical in
theorem exists_cylindricalDiagram_of_ball_pair
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {P : Set E} (hP : IsPLBall 2 P)
    (K L : Geometry.SimplicialComplex ℝ F) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 3 K.space) (hL : IsPLBall 3 L.space)
    {D₀ D₁ : Set F} (hD₁ : IsPLBall 2 D₁) (hdis : Disjoint D₀ D₁)
    (hD₀K : D₀ ⊆ (boundaryComplex 3 K).space) (hD₁K : D₁ ⊆ (boundaryComplex 3 K).space)
    (hD₀L : D₀ ⊆ (boundaryComplex 3 L).space) (hD₁L : D₁ ⊆ (boundaryComplex 3 L).space)
    (hinter : K.space ∩ L.space = D₀ ∪ D₁)
    {g₀ : E → F} (hg₀ : IsPLHomeomorphOn g₀ P D₀) :
    ∃ φ : E × ℝ → F, IsCylindricalDiagram φ P (K.space ∪ L.space) ∧
      ∀ x ∈ P, φ (x, 0) = g₀ x := by
  let _ : DecidableEq F := Classical.decEq _
  obtain ⟨f, hf, hf₀, hfm⟩ := exists_isPLHomeomorphOn_prism_map_ends hP
    (by norm_num : (0 : ℝ) < 1 / 2) K hK hD₀K hD₁ hD₁K hdis hg₀
  have hmidpoly : IsPolyhedron (P ×ˢ {(1 / 2 : ℝ)}) :=
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2))).isPolyhedron
  have hfmid : IsPLHomeomorphOn f (P ×ˢ {1 / 2}) D₁ := by
    have h := hf.restrict hmidpoly (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩)
    rwa [hfm] at h
  let g₁ : E → F := fun x => f (x, 1 / 2)
  have hg₁ : IsPLHomeomorphOn g₁ P D₁ :=
    (hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2)).trans hfmid
  obtain ⟨g, hg, hgm, hg₁⟩ := exists_isPLHomeomorphOn_prism_map_ends hP
    (by norm_num : (1 / 2 : ℝ) < 1) L hL hD₁L (hP.of_isPLHomeomorphOn hg₀) hD₀L hdis.symm hg₁
  have hfzero : f '' (P ×ˢ {0}) = D₀ := by
    have heq : EqOn (f ∘ fun x : E => (x, (0 : ℝ))) g₀ P := hf₀
    rw [← (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0).image_eq, image_image]
    exact heq.image_eq.trans hg₀.image_eq
  have hfg : EqOn f g (P ×ˢ {1 / 2}) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change t = 1 / 2 at ht
    subst t
    exact (hgm x hx).symm
  refine ⟨(P ×ˢ Icc 0 (1 / 2)).piecewise f g,
    isCylindricalDiagram_piecewise hP.isPolyhedron hf hg hfzero hg₁ hfm hfg hinter, ?_⟩
  intro x hx
  rw [piecewise_eq_of_mem _ _ _ (show (x, (0 : ℝ)) ∈ P ×ˢ Icc 0 (1 / 2) from ⟨hx, by norm_num⟩)]
  exact hf₀ x hx

end DifferentialGeometry.Topology.PiecewiseLinear

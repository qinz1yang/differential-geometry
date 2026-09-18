import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E} {S : Set F} (h : IsCylindricalDiagram f P S)

include h

theorem injOn_strip {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : 0 < a ∨ b < 1) :
    InjOn f (P ×ˢ Icc a b) := by
  intro x hx y hy hxy
  rcases h.eq_or_endpoints x ⟨hx.1, ha.trans hx.2.1, hx.2.2.trans hb⟩
    y ⟨hy.1, ha.trans hy.2.1, hy.2.2.trans hb⟩ hxy with heq | hends | hends
  · exact heq
  · rcases hab with ha | hb
    · exfalso
      linarith [hx.2.1, hends.1]
    · exfalso
      linarith [hy.2.2, hends.2]
  · rcases hab with ha | hb
    · exfalso
      linarith [hy.2.1, hends.2]
    · exfalso
      linarith [hx.2.2, hends.1]

theorem isPLHomeomorphOn_strip [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (hP : IsPolyhedron P) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : 0 < a ∨ b < 1) :
    IsPLHomeomorphOn f (P ×ˢ Icc a b) (f '' (P ×ˢ Icc a b)) := by
  have hpoly := hP.prod (isHPolytope_Icc (a := a) (b := b)).isPolyhedron
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    (h.isPiecewiseAffineOn.mono_of_isPolyhedron hpoly
      (fun _ hx => ⟨hx.1, ha.trans hx.2.1, hx.2.2.trans hb⟩))
    (h.injOn_strip ha hb hab).bijOn_image

theorem image_strip_union {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    f '' (P ×ˢ Icc 0 a) ∪ f '' (P ×ˢ Icc a 1) = S := by
  rw [← image_union, ← h.image_eq]
  congr 1
  ext x
  simp only [mem_union, mem_prod, mem_Icc]
  constructor
  · rintro (⟨hx, h0, hxa⟩ | ⟨hx, hax, h1⟩)
    · exact ⟨hx, h0, hxa.trans ha.2⟩
    · exact ⟨hx, ha.1.trans hax, h1⟩
  · rintro ⟨hx, h0, h1⟩
    rcases le_total x.2 a with hxa | hax
    · exact Or.inl ⟨hx, h0, hxa⟩
    · exact Or.inr ⟨hx, hax, h1⟩

theorem image_strip_inter {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    f '' (P ×ˢ Icc 0 a) ∩ f '' (P ×ˢ Icc a 1) =
      f '' (P ×ˢ {0}) ∪ f '' (P ×ˢ {a}) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    rcases h.eq_or_endpoints x ⟨hx.1, hx.2.1, hx.2.2.trans ha.2.le⟩
      y ⟨hy.1, ha.1.le.trans hy.2.1, hy.2.2⟩ hyx.symm with hxy | hends | hends
    · have hxya : x.2 = a := le_antisymm hx.2.2 (hxy.symm ▸ hy.2.1)
      exact Or.inr ⟨x, ⟨hx.1, hxya⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨hx.1, hends.1⟩, rfl⟩
    · exfalso
      linarith [hx.2.2, hends.1, ha.2]
  · intro z hz
    rcases hz with hz | ⟨x, hx, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨⟨x, ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, ha.1.le⟩⟩, rfl⟩, ?_⟩
      have htop : f x ∈ f '' (P ×ˢ {1}) := h.image_top_eq_bottom.symm ▸ ⟨x, hx, rfl⟩
      have hsub : P ×ˢ {(1 : ℝ)} ⊆ P ×ˢ Icc a 1 :=
        fun _ hy => ⟨hy.1, hy.2.symm ▸ ⟨ha.2.le, le_rfl⟩⟩
      exact image_mono hsub htop
    · exact ⟨⟨x, ⟨hx.1, hx.2.symm ▸ ⟨ha.1.le, le_rfl⟩⟩, rfl⟩,
        ⟨x, ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, ha.2.le⟩⟩, rfl⟩⟩

theorem disjoint_image_bottom_slice {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Disjoint (f '' (P ×ˢ {0})) (f '' (P ×ˢ {a})) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxy := h.injOn_strip (a := 0) (b := a) le_rfl ha.2.le (Or.inr ha.2)
    ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, ha.1.le⟩⟩
    ⟨hy.1, hy.2.symm ▸ ⟨ha.1.le, le_rfl⟩⟩ hyx.symm
  have hs := congrArg Prod.snd hxy
  exact ha.1.ne (hx.2.symm.trans (hs.trans hy.2))

end IsCylindricalDiagram

open Classical in
private theorem image_prism_ends_subset_boundaryComplex
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {P : Set E} (hP : IsPLBall 2 P) {a b : ℝ} (hab : a < b)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces]
    {f : E × ℝ → F} (hf : IsPLHomeomorphOn f (P ×ˢ Icc a b) K.space) :
    f '' (P ×ˢ {a}) ⊆ (boundaryComplex 3 K).space ∧
      f '' (P ×ˢ {b}) ⊆ (boundaryComplex 3 K).space := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨Q, hQfin, hQspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 2 Q.space := hQspace.symm ▸ hP
  have hprod := isPLBall_three_prod hP (isPLBall_Icc hab)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  have hbd := boundaryComplex_space_prism Q hQ hab R (hQspace.symm ▸ hRspace)
  rw [hQspace] at hbd
  have hfR : IsPLHomeomorphOn f R.space K.space := hRspace.symm ▸ hf
  rw [boundaryComplex_space_of_isPLHomeomorphOn R K hR.isCombinatorialManifoldWithBoundary hfR, hbd]
  exact ⟨image_mono (fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩),
    image_mono (fun _ hx => Or.inl ⟨hx.1, Or.inr hx.2⟩)⟩

open Classical in
theorem IsCylindricalDiagram.exists_ball_pair_with_boundary
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (h : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ A B : Geometry.SimplicialComplex ℝ F,
      A.faces.Finite ∧ B.faces.Finite ∧ IsPLBall 3 A.space ∧ IsPLBall 3 B.space ∧
      A.space = f '' (P ×ˢ Icc 0 a) ∧ B.space = f '' (P ×ˢ Icc a 1) ∧
      A.space ∪ B.space = S ∧
      A.space ∩ B.space = f '' (P ×ˢ {0}) ∪ f '' (P ×ˢ {a}) ∧
      IsPLBall 2 (f '' (P ×ˢ {0})) ∧ IsPLBall 2 (f '' (P ×ˢ {a})) ∧
      Disjoint (f '' (P ×ˢ {0})) (f '' (P ×ˢ {a})) ∧
      f '' (P ×ˢ {0}) ⊆ (boundaryComplex 3 A).space ∧
      f '' (P ×ˢ {a}) ⊆ (boundaryComplex 3 A).space ∧
      f '' (P ×ˢ {0}) ⊆ (boundaryComplex 3 B).space ∧
      f '' (P ×ˢ {a}) ⊆ (boundaryComplex 3 B).space := by
  let _ : DecidableEq F := Classical.decEq _
  have hf := h.isPLHomeomorphOn_strip hP.isPolyhedron le_rfl ha.2.le (Or.inr ha.2)
  have hg := h.isPLHomeomorphOn_strip hP.isPolyhedron ha.1.le le_rfl (Or.inl ha.1)
  have hA := (isPLBall_three_prod hP (isPLBall_Icc ha.1)).of_isPLHomeomorphOn hf
  have hB := (isPLBall_three_prod hP (isPLBall_Icc ha.2)).of_isPLHomeomorphOn hg
  obtain ⟨A, hAfin, hAsp⟩ := hA.isPolyhedron.exists_simplicialComplex
  obtain ⟨B, hBfin, hBsp⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hPA := image_prism_ends_subset_boundaryComplex hP ha.1 A (hAsp.symm ▸ hf)
  have hPB := image_prism_ends_subset_boundaryComplex hP ha.2 B (hBsp.symm ▸ hg)
  rw [h.image_top_eq_bottom] at hPB
  have hslice (t : ℝ) (ht : t ∈ Icc (0 : ℝ) a) : IsPLBall 2 (f '' (P ×ˢ {t})) := by
    have hPt := hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const t)
    exact hPt.of_isPLHomeomorphOn (hf.restrict hPt.isPolyhedron
      (fun _ hx => ⟨hx.1, hx.2.symm ▸ ht⟩))
  refine ⟨A, B, hAfin, hBfin, hAsp.symm ▸ hA, hBsp.symm ▸ hB, hAsp, hBsp, ?_, ?_,
    hslice 0 ⟨le_rfl, ha.1.le⟩, hslice a ⟨ha.1.le, le_rfl⟩,
    h.disjoint_image_bottom_slice ha, hPA.1, hPA.2, hPB.2, hPB.1⟩
  · rw [hAsp, hBsp]
    exact h.image_strip_union ⟨ha.1.le, ha.2.le⟩
  · rw [hAsp, hBsp]
    exact h.image_strip_inter ha

open Classical in
theorem exists_cylindricalDiagram_iff_ball_pair
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {P : Set E} (hP : IsPLBall 2 P) {S : Set F} :
    (∃ f : E × ℝ → F, IsCylindricalDiagram f P S) ↔
      ∃ (A B : Geometry.SimplicialComplex ℝ F) (D₀ D₁ : Set F),
        A.faces.Finite ∧ B.faces.Finite ∧ IsPLBall 3 A.space ∧ IsPLBall 3 B.space ∧
        IsPLBall 2 D₀ ∧ IsPLBall 2 D₁ ∧ Disjoint D₀ D₁ ∧
        A.space ∪ B.space = S ∧ A.space ∩ B.space = D₀ ∪ D₁ ∧
        D₀ ⊆ (boundaryComplex 3 A).space ∧ D₁ ⊆ (boundaryComplex 3 A).space ∧
        D₀ ⊆ (boundaryComplex 3 B).space ∧ D₁ ⊆ (boundaryComplex 3 B).space := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨A, B, hAfin, hBfin, hA, hB, _, _, hcover, hinter, hD₀, hD₁,
      hdis, hD₀A, hD₁A, hD₀B, hD₁B⟩ :=
      hf.exists_ball_pair_with_boundary hP (a := 1 / 2) (by norm_num)
    exact ⟨A, B, f '' (P ×ˢ {0}), f '' (P ×ˢ {1 / 2}), hAfin, hBfin, hA, hB,
      hD₀, hD₁, hdis, hcover, hinter, hD₀A, hD₁A, hD₀B, hD₁B⟩
  · rintro ⟨A, B, D₀, D₁, hAfin, hBfin, hA, hB, hD₀, hD₁, hdis,
      hcover, hinter, hD₀A, hD₁A, hD₀B, hD₁B⟩
    let _ : Finite A.faces := hAfin.to_subtype
    let _ : Finite B.faces := hBfin.to_subtype
    obtain ⟨p, hp⟩ := hP
    obtain ⟨d, hd⟩ := hD₀
    obtain ⟨f, hf, _⟩ := exists_cylindricalDiagram_of_ball_pair ⟨p, hp⟩ A B hA hB
      hD₁ hdis hD₀A hD₁A hD₀B hD₁B hinter (hp.symm.trans hd)
    exact ⟨f, hcover ▸ hf⟩

end DifferentialGeometry.Topology.PiecewiseLinear

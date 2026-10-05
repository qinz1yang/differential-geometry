import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerBicollar

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_signed_ribbon_chart_matching_cylindrical_core
    {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1))
    (i j : Fin 4) (hij : i ≠ j)
    {g : A × ℝ → E} {P B : Set A} {R : Set E} (hg : IsCylindricalDiagram g P R)
    (hgends : ∀ p ∈ P, g (p, 0) = g (p, 1)) {γ : ℝ → A}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P)
    (haxis : f '' section34MarkedAxis = g '' ({γ 0} ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (ρ : (Fin 3 → ℝ) × ℝ → E) (ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)
        (f '' section34MarkedRibbon j ∪ f '' section34MarkedRibbon i) ∧
      IsPLHomeomorphOn ν (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ρ (stdTriangleLoop s, 0) = g (γ 0, s)) ∧
      (∀ s, ∀ q ∈ Icc (0 : ℝ) 1,
        ν (stdTriangleLoop s) = stdTriangleLoop q →
        ∀ t ∈ Icc (0 : ℝ) 1, ρ (stdTriangleLoop s, t) =
          f (t • fourSpokeModelLeaf i, q)) ∧
      (∀ s, ∀ q ∈ Icc (0 : ℝ) 1,
        ν (stdTriangleLoop s) = stdTriangleLoop q →
        ∀ t ∈ Icc (-1 : ℝ) 0, ρ (stdTriangleLoop s, t) =
          f ((-t) • fourSpokeModelLeaf j, q)) ∧
      (∀ Q ⊆ Icc (0 : ℝ) 1, ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
        f '' (((fun t : ℝ => t • fourSpokeModelLeaf i) '' Q) ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ Q ⊆ Icc (-1 : ℝ) 0, ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
        f '' (((fun t : ℝ => (-t) • fourSpokeModelLeaf j) '' Q) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨τ, hτ, hτpos, hτneg, hτposImage, hτnegImage⟩ :=
    hf.exists_signed_crossing_ribbon_chart hends i j hij
  obtain ⟨ψ, hψ, hψg, hψlevels⟩ :=
    hg.exists_annulus_chart_of_base_arc_with_levels hgends hγ hBP
  have hS := isPolyhedron_stdSimplexBoundary_two
  have hσ : IsPLHomeomorphOn (fun z => ψ (z, 0)) (stdSimplexBoundary 2)
      (f '' section34MarkedAxis) := by
    have h := (hS.isPLHomeomorphOn_prod_const (0 : ℝ)).trans
      (hψ.restrict (hS.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1)))
    rw [hψlevels {0} (by norm_num), image_singleton, ← haxis] at h
    exact h
  let r : (Fin 3 → ℝ) → E := fun z => τ (z, 0)
  have hr : IsPLHomeomorphOn r (stdSimplexBoundary 2) (f '' section34MarkedAxis) := by
    have h := (hS.isPLHomeomorphOn_prod_const (0 : ℝ)).trans
      (hτ.restrict (hS.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc (-1) 1)))
    have hzero := hτposImage {0} (by norm_num)
    simp only [image_singleton, zero_smul] at hzero
    rw [hzero] at h
    exact h
  let ν := Function.invFunOn r (stdSimplexBoundary 2) ∘ fun z => ψ (z, 0)
  have hν : IsPLHomeomorphOn ν (stdSimplexBoundary 2) (stdSimplexBoundary 2) :=
    hσ.trans hr.symm
  let ρ := τ ∘ Prod.map ν id
  have hρ := (hν.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hτ
  have hlevel (Q : Set ℝ) : ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
      τ '' (stdSimplexBoundary 2 ×ˢ Q) := by
    rw [show ρ = τ ∘ Prod.map ν id from rfl, image_comp, prodMap_image_prod,
      hν.image_eq, image_id]
  refine ⟨ρ, ν, hρ, hν, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hz := stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs)
    exact (hr.bijOn.invOn_invFunOn.2 (hσ.bijOn.mapsTo hz)).trans
      (hψg 0 (by norm_num) s hs)
  · intro s q hq heq t ht
    change τ (ν (stdTriangleLoop s), t) = _
    rw [heq]
    exact hτpos t ht q hq
  · intro s q hq heq t ht
    change τ (ν (stdTriangleLoop s), t) = _
    rw [heq]
    exact hτneg t ht q hq
  · intro Q hQ
    exact (hlevel Q).trans (hτposImage Q hQ)
  · intro Q hQ
    exact (hlevel Q).trans (hτnegImage Q hQ)

end DifferentialGeometry.Topology.PiecewiseLinear

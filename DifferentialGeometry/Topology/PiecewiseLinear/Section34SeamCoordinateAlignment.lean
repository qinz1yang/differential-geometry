import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingRibbonAnnuli

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_coherent_annulus_core_reparametrization
    {A E ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (i₀ : ι) {Q : Set A} (hQ : IsPolyhedron Q) {J : Set E} {σ : A → E}
    (hσ : IsPLHomeomorphOn σ Q J) {τ : ι → A × ℝ → E} {T : ι → Set E}
    (hτ : ∀ i, IsPLHomeomorphOn (τ i) (Q ×ˢ Icc (0 : ℝ) 1) (T i))
    (hzero : τ i₀ '' (Q ×ˢ {0}) = J)
    (hcore : ∀ i x, x ∈ Q → τ i (x, 0) = τ i₀ (x, 0)) :
    ∃ ν : A → A, IsPLHomeomorphOn ν Q Q ∧
      (∀ i, IsPLHomeomorphOn (τ i ∘ Prod.map ν id) (Q ×ˢ Icc (0 : ℝ) 1) (T i)) ∧
      (∀ i x, x ∈ Q → τ i (ν x, 0) = σ x) ∧
      ∀ i (I : Set ℝ), (τ i ∘ Prod.map ν id) '' (Q ×ˢ I) = τ i '' (Q ×ˢ I) := by
  let r : A → E := fun x => τ i₀ (x, 0)
  have hr : IsPLHomeomorphOn r Q J := by
    have h := (hQ.isPLHomeomorphOn_prod_const (0 : ℝ)).trans
      ((hτ i₀).restrict (hQ.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1)))
    rwa [hzero] at h
  let ν := Function.invFunOn r Q ∘ σ
  have hν : IsPLHomeomorphOn ν Q Q := hσ.trans hr.symm
  have hI : IsPolyhedron (Icc (0 : ℝ) 1) := isHPolytope_Icc.isPolyhedron
  have hprod := hν.prodMap hI.isPLHomeomorphOn_id
  refine ⟨ν, hν, fun i => hprod.trans (hτ i), ?_, ?_⟩
  · intro i x hx
    rw [hcore i (ν x) (hν.bijOn.mapsTo hx)]
    exact hr.bijOn.invOn_invFunOn.2 (hσ.bijOn.mapsTo hx)
  · intro i I
    rw [image_comp, prodMap_image_prod, hν.image_eq, image_id]

theorem IsCylindricalDiagram.exists_crossing_ribbon_charts_with_prescribed_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    {σ : (Fin 3 → ℝ) → E}
    (hσ : IsPLHomeomorphOn σ (stdSimplexBoundary 2) (f '' section34MarkedAxis)) :
    ∃ ρ : Fin 4 → (Fin 3 → ℝ) × ℝ → E,
      (∀ i, IsPLHomeomorphOn (ρ i) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' section34MarkedRibbon i)) ∧
      (∀ i z, z ∈ stdSimplexBoundary 2 → ρ i (z, 0) = σ z) ∧
      ∀ i r s, 0 ≤ r → s ≤ 1 →
        IsPLHomeomorphOn (ρ i) (stdSimplexBoundary 2 ×ˢ Icc r s)
          (f '' (((fun t : ℝ => t • fourSpokeModelLeaf i) '' Icc r s) ×ˢ Icc (0 : ℝ) 1)) := by
  obtain ⟨τ, hτ, -, hcore, hzero, -, hlevels⟩ :=
    hf.exists_crossing_ribbon_annulus_charts hends
  obtain ⟨ν, hν, hντ, hνcore, -⟩ := exists_coherent_annulus_core_reparametrization
    (0 : Fin 4) isPolyhedron_stdSimplexBoundary_two hσ hτ (hzero 0)
      (fun i z hz => hcore i 0 z hz)
  refine ⟨fun i => τ i ∘ Prod.map ν id, hντ, hνcore, ?_⟩
  intro i r s hr hs
  exact (hν.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans
    (hlevels i r s hr hs)

theorem IsCylindricalDiagram.exists_ribbon_charts_matching_cylindrical_core
    {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    {g : A × ℝ → E} {P B : Set A} {S : Set E} (hg : IsCylindricalDiagram g P S)
    (hgends : ∀ x ∈ P, g (x, 0) = g (x, 1)) {γ : ℝ → A}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P)
    (haxis : f '' section34MarkedAxis = g '' ({γ 0} ×ˢ Icc (0 : ℝ) 1)) :
    ∃ ρ : Fin 4 → (Fin 3 → ℝ) × ℝ → E,
      (∀ i, IsPLHomeomorphOn (ρ i) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' section34MarkedRibbon i)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → ρ i (stdTriangleLoop t, 0) = g (γ 0, t)) ∧
      ∀ i r s, 0 ≤ r → s ≤ 1 →
        IsPLHomeomorphOn (ρ i) (stdSimplexBoundary 2 ×ˢ Icc r s)
          (f '' (((fun t : ℝ => t • fourSpokeModelLeaf i) '' Icc r s) ×ˢ Icc (0 : ℝ) 1)) := by
  obtain ⟨τ, hτ, hconj, hlevels⟩ :=
    hg.exists_annulus_chart_of_base_arc_with_levels hgends hγ hBP
  have hσ : IsPLHomeomorphOn (fun z => τ (z, 0)) (stdSimplexBoundary 2)
      (f '' section34MarkedAxis) := by
    have h := (isPolyhedron_stdSimplexBoundary_two.isPLHomeomorphOn_prod_const (0 : ℝ)).trans
      (hτ.restrict (isPolyhedron_stdSimplexBoundary_two.prod
        (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1)))
    rw [hlevels {0} (by norm_num), image_singleton, ← haxis] at h
    exact h
  obtain ⟨ρ, hρ, hcore, hsmall⟩ := hf.exists_crossing_ribbon_charts_with_prescribed_core hends hσ
  refine ⟨ρ, hρ, ?_, hsmall⟩
  intro i t ht
  exact (hcore i _ (stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht))).trans
    (hconj 0 (by norm_num) t ht)

end DifferentialGeometry.Topology.PiecewiseLinear

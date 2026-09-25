import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamAnnulusExtensionMap
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamAnnulusExtensionChart

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_annulus_map_matching_rim_collars
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A W₀ W₁ : Set E} {φ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) A)
    {c d : ℝ} (hcd : c < d) {ρ₀ ρ₁ : E × ℝ → E}
    (hρ₀ : IsPLHomeomorphOn ρ₀ ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ Icc c d) W₀)
    (hρ₁ : IsPLHomeomorphOn ρ₁ ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ Icc c d) W₁)
    (hzero₀ : ∀ z ∈ φ '' (stdSimplexBoundary 2 ×ˢ {0}), ρ₀ (z, c) = z)
    (hzero₁ : ∀ z ∈ φ '' (stdSimplexBoundary 2 ×ˢ {0}), ρ₁ (z, c) = z)
    (hW₀A : W₀ ⊆ A) (hW₁A : W₁ ⊆ A)
    (hdis₀ : Disjoint W₀ (φ '' (stdSimplexBoundary 2 ×ˢ {1})))
    (hdis₁ : Disjoint W₁ (φ '' (stdSimplexBoundary 2 ×ˢ {1}))) :
    ∃ F : E → E, IsPLHomeomorphOn F A A ∧
      EqOn F id (φ '' (stdSimplexBoundary 2 ×ˢ {0})) ∧
      F '' (φ '' (stdSimplexBoundary 2 ×ˢ {1})) = φ '' (stdSimplexBoundary 2 ×ˢ {1}) ∧
      ∀ z ∈ φ '' (stdSimplexBoundary 2 ×ˢ {0}), ∀ t ∈ Icc c d,
        F (ρ₀ (z, t)) = ρ₁ (z, t) := by
  let V := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let B₀ := stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}
  let B₁ := stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}
  let τ := Function.invFunOn φ V
  have hbd : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  have hB₀ : IsPolyhedron B₀ := hbd.prod (isHPolytope_singleton _).isPolyhedron
  have hB₀V : B₀ ⊆ V := fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩
  have hB₁V : B₁ ⊆ V := fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩
  have hbase := hφ.restrict hB₀ hB₀V
  have hJpoly := hB₀.image_of_isPiecewiseAffineOn hbase.isPiecewiseAffineOn hbase.bijOn.injOn
  have hpull {W : Set E} {ρ : E × ℝ → E}
      (hρ : IsPLHomeomorphOn ρ ((φ '' B₀) ×ˢ Icc c d) W)
      (hzero : ∀ z ∈ φ '' B₀, ρ (z, c) = z) (hWA : W ⊆ A)
      (hdis : Disjoint W (φ '' B₁)) :
      IsPLHomeomorphOn (τ ∘ ρ ∘ Prod.map φ id) (B₀ ×ˢ Icc c d) (τ '' W) ∧
      (∀ z ∈ B₀, (τ ∘ ρ ∘ Prod.map φ id) (z, c) = z) ∧
      τ '' W ⊆ V ∧ Disjoint (τ '' W) B₁ := by
    have hW : IsPolyhedron W := by
      rw [← hρ.image_eq]
      exact (hJpoly.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
        hρ.isPiecewiseAffineOn hρ.bijOn.injOn
    refine ⟨((hbase.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hρ).trans
      (hφ.symm.restrict hW hWA), ?_, ?_, ?_⟩
    · intro z hz
      change τ (ρ (φ z, c)) = z
      rw [hzero (φ z) (mem_image_of_mem φ hz)]
      exact hφ.bijOn.invOn_invFunOn.1 (hB₀V hz)
    · rintro _ ⟨z, hz, rfl⟩
      exact hφ.symm.bijOn.mapsTo (hWA hz)
    · apply disjoint_left.mpr
      rintro z ⟨w, hw, hwz⟩ hz
      have hback : φ z = w := hwz ▸ hφ.bijOn.invOn_invFunOn.2 (hWA hw)
      exact disjoint_left.mp hdis hw ⟨z, hz, hback⟩
  obtain ⟨hψ₀, hψ₀zero, hψ₀V, hψ₀dis⟩ := hpull hρ₀ hzero₀ hW₀A hdis₀
  obtain ⟨hψ₁, hψ₁zero, hψ₁V, hψ₁dis⟩ := hpull hρ₁ hzero₁ hW₁A hdis₁
  have hid := (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
  obtain ⟨H, hH, hHbase, hHtop, hHmatch⟩ :=
    hid.exists_lateral_map_matching_rim_collars (by norm_num : (0 : ℝ) < 1) hcd
      (by simpa only [image_id] using hψ₀) (by simpa only [image_id] using hψ₁)
      (by simpa only [image_id] using hψ₀zero) (by simpa only [image_id] using hψ₁zero)
      (by simpa only [image_id] using hψ₀V) (by simpa only [image_id] using hψ₁V)
      (by simpa only [image_id] using hψ₀dis) (by simpa only [image_id] using hψ₁dis)
  simp only [image_id] at hH hHbase hHtop hHmatch
  refine ⟨φ ∘ H ∘ τ, (hφ.symm.trans hH).trans hφ, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change φ (H (τ (φ z))) = φ z
    rw [show τ (φ z) = z from hφ.bijOn.invOn_invFunOn.1 (hB₀V hz), hHbase hz]
    rfl
  · have hback : τ '' (φ '' B₁) = B₁ := by
      rw [image_image]
      exact (image_congr fun z hz => hφ.bijOn.invOn_invFunOn.1 (hB₁V hz)).trans (image_id _)
    change (φ ∘ H ∘ τ) '' (φ '' B₁) = φ '' B₁
    rw [image_comp, image_comp, hback, hHtop]
  · rintro _ ⟨z, hz, rfl⟩ t ht
    change φ (H (τ (ρ₀ (φ z, t)))) = ρ₁ (φ z, t)
    have hm := hHmatch z hz t ht
    change H (τ (ρ₀ (φ z, t))) = τ (ρ₁ (φ z, t)) at hm
    rw [hm]
    exact hφ.bijOn.invOn_invFunOn.2 (hW₁A (hρ₁.bijOn.mapsTo
      ⟨mem_image_of_mem φ hz, ht⟩))

end DifferentialGeometry.Topology.PiecewiseLinear

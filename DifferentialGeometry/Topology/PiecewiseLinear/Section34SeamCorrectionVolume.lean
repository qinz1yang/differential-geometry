import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamVolumeExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_volume_extension_preserving_annulus_rims
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1))
    {u : E → E}
    (hu : IsPLHomeomorphOn u (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1))
      (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)))
    (hurim : ∀ r ∈ ({0, 1} : Set ℝ), u '' (f '' ({(r, 0)} ×ˢ Icc (0 : ℝ) 1)) =
      f '' ({(r, 0)} ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E) (H : E → E)
      (ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ) (ν : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      IsPLHomeomorphOn σ ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        σ ((stdTriangleLoop t, a), b) = f ((a, b), t)) ∧
      IsPLHomeomorphOn H R R ∧
      IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn H u (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        H (σ (z, v)) = σ (ψ z, v)) ∧
      ∀ r ∈ ({0, 1} : Set ℝ), IsPLHomeomorphOn (ν r) (stdSimplexBoundary 2)
        (stdSimplexBoundary 2) ∧
        (∀ z ∈ stdSimplexBoundary 2, ψ (z, r) = (ν r z, r)) ∧
        ∀ z ∈ stdSimplexBoundary 2, ∀ v ∈ Icc (0 : ℝ) 1,
          H (σ ((z, r), v)) = σ ((ν r z, r), v) := by
  have hI : IsPolyhedron (Icc (0 : ℝ) 1) := isHPolytope_Icc.isPolyhedron
  have hS : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  obtain ⟨ρ, hρ, hρf, hρlevels⟩ := hf.exists_annulus_chart_of_base_arc_with_levels hends
    (hI.isPLHomeomorphOn_prod_const (0 : ℝ))
    (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1))
  let A := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let ψ := Function.invFunOn ρ A ∘ u ∘ ρ
  have hψ : IsPLHomeomorphOn ψ A A := (hρ.trans hu).trans hρ.symm
  have hψrim (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ)) :
      ψ '' (stdSimplexBoundary 2 ×ˢ {r}) = stdSimplexBoundary 2 ×ˢ {r} := by
    have hrI : r ∈ Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
    have hlevel : ρ '' (stdSimplexBoundary 2 ×ˢ {r}) =
        f '' ({(r, 0)} ×ˢ Icc (0 : ℝ) 1) := by
      simpa only [image_singleton] using hρlevels {r} (singleton_subset_iff.mpr hrI)
    change (Function.invFunOn ρ A ∘ (u ∘ ρ)) '' _ = _
    rw [image_comp, image_comp, hlevel, hurim r hr, ← hlevel, ← image_comp]
    have heq : EqOn (Function.invFunOn ρ A ∘ ρ) id
        (stdSimplexBoundary 2 ×ˢ {r}) := by
      intro z hz
      exact hρ.bijOn.invOn_invFunOn.1 ⟨hz.1, hz.2.symm ▸ hrI⟩
    exact heq.image_eq.trans (image_id _)
  let ν := fun r z => (ψ (z, r)).1
  have hν (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ)) :
      IsPLHomeomorphOn (ν r) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
        ∀ z ∈ stdSimplexBoundary 2, ψ (z, r) = (ν r z, r) := by
    have hrI : r ∈ Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
    have hrim := hψ.restrict (hS.prod (isHPolytope_singleton r).isPolyhedron)
      (prod_mono_right (singleton_subset_iff.mpr hrI))
    rw [hψrim r hr] at hrim
    refine ⟨((hS.isPLHomeomorphOn_prod_const r).trans hrim).trans
      (hS.isPLHomeomorphOn_fst_prod_const r), ?_⟩
    intro z hz
    have hm : ψ (z, r) ∈ stdSimplexBoundary 2 ×ˢ {r} :=
      hrim.bijOn.mapsTo (show (z, r) ∈ stdSimplexBoundary 2 ×ˢ {r} from ⟨hz, rfl⟩)
    exact Prod.ext rfl hm.2
  obtain ⟨σ, H, hσ, hσf, hH, hconj⟩ := hf.exists_product_extension_of_annulus_map hends hψ
  have hσρ (z : (Fin 3 → ℝ) × ℝ) (hz : z ∈ A) : σ (z, 0) = ρ z := by
    obtain ⟨t, ht, heq⟩ := stdTriangleLoop_image.symm.subset hz.1
    have hz' : z = (stdTriangleLoop t, z.2) := Prod.ext heq.symm rfl
    rw [hz', hσf z.2 hz.2 0 (by norm_num) t ht, hρf z.2 hz.2 t ht]
  refine ⟨σ, H, ψ, ν, hσ, hσf, hH, hψ, ?_, hconj, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hρ.bijOn.surjOn hy
    rw [← hσρ z hz, hconj z hz 0 (by norm_num),
      hσρ (ψ z) (hψ.bijOn.mapsTo hz), hσρ z hz]
    exact hρ.bijOn.invOn_invFunOn.2 (hu.bijOn.mapsTo (hρ.bijOn.mapsTo hz))
  · intro r hr
    refine ⟨(hν r hr).1, (hν r hr).2, ?_⟩
    intro z hz v hv
    have hrI : r ∈ Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
    rw [hconj (z, r) ⟨hz, hrI⟩ v hv, (hν r hr).2 z hz]

end DifferentialGeometry.Topology.PiecewiseLinear

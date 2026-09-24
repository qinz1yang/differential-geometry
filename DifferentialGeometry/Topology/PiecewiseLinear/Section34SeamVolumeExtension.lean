import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingRibbonAnnuli

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_square_circle_product_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1)) :
    ∃ σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E,
      IsPLHomeomorphOn σ ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) R ∧
      ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        σ ((stdTriangleLoop t, u), v) = f ((u, v), t) := by
  have hI : IsPolyhedron (Icc (0 : ℝ) 1) := isHPolytope_Icc.isPolyhedron
  have hloop : ∀ x ∈ Icc (0 : ℝ) 1,
      (stdTriangleLoop 0, x) = (stdTriangleLoop 1, x) := by
    intro x _
    exact Prod.ext (by norm_num [stdTriangleLoop]) rfl
  have hm := isCylindricalDiagram_stdTriangleLoop.prod_collaring_interval hI hloop 0 1
  obtain ⟨σ, hσ, hconj⟩ := exists_isPLHomeomorphOn_of_eq_endMap (hI.prod hI) hm hf
    (hI.prod hI).isPLHomeomorphOn_id
    (fun p hp => Prod.ext (hloop p.1 hp.1) rfl) hends
  exact ⟨σ, hσ, fun u hu v hv t ht => hconj ((u, v), t) ⟨⟨hu, hv⟩, ht⟩⟩

theorem IsCylindricalDiagram.exists_product_extension_of_annulus_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1))
    {φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E) (H : E → E),
      IsPLHomeomorphOn σ ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        σ ((stdTriangleLoop t, u), v) = f ((u, v), t)) ∧
      IsPLHomeomorphOn H R R ∧
      ∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        H (σ (z, v)) = σ (φ z, v) := by
  obtain ⟨σ, hσ, hσf⟩ := hf.exists_square_circle_product_chart hends
  let V := (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1
  let H := σ ∘ Prod.map φ id ∘ Function.invFunOn σ V
  have hI : IsPolyhedron (Icc (0 : ℝ) 1) := isHPolytope_Icc.isPolyhedron
  have hp := hφ.prodMap hI.isPLHomeomorphOn_id
  refine ⟨σ, H, hσ, hσf, (hσ.symm.trans hp).trans hσ, ?_⟩
  intro z hz v hv
  change σ (Prod.map φ id (Function.invFunOn σ V (σ (z, v)))) = _
  rw [hσ.bijOn.invOn_invFunOn.1 ⟨hz, hv⟩]
  rfl

theorem IsCylindricalDiagram.exists_volume_extension_of_compensated_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1))
    {φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hφzero : ∀ z ∈ stdSimplexBoundary 2, φ (z, 0) = (z, 0))
    (hφone : ∀ z ∈ stdSimplexBoundary 2, φ (z, 1) = (z, 1)) :
    ∃ (σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E) (H : E → E),
      IsPLHomeomorphOn σ ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        σ ((stdTriangleLoop t, u), v) = f ((u, v), t)) ∧
      IsPLHomeomorphOn H R R ∧
      (∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        H (σ (z, v)) = σ (φ z, v)) ∧
      EqOn H id (f '' ((({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ v ∈ Icc (0 : ℝ) 1,
        H '' (f '' ((Icc (0 : ℝ) 1 ×ˢ {v}) ×ˢ Icc (0 : ℝ) 1)) =
          f '' ((Icc (0 : ℝ) 1 ×ˢ {v}) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨σ, H, hσ, hσf, hH, hconj⟩ := hf.exists_product_extension_of_annulus_map hends hφ
  refine ⟨σ, H, hσ, hσf, hH, hconj, ?_, ?_⟩
  · rintro _ ⟨⟨⟨u, v⟩, t⟩, ⟨⟨hu, hv⟩, ht⟩, rfl⟩
    have hz := stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht)
    rcases hu with rfl | rfl
    · rw [← hσf 0 (by norm_num) v hv t ht,
        hconj (stdTriangleLoop t, 0) ⟨hz, by norm_num⟩ v hv, hφzero _ hz]
      rfl
    · rw [← hσf 1 (by norm_num) v hv t ht,
        hconj (stdTriangleLoop t, 1) ⟨hz, by norm_num⟩ v hv, hφone _ hz]
      rfl
  · intro v hv
    have heq : σ '' ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ {v}) =
        f '' ((Icc (0 : ℝ) 1 ×ˢ {v}) ×ˢ Icc (0 : ℝ) 1) := by
      ext y
      constructor
      · rintro ⟨⟨⟨z, u⟩, w⟩, ⟨⟨hz, hu⟩, hw⟩, rfl⟩
        have hwv : w = v := hw
        subst w
        obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
        exact ⟨((u, v), t), ⟨⟨hu, rfl⟩, ht⟩, (hσf u hu v hv t ht).symm⟩
      · rintro ⟨⟨⟨u, w⟩, t⟩, ⟨⟨hu, hw⟩, ht⟩, rfl⟩
        have hwv : w = v := hw
        subst w
        exact ⟨((stdTriangleLoop t, u), v),
          ⟨⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht), hu⟩, rfl⟩,
          hσf u hu v hv t ht⟩
    rw [← heq, ← image_comp]
    have hEq : EqOn (H ∘ σ) (σ ∘ Prod.map φ id)
        ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ {v}) := by
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      have hwv : w = v := hw
      subst w
      exact hconj z hz v hv
    rw [hEq.image_eq, image_comp, prodMap_image_prod, hφ.image_eq, image_id]

theorem IsCylindricalDiagram.exists_volume_extension_of_boundary_annulus_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1))
    {u : E → E}
    (hu : IsPLHomeomorphOn u (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1))
      (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)))
    (hufix : EqOn u id (f '' ((({0, 1} : Set ℝ) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1))) :
    ∃ H : E → E, IsPLHomeomorphOn H R R ∧
      EqOn H u (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∧
      EqOn H id (f '' ((({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ v ∈ Icc (0 : ℝ) 1,
        H '' (f '' ((Icc (0 : ℝ) 1 ×ˢ {v}) ×ˢ Icc (0 : ℝ) 1)) =
          f '' ((Icc (0 : ℝ) 1 ×ˢ {v}) ×ˢ Icc (0 : ℝ) 1) := by
  have hI : IsPolyhedron (Icc (0 : ℝ) 1) := isHPolytope_Icc.isPolyhedron
  obtain ⟨ρ, hρ, hρf, -⟩ := hf.exists_annulus_chart_of_base_arc_with_levels hends
    (hI.isPLHomeomorphOn_prod_const (0 : ℝ))
    (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1))
  let A := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let φ := Function.invFunOn ρ A ∘ u ∘ ρ
  have hφ : IsPLHomeomorphOn φ A A := (hρ.trans hu).trans hρ.symm
  have hendsφ (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ))
      (z) (hz : z ∈ stdSimplexBoundary 2) : φ (z, r) = (z, r) := by
    have hrI : r ∈ Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
    have hfix : u (ρ (z, r)) = ρ (z, r) := by
      obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
      rw [hρf r hrI t ht]
      exact hufix ⟨((r, 0), t), ⟨⟨hr, rfl⟩, ht⟩, rfl⟩
    change Function.invFunOn ρ A (u (ρ (z, r))) = _
    rw [hfix]
    exact hρ.bijOn.invOn_invFunOn.1 ⟨hz, hrI⟩
  obtain ⟨σ, H, -, hσf, hH, hHσ, hfix, hlevels⟩ :=
    hf.exists_volume_extension_of_compensated_annulus hends hφ
      (hendsφ 0 (by simp)) (hendsφ 1 (by simp))
  have hσρ (z : (Fin 3 → ℝ) × ℝ) (hz : z ∈ A) : σ (z, 0) = ρ z := by
    obtain ⟨t, ht, heq⟩ := stdTriangleLoop_image.symm.subset hz.1
    have hz' : z = (stdTriangleLoop t, z.2) := Prod.ext heq.symm rfl
    rw [hz', hσf z.2 hz.2 0 (by norm_num) t ht, hρf z.2 hz.2 t ht]
  refine ⟨H, hH, ?_, hfix, hlevels⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hρ.bijOn.surjOn hy
  rw [← hσρ z hz, hHσ z hz 0 (by norm_num), hσρ (φ z) (hφ.bijOn.mapsTo hz)]
  rw [hσρ z hz]
  exact hρ.bijOn.invOn_invFunOn.2 (hu.bijOn.mapsTo (hρ.bijOn.mapsTo hz))

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionVolume

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_square_annulus_seam_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1)) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)
        (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        φ (stdTriangleLoop s, t) = f ((t / 2 + 1 / 2, 0), s)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0) =
        f '' ((Icc (0 : ℝ) (1 / 2) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        f '' ((Icc (1 / 2 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,
        φ '' (stdSimplexBoundary 2 ×ˢ {t}) =
          f '' ({(t / 2 + 1 / 2, 0)} ×ˢ Icc (0 : ℝ) 1) := by
  have hI : IsPolyhedron (Icc (0 : ℝ) 1) := isHPolytope_Icc.isPolyhedron
  have hS : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  obtain ⟨ρ, hρ, hρf, hρlevels⟩ := hf.exists_annulus_chart_of_base_arc_with_levels hends
    (hI.isPLHomeomorphOn_prod_const (0 : ℝ))
    (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1))
  let η : ℝ → ℝ := fun t => t / 2 + 1 / 2
  have hη {a b c d : ℝ} (ha : a / 2 + 1 / 2 = c) (hb : b / 2 + 1 / 2 = d) :
      IsPLHomeomorphOn η (Icc a b) (Icc c d) := by
    simpa only [η, div_eq_mul_inv, mul_comm, one_mul] using
      isPLHomeomorphOn_mul_add_Icc (by norm_num : (0 : ℝ) < 1 / 2)
        (show (1 / 2 : ℝ) * a + 1 / 2 = c by linarith)
        (show (1 / 2 : ℝ) * b + 1 / 2 = d by linarith)
  have hηfull := hη (by norm_num : (-1 : ℝ) / 2 + 1 / 2 = 0)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  let φ := ρ ∘ Prod.map id η
  have hφ := (hS.isPLHomeomorphOn_id.prodMap hηfull).trans hρ
  have hlevel (I : Set ℝ) (hI' : I ⊆ Icc (-1 : ℝ) 1) :
      φ '' (stdSimplexBoundary 2 ×ˢ I) =
        f '' (((fun t => (η t, (0 : ℝ))) '' I) ×ˢ Icc (0 : ℝ) 1) := by
    change (ρ ∘ Prod.map id η) '' _ = _
    rw [image_comp, prodMap_image_prod, image_id,
      hρlevels (η '' I) ((image_mono hI').trans hηfull.image_eq.subset), image_image]
  refine ⟨φ, hφ, ?_, ?_, ?_, ?_⟩
  · intro t ht s hs
    exact hρf (η t) (hηfull.bijOn.mapsTo ht) s hs
  · rw [hlevel _ (Icc_subset_Icc le_rfl (by norm_num))]
    have hn := hη (by norm_num : (-1 : ℝ) / 2 + 1 / 2 = 0)
      (by norm_num : (0 : ℝ) / 2 + 1 / 2 = 1 / 2)
    rw [show (fun t => (η t, (0 : ℝ))) = (fun t => (t, (0 : ℝ))) ∘ η from rfl,
      image_comp, hn.image_eq, ← prod_singleton]
  · rw [hlevel _ (Icc_subset_Icc (by norm_num) le_rfl)]
    have hp := hη (by norm_num : (0 : ℝ) / 2 + 1 / 2 = 1 / 2)
      (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
    rw [show (fun t => (η t, (0 : ℝ))) = (fun t => (t, (0 : ℝ))) ∘ η from rfl,
      image_comp, hp.image_eq, ← prod_singleton]
  · intro t ht
    rw [hlevel {t} (singleton_subset_iff.mpr ht), image_singleton]

end DifferentialGeometry.Topology.PiecewiseLinear

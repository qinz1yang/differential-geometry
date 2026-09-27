import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionCharts
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionShortening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_seam_volume_correction_of_surface_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R P N W : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1))
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hAL : f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) ⊆ L.space)
    {d : ℝ} (hd : 0 < d) {ρ : (Fin 3 → ℝ) × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (-d) d) W)
    (hWL : W ⊆ L.space)
    (hzero : ∀ s ∈ Icc (0 : ℝ) 1, ρ (stdTriangleLoop s, 0) = f ((1 / 2, 0), s))
    (hpos : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d) ⊆ P)
    (hneg : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (-d) 0) ⊆ N)
    (hAP : (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∩ P =
      f '' ((Icc (1 / 2 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1))
    (hAN : (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∩ N =
      f '' ((Icc (0 : ℝ) (1 / 2) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (e : ℝ) (H : E → E) (σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E)
      (ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ) (ν : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      0 < e ∧ e ≤ d ∧ e ≤ 1 ∧ IsPLHomeomorphOn H R R ∧
      IsPLHomeomorphOn σ ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        σ ((stdTriangleLoop t, a), b) = f ((a, b), t)) ∧
      IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        H (σ (z, v)) = σ (ψ z, v)) ∧
      (H '' (f '' ((Icc (0 : ℝ) (1 / 2) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) =
        f '' ((Icc (0 : ℝ) (1 / 2) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∧
      (H '' (f '' ((Icc (1 / 2 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) =
        f '' ((Icc (1 / 2 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ t ∈ Icc (-e) e, ∀ s ∈ Icc (0 : ℝ) 1,
        H (f ((t / 2 + 1 / 2, 0), s)) = ρ (stdTriangleLoop s, t)) ∧
      ∀ r ∈ ({0, 1} : Set ℝ), IsPLHomeomorphOn (ν r) (stdSimplexBoundary 2)
        (stdSimplexBoundary 2) ∧
        (∀ z ∈ stdSimplexBoundary 2, ψ (z, r) = (ν r z, r)) ∧
        ∀ z ∈ stdSimplexBoundary 2, ∀ v ∈ Icc (0 : ℝ) 1,
          H (σ ((z, r), v)) = σ ((ν r z, r), v) := by
  obtain ⟨φ, hφ, hφf, hφneg, hφpos, hφlevel⟩ :=
    hf.exists_square_annulus_seam_chart hends
  have hcore (z) (hz : z ∈ stdSimplexBoundary 2) : ρ (z, 0) = φ (z, 0) := by
    obtain ⟨s, hs, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    have hh := hφf 0 (by norm_num) s hs
    norm_num at hh
    exact (hzero s hs).trans hh.symm
  obtain ⟨e, F, he, hed, he1, hF, -, hFrim, hFN, hFP, hmatch⟩ :=
    hφ.exists_bicollar_matching_from_surface_sides L hL hAL hd hρ hWL hcore hpos hneg
      (hAP.trans hφpos.symm) (hAN.trans hφneg.symm)
  have hFrim' (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ)) :
      F '' (f '' ({(r, 0)} ×ˢ Icc (0 : ℝ) 1)) =
        f '' ({(r, 0)} ×ˢ Icc (0 : ℝ) 1) := by
    rcases hr with rfl | rfl
    · have hh := hFrim (-1) (by simp)
      rw [hφlevel (-1) (by norm_num)] at hh
      norm_num at hh ⊢
      exact hh
    · have hh := hFrim 1 (by simp)
      rw [hφlevel 1 (by norm_num)] at hh
      norm_num at hh ⊢
      exact hh
  obtain ⟨σ, H, ψ, ν, hσ, hσf, hH, hψ, hHF, hconj, hν⟩ :=
    hf.exists_volume_extension_preserving_annulus_rims hends hF hFrim'
  refine ⟨e, H, σ, ψ, ν, he, hed, he1, hH, hσ, hσf, hψ, hconj, ?_, ?_, ?_, hν⟩
  · have hsub : f '' ((Icc (0 : ℝ) (1 / 2) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) ⊆
        f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) :=
      image_mono (prod_mono_left (prod_mono_left
        (Icc_subset_Icc le_rfl (by norm_num))))
    exact (hHF.mono hsub).image_eq.trans (hAN ▸ hFN)
  · have hsub : f '' ((Icc (1 / 2 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) ⊆
        f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) :=
      image_mono (prod_mono_left (prod_mono_left
        (Icc_subset_Icc (by norm_num) le_rfl)))
    exact (hHF.mono hsub).image_eq.trans (hAP ▸ hFP)
  · intro t ht s hs
    have htI : t ∈ Icc (-1 : ℝ) 1 :=
      Icc_subset_Icc (neg_le_neg he1) he1 ht
    have hloop := stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs)
    rw [← hφf t htI s hs]
    exact (hHF (hφ.bijOn.mapsTo ⟨hloop, htI⟩)).trans
      (hmatch (stdTriangleLoop s) hloop t ht)

end DifferentialGeometry.Topology.PiecewiseLinear

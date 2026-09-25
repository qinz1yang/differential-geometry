import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSideAlignment

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_marked_cell_page_alignment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S₀ S₁ X Y C N W₀ W₁ : Set E} {P : Fin 4 → Set E}
    {G : (ℝ × ℝ) × ℝ → E} (hG : IsPLHomeomorphOn G spliceCylinder C)
    (hS₀ : G '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ S₀)
    (hS₁ : G '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ S₁)
    (hFX : C ∩ S₀ = C ∩ frontier X) (hFY : C ∩ S₁ = C ∩ frontier Y)
    (hc : G (0, 1 / 2) ∈ interior C)
    (hcross : HasPLCrossingAt S₀ S₁ (G (0, 1 / 2)))
    (hball₀ : ∀ O ∈ 𝓝 (G (0, 1 / 2)),
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
          MapsTo g (Metric.ball c r) (S₀ ∩ O) ∧ g c = G (0, 1 / 2))
    (hball₁ : ∀ O ∈ 𝓝 (G (0, 1 / 2)),
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
          MapsTo g (Metric.ball c r) (S₁ ∩ O) ∧ g c = G (0, 1 / 2))
    (hX : IsClosed X) (hY : IsClosed Y)
    (hregX : closure (interior X) = X) (hregY : closure (interior Y) = Y)
    (hCN : C ⊆ N) (hNW₀ : N ∩ S₀ = N ∩ W₀) (hNW₁ : N ∩ S₁ = N ∩ W₁)
    (hP₀ : P 0 = W₀ ∩ Y) (hP₂ : P 2 = W₀ \ interior Y)
    (hP₁ : P 1 = W₁ ∩ X) (hP₃ : P 3 = W₁ \ interior X) :
    ∃ H : (ℝ × ℝ) × ℝ → E, IsPLHomeomorphOn H spliceCylinder C ∧
      (∀ t, H (0, t) = G (0, t)) ∧
      (∀ T : Set ℝ, H '' (spliceSquare ×ˢ T) = G '' (spliceSquare ×ˢ T)) ∧
      ∀ i, H '' section34MarkedRibbon i = C ∩ P i := by
  have hCW₀ : C ∩ S₀ = C ∩ W₀ := by
    have h := congrArg (fun A => C ∩ A) hNW₀
    rwa [← inter_assoc, inter_eq_left.mpr hCN, ← inter_assoc, inter_eq_left.mpr hCN] at h
  have hCW₁ : C ∩ S₁ = C ∩ W₁ := by
    have h := congrArg (fun A => C ∩ A) hNW₁
    rwa [← inter_assoc, inter_eq_left.mpr hCN, ← inter_assoc, inter_eq_left.mpr hCN] at h
  obtain ⟨H, hH, haxis, hfaces, h₀, h₂, h₁, h₃⟩ := exists_marked_cell_side_alignment hG
    hS₀ hS₁ hFX hFY hc hcross hball₀ hball₁ hX hY hregX hregY
  refine ⟨H, hH, haxis, hfaces, ?_⟩
  intro i
  fin_cases i
  · change H '' section34MarkedRibbon 0 = C ∩ P 0
    simpa only [hP₀, hCW₀, inter_assoc] using h₀
  · change H '' section34MarkedRibbon 1 = C ∩ P 1
    simpa only [hP₁, hCW₁, inter_assoc] using h₁
  · change H '' section34MarkedRibbon 2 = C ∩ P 2
    simpa only [hP₂, hCW₀, inter_sdiff_assoc] using h₂
  · change H '' section34MarkedRibbon 3 = C ∩ P 3
    simpa only [hP₃, hCW₁, inter_sdiff_assoc] using h₃

end DifferentialGeometry.Topology.PiecewiseLinear

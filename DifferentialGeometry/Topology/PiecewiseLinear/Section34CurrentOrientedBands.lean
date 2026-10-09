import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingOrderedBands
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LateralBandReversal

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_oriented_lateral_band_of_ordered_caps {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ T : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) {n : ℕ} {J D₀ D₁ : Fin n → Set M}
    (hcap : ∀ i, IsPLCellOn 2 (D₀ i) (J i) ∧ IsPLCellOn 2 (D₁ i) (J i) ∧
      D₀ i ∪ D₁ i = B ∧ D₀ i ∩ D₁ i = J i ∧ A₀ ⊆ D₀ i ∧ A₁ ⊆ D₁ i)
    (hdis : ∀ i j, i < j → Disjoint (D₀ i) (D₁ j))
    (hleft : ∀ i j, J i ⊆ D₀ j ↔ i ≤ j)
    (hright : ∀ i j, J i ⊆ D₁ j ↔ j ≤ i)
    (hJA : ∀ i, J i ⊆ A) (hJend : ∀ i, Disjoint (J i) (A₀ ∪ A₁))
    (htrace : A ∩ T ⊆ ⋃ i, J i) (i j : Fin n) (hij : i ≠ j) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = S ∧
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        D₁ (min i j) ∩ D₀ (max i j) ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = J i ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = J j ∧
      (∀ k, J k ⊆ (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
        min i j ≤ k ∧ k ≤ max i j) ∧
      (i.val + 1 = j.val ∨ j.val + 1 = i.val →
        Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) T) := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · obtain ⟨P, u, f, hP, hu, hS', hf, hfP, hfc, hfA, hf₀, hf₁, hint, hempty⟩ :=
      hS.exists_lateral_bands_of_ordered_caps hA hAB hcap hdis hleft hright
        hJA hJend htrace i j hlt
    refine ⟨P, u, f, hP, hu, hS', hf, hfP, ?_, hfA, hf₀, hf₁, ?_, ?_⟩
    · simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using hfc
    · simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using hint
    · intro hadj
      apply hempty
      have := hlt
      omega
  · obtain ⟨P, u, f, hP, hu, hS', hf, hfP, hfc, hfA, hf₀, hf₁, hint, hempty⟩ :=
      hS.exists_lateral_bands_of_ordered_caps hA hAB hcap hdis hleft hright
        hJA hJend htrace j i hlt
    obtain ⟨g, hg, hgP, hgc, hgo, hg₀, hg₁⟩ := exists_lateral_PL_band_reversal u hf hfP
    refine ⟨P, u, g, hP, hu, hS', hg, hgP, ?_, hgc ▸ hfA,
      hg₀.trans hf₁, hg₁.trans hf₀, ?_, ?_⟩
    · simpa only [min_eq_right hlt.le, max_eq_left hlt.le] using hgc.trans hfc
    · simpa only [hgc, min_eq_right hlt.le, max_eq_left hlt.le] using hint
    · intro hadj
      rw [hgo]
      apply hempty
      have := hlt
      omega

end DifferentialGeometry.Topology.PiecewiseLinear

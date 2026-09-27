import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingCollarRibbonTraces

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_common_seam_collar_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Fin 2 → (ℝ × ℝ) × ℝ → E} {C : Fin 2 → Set E} {S L : Set E}
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k)) (a b : Fin 2 → Bool)
    (hbase : ∀ k, f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1) ⊆ S)
    (hL : ∀ k, L ∈ 𝓝ˢ[S] (f k '' section34MarkedAxis))
    {c : ℝ} (hc : 0 < c) (e : Fin 2 → ℝ) (he : ∀ k, 0 < e k) :
    ∃ d : ℝ, 0 < d ∧ d ≤ c ∧ d ≤ 1 ∧ (∀ k, d / 2 ≤ e k) ∧
      ∀ k r, r ∈ Icc (0 : ℝ) d → ∀ s ∈ Icc (0 : ℝ) 1,
        f k ((0, if b k then r / 2 else -r / 2), s) ∈ L ∧
          f k ((if a k then r / 2 else -r / 2, 0), s) ∈ L := by
  choose δ hδ hδ1 hshort using fun k =>
    (hf k).exists_short_corner_strip_in_neighborhood (a k) (b k) (hbase k) (hL k)
  let d := min c (min (min (δ 0) (δ 1)) (2 * min (e 0) (e 1)))
  have hd : 0 < d := lt_min hc
    (lt_min (lt_min (hδ 0) (hδ 1)) (mul_pos (by norm_num) (lt_min (he 0) (he 1))))
  have hdc : d ≤ c := min_le_left _ _
  have hdδ (k : Fin 2) : d ≤ δ k := by
    have hh : d ≤ min (δ 0) (δ 1) :=
      (min_le_right c _).trans (min_le_left (min (δ 0) (δ 1)) _)
    fin_cases k
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans (min_le_right _ _)
  have hde (k : Fin 2) : d / 2 ≤ e k := by
    have hh : d ≤ 2 * min (e 0) (e 1) :=
      (min_le_right c _).trans (min_le_right (min (δ 0) (δ 1)) _)
    fin_cases k
    · change d / 2 ≤ e 0
      linarith [min_le_left (e 0) (e 1)]
    · change d / 2 ≤ e 1
      linarith [min_le_right (e 0) (e 1)]
  refine ⟨d, hd, hdc, (hdδ 0).trans (hδ1 0), hde, ?_⟩
  intro k r hr s hs
  have hp₀ : (0, if b k then (1 : ℝ) / 2 else -1 / 2) ∈
      section34CornerBase (a k) (b k) := by
    right
    cases b k <;> norm_num
  have hp₁ : (if a k then (1 : ℝ) / 2 else -1 / 2, 0) ∈
      section34CornerBase (a k) (b k) := by
    left
    cases a k <;> norm_num
  have hh₀ := hshort k _ hp₀ s hs r ⟨hr.1, hr.2.trans (hdδ k)⟩
  have hh₁ := hshort k _ hp₁ s hs r ⟨hr.1, hr.2.trans (hdδ k)⟩
  constructor
  · cases hb : b k <;>
      simpa [hb, Prod.smul_mk, smul_eq_mul, div_eq_mul_inv] using hh₀
  · cases ha : a k <;>
      simpa [ha, Prod.smul_mk, smul_eq_mul, div_eq_mul_inv] using hh₁

end DifferentialGeometry.Topology.PiecewiseLinear

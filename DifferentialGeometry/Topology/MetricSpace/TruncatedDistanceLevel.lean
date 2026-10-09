import DifferentialGeometry.Topology.MetricSpace.TruncatedDistance

noncomputable section

open scoped ENNReal NNReal

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

/-- Truncate before taking `toReal`, so disconnected components also have finite data. -/
theorem lipschitzWith_truncated_edist_level (p : X) (N : ℝ≥0) :
    LipschitzWith 1 (fun x => (min (edist x p) (N : ℝ≥0∞)).toReal) := by
  intro x y
  rw [ENNReal.coe_one, one_mul]
  change edist ((min (edist x p) (N : ℝ≥0∞)).toReal)
    ((min (edist y p) (N : ℝ≥0∞)).toReal) ≤ edist x y
  by_cases hxy : edist x y = ⊤
  · rw [hxy]
    exact le_top
  by_cases hxp : edist x p = ⊤
  · have hyp : edist y p = ⊤ := by
      by_contra hyp
      have hfin := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hxy, hyp⟩)
        (edist_triangle x y p)
      exact hfin hxp
    rw [hxp, hyp, edist_self]
    exact zero_le
  · have hyp : edist y p ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨by simpa only [edist_comm y x] using hxy, hxp⟩) (edist_triangle y x p)
    have hmin := (LipschitzWith.id (α := ℝ)).min_const (N : ℝ)
    have h := hmin (edist x p).toReal (edist y p).toReal
    simp only [ENNReal.coe_one, one_mul] at h
    rw [ENNReal.toReal_min hxp ENNReal.coe_ne_top,
      ENNReal.toReal_min hyp ENNReal.coe_ne_top, ENNReal.coe_toReal]
    apply h.trans
    rw [edist_dist, Real.dist_eq]
    have hx := ENNReal.toReal_le_add (edist_triangle x y p) hxy hyp
    have hy := ENNReal.toReal_le_add (edist_triangle y x p)
      (by simpa only [edist_comm y x] using hxy) hxp
    rw [edist_comm y x] at hy
    have habs : |(edist x p).toReal - (edist y p).toReal| ≤ (edist x y).toReal :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    exact (ENNReal.ofReal_le_ofReal habs).trans ENNReal.ofReal_toReal_le

theorem truncated_edist_level_mem_Icc (x p : X) (N : ℝ≥0) :
    (min (edist x p) (N : ℝ≥0∞)).toReal ∈ Set.Icc (0 : ℝ) N := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.coe_ne_top
    (min_le_right (edist x p) (N : ℝ≥0∞))
  simpa only [ENNReal.coe_toReal] using h

end EMetric

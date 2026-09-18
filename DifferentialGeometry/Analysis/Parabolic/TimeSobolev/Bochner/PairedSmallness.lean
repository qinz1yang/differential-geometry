import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.LocalSmallness

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem exists_pos_l2_slice_norm_lt {X : Type*} [NormedAddCommGroup X]
    {T : ℝ} (hT : 0 < T) (f : timeL2 X T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ T ∧ ∀ a b : ℝ, ∀ ha : 0 ≤ a, ∀ hbT : b ≤ T,
      0 ≤ b - a → b - a ≤ δ → ‖timeL2.slice f a b ha hbT‖ < ε := by
  let ε₀ : ℝ := min ε (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀le : ε₀ ≤ 1 / 2 := min_le_right _ _
  let C : ℝ≥0 := ⟨1 - ε₀, by linarith⟩
  have hC : (C : ℝ) < 1 := by
    change 1 - ε₀ < 1
    linarith
  obtain ⟨δ, hδ, hδT, hs⟩ := exists_pos_l2_slice_contraction_lt hT f C hC
  refine ⟨δ, hδ, hδT, ?_⟩
  intro a b ha hbT hd hdδ
  have hsmall := hs a b ha hbT hd hdδ
  have hsqrt : 1 ≤ Real.sqrt (1 + (b - a)) :=
    Real.one_le_sqrt.mpr (by linarith)
  have hbase : (C : ℝ) ≤ (C : ℝ) * (1 + (b - a)) := by
    nlinarith [C.coe_nonneg]
  have hn := norm_nonneg (timeL2.slice f a b ha hbT)
  have hnorm : ‖timeL2.slice f a b ha hbT‖ ≤
      Real.sqrt (1 + (b - a)) * ‖timeL2.slice f a b ha hbT‖ := by
    nlinarith
  have htarget : ‖timeL2.slice f a b ha hbT‖ < ε₀ := by
    change 1 - ε₀ ≤ _ at hbase
    nlinarith
  exact htarget.trans_le (min_le_left _ _)

theorem exists_pos_l2_slice_pair_contraction_lt
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {T : ℝ} (hT : 0 < T) (f : timeL2 X T) (g : timeL2 Y T)
    {q B C : ℝ} (hq : q < 1) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ δ > 0, δ ≤ T ∧ ∀ a b : ℝ, ∀ ha : 0 ≤ a, ∀ hbT : b ≤ T,
      0 ≤ b - a → b - a ≤ δ →
        q + B * Real.sqrt (b - a) +
          C * (‖timeL2.slice f a b ha hbT‖ + ‖timeL2.slice g a b ha hbT‖) < 1 := by
  let gap : ℝ := 1 - q
  let ε : ℝ := gap / (8 * (C + 1))
  let η : ℝ := gap / (4 * (B + 1))
  have hgap : 0 < gap := sub_pos.mpr hq
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hεeq : ε * (8 * (C + 1)) = gap :=
    div_mul_cancel₀ gap (by positivity)
  have hηeq : η * (4 * (B + 1)) = gap :=
    div_mul_cancel₀ gap (by positivity)
  obtain ⟨δ₁, hδ₁, hδ₁T, hs₁⟩ := exists_pos_l2_slice_norm_lt hT f hε
  obtain ⟨δ₂, hδ₂, _, hs₂⟩ := exists_pos_l2_slice_norm_lt hT g hε
  let δ : ℝ := min δ₁ (min δ₂ (η ^ 2))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, hδ, (min_le_left _ _).trans hδ₁T, ?_⟩
  intro a b ha hbT hd hdδ
  have hd₁ : b - a ≤ δ₁ := hdδ.trans (min_le_left _ _)
  have hd₂ : b - a ≤ δ₂ :=
    hdδ.trans ((min_le_right δ₁ _).trans (min_le_left _ _))
  have hdη : b - a ≤ η ^ 2 :=
    hdδ.trans ((min_le_right δ₁ _).trans (min_le_right _ _))
  have hsqrt : Real.sqrt (b - a) ≤ η := Real.sqrt_le_iff.mpr ⟨hη.le, hdη⟩
  have hn₁ := hs₁ a b ha hbT hd hd₁
  have hn₂ := hs₂ a b ha hbT hd hd₂
  have hsum : ‖timeL2.slice f a b ha hbT‖ + ‖timeL2.slice g a b ha hbT‖ ≤ 2 * ε := by
    linarith
  have hBt := mul_le_mul_of_nonneg_left hsqrt hB
  have hCt := mul_le_mul_of_nonneg_left hsum hC
  dsimp only [gap] at hεeq hηeq hgap
  nlinarith

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

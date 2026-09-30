import DifferentialGeometry.Geometry.Comparison.PairedDistanceResidual

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem PairedComparisonPacket.cube_subset_distanceCoordinates_image_three
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : Fin 3 → X} {q : X} {a₀ A δ r : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / 300)
    (hr : 0 < r) (hcomplete : IsComplete (closedBall q r)) (hbuffer : ball q (2 * r) ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A) :
    let μ := 1 - 3 * δ ^ 2 - 12 * δ
    let e := min 1 (min (a₀ / 2) (min (δ ^ 2 / (4 * cosh (A + 1) / sinh a₀)) (μ * r / 2)))
    9 / 10 ≤ μ ∧ 0 < e ∧
      {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - dist q (a j)| ≤ e / 4} ⊆
        distanceCoordinates 2 a '' ball q (r / 2) ∧
      LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 a) := by
  let μ := 1 - 3 * δ ^ 2 - 12 * δ
  let K := 4 * cosh (A + 1) / sinh a₀
  let e := min 1 (min (a₀ / 2) (min (δ ^ 2 / K) (μ * r / 2)))
  change 9 / 10 ≤ μ ∧ 0 < e ∧ _
  have hδm' : δ ≤ 1 / (100 * (Fintype.card (Fin 3) : ℝ)) := by norm_num; exact hδm
  have hconstants := paired_correction_constants (by norm_num : 0 < 3) hδ (by norm_num; exact hδm)
  have hμ : 9 / 10 ≤ μ := by norm_num [μ] at hconstants ⊢; exact hconstants.1
  have hμpos : 0 < μ := by linarith
  have hK : 0 < K := div_pos (mul_pos (by norm_num) (cosh_pos _)) (sinh_pos_iff.mpr ha₀)
  have he : 0 < e := lt_min zero_lt_one
    (lt_min (half_pos ha₀) (lt_min (div_pos (sq_pos_of_pos hδ) hK) (by positivity)))
  refine ⟨hμ, he, ?_, ?_⟩
  · intro w hw
    let w₁ : PiLp 1 (fun _ : Fin 3 => ℝ) := WithLp.toLp 1 (fun j => w j)
    have hμeq : 1 - 3 * δ ^ 2 - 6 * (Fintype.card (Fin 3) - 1 : ℝ) * δ = μ := by
      norm_num [μ]
    have herr : dist (distanceCoordinates 1 a q) w₁ ≤ 3 * e / 4 := by
      have hi (j : Fin 3) : dist (distanceCoordinates 1 a q j) (w₁ j) ≤ e / 4 := by
        simpa only [distanceCoordinates_apply, w₁, PiLp.toLp_apply, Real.dist_eq, abs_sub_comm] using hw j
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hi j)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
      norm_num only [Nat.cast_ofNat] at hh
      rw [show (3 : ℝ) * (e / 4) = 3 * e / 4 by ring] at hh
      simpa only [PiLp.dist_eq_sum (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal),
        ENNReal.toReal_one, Real.rpow_one, one_div_one, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
    have her : dist (distanceCoordinates 1 a q) w₁ < e := by linarith
    have he1 : e ≤ 1 := min_le_left _ _
    have hea : e ≤ a₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have heK : e ≤ δ ^ 2 / K := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have heμ : e ≤ μ * r / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨z, _, hfz, hd⟩ := hpacket.exists_preimage_in_complete_buffer hcurves hcomp hV hanchors
      ha₀ hδ hδm' hr hcomplete hbuffer hbounds (her.le.trans he1) (her.le.trans hea)
      (her.le.trans heK) (by rw [hμeq]; exact her.le.trans heμ)
    refine ⟨z, ?_, ?_⟩
    · rw [mem_ball, dist_comm]
      apply hd.trans_lt
      rw [hμeq]
      apply (div_lt_iff₀ hμpos).mpr
      linarith [her.trans_le heμ]
    · apply PiLp.ext
      intro j
      exact congrArg (fun v : PiLp 1 (fun _ : Fin 3 => ℝ) => v j) hfz
  · simpa using lipschitzWith_distanceCoordinates_two a

end DifferentialGeometry.Geometry.Comparison.Toponogov

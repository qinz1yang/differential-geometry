import DifferentialGeometry.Geometry.Comparison.AngleReversal

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem four_cross_angles_near_pi_div_two {α α' γ γ' δ τ ω σ : ℝ}
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hω : 0 ≤ ω)
    (hdiff : |α - α'| ≤ σ) (hasum : α + α' ≤ Real.pi + τ)
    (hgsum : γ + γ' ≤ Real.pi + τ)
    (hp : Real.pi - δ - 2 * ω ≤ α + γ)
    (hp' : Real.pi - δ - 2 * ω ≤ α' + γ') :
    let E := 2 * δ + 3 * τ / 2 + 4 * ω + σ / 2
    |α - Real.pi / 2| ≤ E ∧ |α' - Real.pi / 2| ≤ E ∧
      |γ - Real.pi / 2| ≤ E ∧ |γ' - Real.pi / 2| ≤ E := by
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply abs_le.mpr <;> constructor <;> linarith

theorem rank_increase_angle_error_lt {β δ K s : ℝ}
    (hβ : 0 < β) (hδ : δ ≤ β / 100)
    (hKs : K * s ≤ (β / (100 * Real.pi)) ^ 2) :
    2 * δ + 3 * (β / 100) / 2 + 4 * (Real.pi * sqrt (K * s)) +
      (Real.pi * sqrt ((β / (100 * Real.pi)) ^ 2 + K * s)) / 2 < β / 10 := by
  have hq : 0 ≤ β / (100 * Real.pi) := by positivity
  have hw : Real.pi * sqrt (K * s) ≤ β / 100 := by
    have h := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hKs) pi_pos.le
    rw [sqrt_sq hq] at h
    convert h using 1; field_simp
  have hs : Real.pi * sqrt ((β / (100 * Real.pi)) ^ 2 + K * s) ≤ β / 50 := by
    have hb : sqrt ((β / (100 * Real.pi)) ^ 2 + K * s) ≤ 2 * (β / (100 * Real.pi)) := by
      apply (sqrt_le_iff).mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (β / (100 * Real.pi))]
    have h := mul_le_mul_of_nonneg_left hb pi_pos.le
    convert h using 1; field_simp; ring
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov

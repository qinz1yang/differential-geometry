import DifferentialGeometry.Geometry.Coordinates.StereographicComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace DifferentialGeometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private theorem stereographic_half_chord_zero_sq (z : ℂ) :
    (dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2) ^ 2 *
      (‖z‖ ^ 2 + 4) = ‖z‖ ^ 2 := by
  have h := dist_stereographicComplex_symm_sq z 0
  simp only [dist_zero_right, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add] at h
  have hp : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  field_simp [hp] at h ⊢
  nlinarith

private theorem stereographic_half_chord_north_sq (z : ℂ) :
    (dist (stereographicComplex.symm z).val sphereNorthPole / 2) ^ 2 * (‖z‖ ^ 2 + 4) = 4 := by
  have h := dist_stereographicComplex_symm_northPole_sq z
  have hp : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  field_simp [hp] at h ⊢
  nlinarith

private theorem stereographic_half_chord_zero_le (z : ℂ) :
    dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2 ≤ ‖z‖ / 2 := by
  have h := stereographic_half_chord_zero_sq z
  have hp := mul_nonneg (sq_nonneg
    (dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2)) (sq_nonneg ‖z‖)
  nlinarith [dist_nonneg (x := (stereographicComplex.symm z).val)
    (y := (stereographicComplex.symm 0).val), norm_nonneg z]

private theorem norm_lt_one_of_half_chord_zero_le {z : ℂ}
    (h : dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2 ≤ 1 / 4) :
    ‖z‖ < 1 := by
  have he := stereographic_half_chord_zero_sq z
  have hd : 0 ≤ dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2 := by positivity
  have hs : (dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2) ^ 2 ≤ 1 / 16 := by
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ ‖z‖ ^ 2 + 4 by positivity)
  nlinarith [norm_nonneg z]

private theorem half_le_stereographic_half_chord_north {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (1 / 2 : ℝ) ≤ dist (stereographicComplex.symm z).val sphereNorthPole / 2 := by
  have he := stereographic_half_chord_north_sq z
  have hn : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hp := mul_nonneg (sub_nonneg.mpr hn)
    (sq_nonneg (dist (stereographicComplex.symm z).val sphereNorthPole / 2))
  have hd : 0 ≤ dist (stereographicComplex.symm z).val sphereNorthPole / 2 := by positivity
  nlinarith

private theorem norm_le_of_le_stereographic_half_chord_north {z : ℂ} {a : ℝ} (ha : 0 < a)
    (h : a ≤ dist (stereographicComplex.symm z).val sphereNorthPole / 2) : ‖z‖ ≤ 2 / a := by
  have he := stereographic_half_chord_north_sq z
  have hs : a ^ 2 ≤ (dist (stereographicComplex.symm z).val sphereNorthPole / 2) ^ 2 := by
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg ‖z‖)
  apply (le_div_iff₀ ha).mpr
  nlinarith [sq_nonneg (dist (stereographicComplex.symm z).val sphereNorthPole / 2), norm_nonneg z]

theorem exists_stereographic_disk_inclusions_of_inverse_holder
    (H β : ℝ) (hH : 1 ≤ H) (hβ : 0 < β) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 ≤ R ∧
      ∀ (Q : S2 ≃ₜ S2) (h : ℂ ≃ₜ ℂ),
        (∀ z : ℂ, (stereographicComplex.symm (h z)).val = Q (stereographicComplex.symm z).val) →
        h 0 = 0 → Q sphereNorthPole = sphereNorthPole →
        (∀ ξ η : S2, dist (Q.symm ξ) (Q.symm η) / 2 ≤
          H * Real.rpow (dist ξ η / 2) β) →
        Metric.closedBall (0 : ℂ) ρ ⊆ h '' Metric.ball 0 1 ∧
          h '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.closedBall 0 R := by
  let a := Real.rpow (1 / (2 * H)) β⁻¹
  let b := Real.rpow (1 / (4 * H)) β⁻¹
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have hapow : Real.rpow a β = 1 / (2 * H) :=
    Real.rpow_inv_rpow (by positivity) hβ.ne'
  have hbpow : Real.rpow b β = 1 / (4 * H) :=
    Real.rpow_inv_rpow (by positivity) hβ.ne'
  refine ⟨2 * b, 2 / a, by positivity, by positivity, ?_⟩
  intro Q h hchart hzero hnorth hholder
  have hchartInv (z : ℂ) : Q.symm (stereographicComplex.symm z).val =
      (stereographicComplex.symm (h.symm z)).val := by
    have hc := hchart (h.symm z)
    rw [h.apply_symm_apply] at hc
    exact (congrArg Q.symm hc).trans (Q.symm_apply_apply _)
  have hInvZero : Q.symm (stereographicComplex.symm 0).val = (stereographicComplex.symm 0).val := by
    have hz : h.symm 0 = 0 := h.injective ((h.apply_symm_apply 0).trans hzero.symm)
    exact (hchartInv 0).trans (congrArg (fun z : ℂ => (stereographicComplex.symm z).val) hz)
  have hInvNorth : Q.symm sphereNorthPole = sphereNorthPole := by
    exact (congrArg Q.symm hnorth.symm).trans (Q.symm_apply_apply sphereNorthPole)
  constructor
  · intro z hz
    have hz' : ‖z‖ ≤ 2 * b := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hd : dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2 ≤ b :=
      (stereographic_half_chord_zero_le z).trans (by linarith)
    have hh := hholder (stereographicComplex.symm z).val (stereographicComplex.symm 0).val
    rw [hchartInv, hInvZero] at hh
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤
      dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2) hd hβ.le
    change Real.rpow (dist (stereographicComplex.symm z).val (stereographicComplex.symm 0).val / 2) β ≤ Real.rpow b β at hp
    rw [hbpow] at hp
    have hsmall : dist (stereographicComplex.symm (h.symm z)).val
        (stereographicComplex.symm 0).val / 2 ≤ 1 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hp hHp.le
      have hc : H * (1 / (4 * H)) = 1 / 4 := by field_simp [hHp.ne']
      rw [hc] at hmul
      exact hh.trans hmul
    refine ⟨h.symm z, ?_, h.apply_symm_apply z⟩
    simpa only [Metric.mem_ball, dist_zero_right] using norm_lt_one_of_half_chord_zero_le hsmall
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hh := hholder (stereographicComplex.symm (h z)).val sphereNorthPole
    rw [hchartInv, h.symm_apply_apply, hInvNorth] at hh
    have hlow : 1 / (2 * H) ≤ Real.rpow
        (dist (stereographicComplex.symm (h z)).val sphereNorthPole / 2) β := by
      have hc := (half_le_stereographic_half_chord_north hz').trans hh
      apply (div_le_iff₀ (show 0 < 2 * H by positivity)).mpr
      nlinarith
    have hpow := (Real.rpow_le_rpow_iff ha.le (by positivity) hβ).mp
      (hapow ▸ hlow)
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_le_of_le_stereographic_half_chord_north ha hpow

end DifferentialGeometry

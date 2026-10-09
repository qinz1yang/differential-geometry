import DifferentialGeometry.Geometry.Metric.Approximation.ExactRadiusLifts
import DifferentialGeometry.Geometry.Metric.Approximation.EqualRadiusStrainerConfiguration

set_option autoImplicit false

open Set Metric


open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

noncomputable def reverseStrainerTolerance (r α : ℝ) : ℝ :=
  min (1 / 8) (min (1 / (4 * (r + 1))) (equalRadiusStrainerMargin r α / 60))

theorem reverseStrainerTolerance_pos {r α : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1) :
    0 < reverseStrainerTolerance r α := by
  have hμ := equalRadiusStrainerMargin_pos hr hα hαone
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem reverseStrainerTolerance_lt_one (r α : ℝ) :
    reverseStrainerTolerance r α < 1 :=
  (min_le_left _ _).trans_lt (by norm_num)

theorem radius_buffer_and_chord_error_of_le_reverseStrainerTolerance {r α ε : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1) (hε : 0 < ε)
    (hbound : ε ≤ reverseStrainerTolerance r α) :
    r + 5 * ε < ε⁻¹ ∧ 27 * ε < equalRadiusStrainerMargin r α := by
  have hμ := equalRadiusStrainerMargin_pos hr hα hαone
  have hsmall : ε ≤ 1 / 8 := hbound.trans (min_le_left _ _)
  have hrad : ε ≤ 1 / (4 * (r + 1)) :=
    hbound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmargin : ε ≤ equalRadiusStrainerMargin r α / 60 :=
    hbound.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hprod := (le_div_iff₀ (show 0 < 4 * (r + 1) by positivity)).mp hrad
  have hinv : 4 * (r + 1) ≤ ε⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hε).mpr (by nlinarith)
  constructor
  · have hs : r + 5 * ε < 4 * (r + 1) := by linarith
    exact hs.trans_le hinv
  · linarith

theorem KleinerLottApprox.exists_exact_radius_strainer_of_le_reverseStrainerTolerance
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {p : X} {y : Y}
    {k : ℕ} {r α ε : ℝ}
    (φ : KleinerLottApprox p
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), y)) ε)
    (hsegments : ∀ a b : X, ∃ c : Icc (0 : ℝ) 1 → X,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t)
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1)
    (hbound : ε ≤ reverseStrainerTolerance r α) :
    ∃ a : Fin k × Bool → X,
      (∀ j, dist p (a j) = r) ∧
      (∀ j, dist (φ.toFun (a j))
        (WithLp.toLp 2 (PiLp.single 2 j.1 (if j.2 then r else -r), y)) < 14 * ε) ∧
      (∀ j l, |dist (a j) (a l) - r *
        ‖(PiLp.single 2 j.1 (if j.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin k)) -
          PiLp.single 2 l.1 (if l.2 then (1 : ℝ) else -1)‖| < 27 * ε) ∧
      (∀ j, Real.pi - α < metricComparisonAngle (a (j, true)) p (a (j, false))) ∧
      (∀ j l, j ≠ l → ∀ b c : Bool,
        Real.pi / 2 - α < metricComparisonAngle (a (j, b)) p (a (l, c))) ∧
      Function.Injective a ∧ ∀ j, a j ≠ p := by
  obtain ⟨hbuffer, hmargin⟩ :=
    radius_buffer_and_chord_error_of_le_reverseStrainerTolerance hr hα hαone φ.error_pos hbound
  obtain ⟨_x, a, _hxmem, _hxlift, _hlength, harad, _htail, hamap, hpair⟩ :=
    φ.exists_exact_radius_signed_axis_lifts hsegments hr hbuffer
  obtain ⟨hopposite, hcross, hinj, hne⟩ :=
    equal_radius_strainer_angles_of_chord_errors hr hα hαone a harad hmargin
      (fun j l => (hpair j l).le)
  exact ⟨a, harad, hamap, hpair, hopposite, hcross, hinj, hne⟩

end GC.MetricGeometry

import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

open MeasureTheory Filter
open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem quasilinear_forcing_shift_sub_norm_le
    {𝕜 A X Y Z : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {T : ℝ} {S : Set Z}
    (m : A →L[𝕜] Y →L[𝕜] Y) (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z)
    (alpha : ℝ → Z → A) (reaction : ℝ → Z → Y) (offset : ℝ → Y)
    (f g : X) (w : timeL2 X T) (F G : timeL2 Y T)
    {a : ℝ} (ha : 0 ≤ a) {Lalpha Lreaction : ℝ≥0}
    (halpha : ∀ᵐ t ∂(timeMeasure T), LipschitzOnWith Lalpha (alpha t) S)
    (hreaction : ∀ᵐ t ∂(timeMeasure T), LipschitzOnWith Lreaction (reaction t) S)
    (hstatef : ∀ᵐ t ∂(timeMeasure T), J (f + w t) ∈ S)
    (hstateg : ∀ᵐ t ∂(timeMeasure T), J (g + w t) ∈ S)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖alpha t (J (f + w t))‖ ≤ a)
    (hF : F =ᵐ[timeMeasure T] fun t =>
      m (alpha t (J (f + w t))) (Q (f + w t)) +
        reaction t (J (f + w t)) - offset t)
    (hG : G =ᵐ[timeMeasure T] fun t =>
      m (alpha t (J (g + w t))) (Q (g + w t)) +
        reaction t (J (g + w t)) - offset t) :
    ‖F - G‖ ≤ Real.sqrt T * ‖m‖ * a * ‖Q (f - g)‖ +
      (‖m‖ * Lalpha * (Real.sqrt T * ‖Q g‖ + ‖Q‖ * ‖w‖) +
        Real.sqrt T * Lreaction) * ‖J (f - g)‖ := by
  let K : ℝ := ‖m‖ * Lalpha * ‖Q‖ * ‖J (f - g)‖
  let D : ℝ := ‖m‖ * a * ‖Q (f - g)‖ +
    (‖m‖ * Lalpha * ‖Q g‖ + Lreaction) * ‖J (f - g)‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpoint : ∀ᵐ t ∂(timeMeasure T), ‖(F - G) t‖ ≤ K * ‖w t‖ + D := by
    filter_upwards [Lp.coeFn_sub F G, hF, hG, halpha, hreaction,
      hstatef, hstateg, hbound] with t hsub hFt hGt hat hBt hft hgt hab
    have hJ : J (f + w t) - J (g + w t) = J (f - g) := by
      simp only [map_add, map_sub, add_sub_add_right_eq_sub]
    have hdiffa : ‖alpha t (J (f + w t)) - alpha t (J (g + w t))‖ ≤
        Lalpha * ‖J (f - g)‖ := by
      simpa only [dist_eq_norm, hJ] using hat.dist_le_mul _ hft _ hgt
    have hdiffB : ‖reaction t (J (f + w t)) - reaction t (J (g + w t))‖ ≤
        Lreaction * ‖J (f - g)‖ := by
      simpa only [dist_eq_norm, hJ] using hBt.dist_le_mul _ hft _ hgt
    have hQ : ‖Q (g + w t)‖ ≤ ‖Q g‖ + ‖Q‖ * ‖w t‖ := by
      rw [map_add]
      calc
        ‖Q g + Q (w t)‖ ≤ ‖Q g‖ + ‖Q (w t)‖ := norm_add_le _ _
        _ ≤ ‖Q g‖ + ‖Q‖ * ‖w t‖ := add_le_add_right (Q.le_opNorm _) _
    have heq :
        (m (alpha t (J (f + w t))) (Q (f + w t)) +
          reaction t (J (f + w t)) - offset t) -
        (m (alpha t (J (g + w t))) (Q (g + w t)) +
          reaction t (J (g + w t)) - offset t) =
        m (alpha t (J (f + w t))) (Q (f - g)) +
          m (alpha t (J (f + w t)) - alpha t (J (g + w t))) (Q (g + w t)) +
          (reaction t (J (f + w t)) - reaction t (J (g + w t))) := by
      simp only [map_add, map_sub, sub_apply]
      module
    rw [hsub, Pi.sub_apply, hFt, hGt, heq]
    calc
      _ ≤ ‖m (alpha t (J (f + w t))) (Q (f - g))‖ +
          ‖m (alpha t (J (f + w t)) - alpha t (J (g + w t))) (Q (g + w t))‖ +
          ‖reaction t (J (f + w t)) - reaction t (J (g + w t))‖ :=
        (norm_add₃_le : ‖m (alpha t (J (f + w t))) (Q (f - g)) +
          m (alpha t (J (f + w t)) - alpha t (J (g + w t))) (Q (g + w t)) +
          (reaction t (J (f + w t)) - reaction t (J (g + w t)))‖ ≤ _)
      _ ≤ ‖m‖ * a * ‖Q (f - g)‖ +
          ‖m‖ * (Lalpha * ‖J (f - g)‖) * (‖Q g‖ + ‖Q‖ * ‖w t‖) +
          Lreaction * ‖J (f - g)‖ := by
        exact add_le_add (add_le_add
          (m.le_of_opNorm₂_le_of_le le_rfl hab le_rfl)
          (m.le_of_opNorm₂_le_of_le le_rfl hdiffa hQ)) hdiffB
      _ = K * ‖w t‖ + D := by dsimp only [K, D]; ring
  have h := timeL2_norm_le_of_ae_affine_bound (F - G) w hK hD hpoint
  calc
    ‖F - G‖ ≤ K * ‖w‖ + Real.sqrt T * D := h
    _ = _ := by dsimp only [K, D]; ring

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

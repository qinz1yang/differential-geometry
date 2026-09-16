import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftedTame

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {𝕜 T A X Y Z V : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem shifted_remainder_parameter_sub_norm_le
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A) (P : X →L[𝕜] V)
    (alpha alpha' : T → Z → A) (reaction reaction' : T → Z → Y)
    (f k v : X) (t : T) (A₀ Ka Kb : ℝ≥0) {W : ℝ}
    (hQk : ‖Q k‖ ≤ W)
    (hAf : ‖alpha t (J v)‖ ≤ A₀)
    (hAlpha : ‖alpha t (J v) - alpha' t (J v)‖ ≤ Ka * ‖P (f - k)‖)
    (hReaction : ‖reaction t (J v) - reaction' t (J v)‖ ≤ Kb * ‖P (f - k)‖) :
    ‖shiftedRemainder m Q J D d q alpha reaction f t v -
        shiftedRemainder m Q J D d q alpha' reaction' k t v‖ ≤
      (‖m‖ * Ka * ‖P‖ * ‖Q‖ * ‖v‖ +
        (‖m‖ * A₀ * ‖Q‖ + ‖m‖ * Ka * ‖P‖ * W + Kb * ‖P‖)) * ‖f - k‖ := by
  have hA : ‖alpha t (J v) - alpha' t (J v)‖ ≤
      (Ka : ℝ) * (‖P‖ * ‖f - k‖) :=
    hAlpha.trans (mul_le_mul_of_nonneg_left (P.le_opNorm _) Ka.coe_nonneg)
  have hB : ‖reaction t (J v) - reaction' t (J v)‖ ≤
      (Kb : ℝ) * (‖P‖ * ‖f - k‖) :=
    hReaction.trans (mul_le_mul_of_nonneg_left (P.le_opNorm _) Kb.coe_nonneg)
  have hterm := m.le_of_opNorm₂_le_of_le le_rfl hA (Q.le_opNorm v)
  have hprincipal := m.le_of_opNorm₂_le_of_le le_rfl hAf (Q.le_opNorm (f - k))
  have hshift := m.le_of_opNorm₂_le_of_le le_rfl hA hQk
  have heq : shiftedRemainder m Q J D d q alpha reaction f t v -
        shiftedRemainder m Q J D d q alpha' reaction' k t v =
      m (alpha t (J v) - alpha' t (J v)) (Q v) +
        m (alpha t (J v)) (Q (f - k)) +
        m (alpha t (J v) - alpha' t (J v)) (Q k) +
        (reaction t (J v) - reaction' t (J v)) := by
    simp only [shiftedRemainder, map_sub, sub_apply]
    module
  rw [heq]
  calc
    _ ≤ ‖m (alpha t (J v) - alpha' t (J v)) (Q v)‖ +
        ‖m (alpha t (J v)) (Q (f - k))‖ +
        ‖m (alpha t (J v) - alpha' t (J v)) (Q k)‖ +
        ‖reaction t (J v) - reaction' t (J v)‖ := norm_add₄_le
    _ ≤ ‖m‖ * ((Ka : ℝ) * (‖P‖ * ‖f - k‖)) * (‖Q‖ * ‖v‖) +
        ‖m‖ * (A₀ : ℝ) * (‖Q‖ * ‖f - k‖) +
        ‖m‖ * ((Ka : ℝ) * (‖P‖ * ‖f - k‖)) * W +
        (Kb : ℝ) * (‖P‖ * ‖f - k‖) :=
      add_le_add (add_le_add (add_le_add hterm hprincipal) hshift) hB
    _ = _ := by ring

theorem shifted_remainder_parameter_sub_norm_le_on_closedBall
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A) (P : X →L[𝕜] V)
    (f₀ : X) {δ : ℝ}
    (alpha : Metric.closedBall f₀ δ → T → Z → A)
    (reaction : Metric.closedBall f₀ δ → T → Z → Y)
    (f k : Metric.closedBall f₀ δ) (v : X) (t : T) (A₀ Ka Kb : ℝ≥0)
    (hAf : ‖alpha f t (J v)‖ ≤ A₀)
    (hAlpha : ‖alpha f t (J v) - alpha k t (J v)‖ ≤ Ka * ‖P ((f : X) - (k : X))‖)
    (hReaction : ‖reaction f t (J v) - reaction k t (J v)‖ ≤ Kb * ‖P ((f : X) - (k : X))‖) :
    let W := ‖Q f₀‖ + ‖Q‖ * δ
    let K₁ := ‖m‖ * Ka * ‖P‖ * ‖Q‖
    let K₀ := ‖m‖ * A₀ * ‖Q‖ + ‖m‖ * Ka * ‖P‖ * W + Kb * ‖P‖
    ‖shiftedRemainder m Q J D d q (alpha f) (reaction f) (f : X) t v -
        shiftedRemainder m Q J D d q (alpha k) (reaction k) (k : X) t v‖ ≤
      (K₁ * ‖v‖ + K₀) * ‖(f : X) - (k : X)‖ := by
  have hk : ‖(k : X) - f₀‖ ≤ δ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using k.property
  have hQk : ‖Q (k : X)‖ ≤ ‖Q f₀‖ + ‖Q‖ * δ := by
    calc
      ‖Q (k : X)‖ ≤ ‖Q f₀‖ + ‖Q (k : X) - Q f₀‖ := norm_le_norm_add_norm_sub' _ _
      _ = ‖Q f₀‖ + ‖Q ((k : X) - f₀)‖ := by rw [map_sub]
      _ ≤ ‖Q f₀‖ + ‖Q‖ * δ := add_le_add le_rfl
        ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hk (norm_nonneg Q)))
  exact shifted_remainder_parameter_sub_norm_le m Q J D d q P
    (alpha f) (alpha k) (reaction f) (reaction k) f k v t A₀ Ka Kb hQk hAf hAlpha hReaction

end DifferentialGeometry.Analysis.Parabolic

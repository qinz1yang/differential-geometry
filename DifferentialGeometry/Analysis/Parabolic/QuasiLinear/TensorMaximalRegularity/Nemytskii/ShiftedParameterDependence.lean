import Mathlib.Analysis.Normed.Operator.Prod
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

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {A X Y Z V : Type*}
  [SeminormedAddCommGroup A] [NormedSpace ℝ A]
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
  [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]

theorem shifted_remainder_time_parameter_sub_norm_le
    (m : A →L[ℝ] Y →L[ℝ] Y)
    (Q : X →L[ℝ] Y) (J : X →L[ℝ] Z) (D : Z →L[ℝ] Y)
    (d : Y →L[ℝ] Y) (q : A) (P : X →L[ℝ] V)
    (f₀ : X) {δ : ℝ}
    (alpha : Metric.closedBall f₀ δ → ℝ → Z → A)
    (reaction : Metric.closedBall f₀ δ → ℝ → Z → Y)
    (f k : Metric.closedBall f₀ δ) (v : X) (s s' t : ℝ)
    (A₀ Ka Kb : ℝ≥0)
    (hAf : ‖alpha f (s + t) (J v)‖ ≤ A₀)
    (hAlpha : ‖alpha f (s + t) (J v) - alpha k (s' + t) (J v)‖ ≤
      Ka * max |s - s'| ‖P ((f : X) - (k : X))‖)
    (hReaction : ‖reaction f (s + t) (J v) - reaction k (s' + t) (J v)‖ ≤
      Kb * max |s - s'| ‖P ((f : X) - (k : X))‖) :
    let Cq := ‖Q f₀‖ + ‖Q‖ * δ
    let K₁ := ‖m‖ * Ka * max 1 ‖P‖ * ‖Q‖
    let K₀ := ‖m‖ * A₀ * ‖Q‖ + ‖m‖ * Ka * max 1 ‖P‖ * Cq + Kb * max 1 ‖P‖
    ‖shiftedRemainder m Q J D d q
        (fun t z => alpha f (s + t) z) (fun t z => reaction f (s + t) z) f t v -
      shiftedRemainder m Q J D d q
        (fun t z => alpha k (s' + t) z) (fun t z => reaction k (s' + t) z) k t v‖ ≤
      (K₁ * ‖v‖ + K₀) * dist (s, f) (s', k) := by
  intro Cq K₁ K₀
  have hδ : 0 ≤ δ := dist_nonneg.trans (Metric.mem_closedBall.mp k.property)
  let Qp := Q.comp (ContinuousLinearMap.snd ℝ ℝ X)
  let Jp := J.comp (ContinuousLinearMap.snd ℝ ℝ X)
  let Pp := (ContinuousLinearMap.fst ℝ ℝ X).prod
    (P.comp (ContinuousLinearMap.snd ℝ ℝ X))
  have hQp : ‖Qp‖ ≤ ‖Q‖ := by
    exact (Q.opNorm_comp_le _).trans
      (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_snd_le ℝ ℝ X) (norm_nonneg Q))
  have hPp : ‖Pp‖ ≤ max 1 ‖P‖ := by
    dsimp only [Pp]
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    apply max_le_max (ContinuousLinearMap.norm_fst_le ℝ ℝ X)
    exact (P.opNorm_comp_le _).trans
      (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_snd_le ℝ ℝ X) (norm_nonneg P))
  have hk : ‖(k : X) - f₀‖ ≤ δ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using k.property
  have hQk : ‖Qp (s', (k : X))‖ ≤ Cq := by
    change ‖Q (k : X)‖ ≤ Cq
    calc
      _ ≤ ‖Q f₀‖ + ‖Q (k : X) - Q f₀‖ := norm_le_norm_add_norm_sub' _ _
      _ = ‖Q f₀‖ + ‖Q ((k : X) - f₀)‖ := by rw [map_sub]
      _ ≤ Cq := add_le_add le_rfl
        ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hk (norm_nonneg Q)))
  have hJpv : Jp (0, v) = J v := rfl
  have hparam : ‖Pp ((s, (f : X)) - (s', (k : X)))‖ =
      max |s - s'| ‖P ((f : X) - (k : X))‖ := rfl
  have hraw := shifted_remainder_parameter_sub_norm_le m Qp Jp D d q Pp
    (fun t z => alpha f (s + t) z) (fun t z => alpha k (s' + t) z)
    (fun t z => reaction f (s + t) z) (fun t z => reaction k (s' + t) z)
    (s, (f : X)) (s', (k : X)) (0, v) t A₀ Ka Kb hQk hAf
    (by simpa only [hparam, hJpv] using hAlpha)
    (by simpa only [hparam, hJpv] using hReaction)
  have hv : ‖((0 : ℝ), v)‖ = ‖v‖ := by
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have hdist : ‖(s, (f : X)) - (s', (k : X))‖ = dist (s, f) (s', k) := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Prod.dist_eq,
      Subtype.dist_eq, dist_eq_norm]
  change ‖shiftedRemainder m Q J D d q
      (fun t z => alpha f (s + t) z) (fun t z => reaction f (s + t) z) f t v -
    shiftedRemainder m Q J D d q
      (fun t z => alpha k (s' + t) z) (fun t z => reaction k (s' + t) z) k t v‖ ≤ _ at hraw
  rw [hv, hdist] at hraw
  refine hraw.trans ?_
  have hCq : 0 ≤ Cq := by dsimp only [Cq]; positivity
  dsimp only [K₁, K₀]
  gcongr

end DifferentialGeometry.Analysis.Parabolic

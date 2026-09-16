import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.RecenteredTame
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.MetricSpace.Lipschitz

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {𝕜 T A X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def shiftedRemainder
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A)
    (alpha : T → Z → A) (reaction : T → Z → Y)
    (f : X) (t : T) (v : X) : Y :=
  m (alpha t (J v) - q) (Q v) + m (alpha t (J v)) (Q f) +
    reaction t (J v) - d (D (J v))

private theorem shifted_remainder_eq_recentered_add
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A)
    (alpha : T → Z → A) (reaction : T → Z → Y)
    (f : X) (t : T) (v : X) :
    shiftedRemainder m Q J D d q alpha reaction f t v =
      recenteredRemainder m Q J D d q
        (fun t z => alpha t (z - J f)) (fun t z => reaction t (z - J f)) f t v +
        m q (Q f) + d (D (J f)) := by
  simp only [shiftedRemainder, recenteredRemainder, add_sub_cancel_left,
    map_add, map_sub, sub_apply]
  module

theorem shifted_remainder_uniform_tame_estimate
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A) (b₀ : Y)
    (f₀ : X) {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (alpha : Metric.closedBall f₀ δ → T → Z → A)
    (reaction : Metric.closedBall f₀ δ → T → Z → Y)
    (s : Set T) (K L M M₀ : ℝ≥0)
    (halip : ∀ f t, t ∈ s → LipschitzOnWith L (alpha f t) (Metric.closedBall 0 R))
    (haclose : ∀ f t, t ∈ s → ∀ z, ‖z‖ ≤ R →
      ‖alpha f t z - q‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ f t, t ∈ s →
      LipschitzOnWith M (reaction f t) (Metric.closedBall 0 R))
    (hreaction_zero : ∀ f t, t ∈ s → ‖reaction f t 0 - b₀‖ ≤ (M₀ : ℝ) * R) :
    let Cq := ‖Q f₀‖ + ‖Q‖ * δ
    let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
    let Bconst : ℝ≥0 := ‖m‖₊ * L * Cq.toNNReal + M + ‖d‖₊ * ‖D‖₊
    let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
    let D₀ := ‖m‖ * (‖q‖ + (K : ℝ) * R) * Cq + ‖b₀‖ + (M₀ : ℝ) * R
    ∀ f t, t ∈ s →
      (∀ u v : X, ‖J u‖ ≤ R → ‖J v‖ ≤ R →
        ‖shiftedRemainder m Q J D d q (alpha f) (reaction f) f t u -
          shiftedRemainder m Q J D d q (alpha f) (reaction f) f t v‖ ≤
          (Aconst : ℝ) * R * ‖u - v‖ + (Bconst : ℝ) * ‖J (u - v)‖ +
            (Cconst : ℝ) * (‖u‖ + ‖v‖) * ‖J (u - v)‖) ∧
      ‖shiftedRemainder m Q J D d q (alpha f) (reaction f) f t 0‖ ≤ D₀ := by
  dsimp only
  have hCq : 0 ≤ ‖Q f₀‖ + ‖Q‖ * δ := by positivity
  intro f t ht
  have hQf : ‖Q (f : X)‖ ≤ ‖Q f₀‖ + ‖Q‖ * δ := by
    have hf : ‖(f : X) - f₀‖ ≤ δ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using f.property
    calc
      ‖Q (f : X)‖ ≤ ‖Q f₀‖ + ‖Q (f : X) - Q f₀‖ := norm_le_norm_add_norm_sub' _ _
      _ = ‖Q f₀‖ + ‖Q ((f : X) - f₀)‖ := by rw [map_sub]
      _ ≤ ‖Q f₀‖ + ‖Q‖ * δ := add_le_add le_rfl
        ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg Q)))
  constructor
  · intro u v hu hv
    have ha_lip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
        ‖alpha f t z - alpha f t w‖ ≤ (L : ℝ) * ‖z - w‖ := by
      intro z hz w hw
      simpa only [dist_eq_norm] using (halip f t ht).dist_le_mul z
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) w
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
    have hB_lip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
        ‖reaction f t z - reaction f t w‖ ≤ (M : ℝ) * ‖z - w‖ := by
      intro z hz w hw
      simpa only [dist_eq_norm] using (hreaction f t ht).dist_le_mul z
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) w
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
    have hraw := recentered_tame_estimate m Q J D d q
      (fun t z => alpha f t (z - J f)) (fun t z => reaction f t (z - J f)) (f : X) t
      (by simpa only [add_sub_cancel_left] using ha_lip)
      (by simpa only [add_sub_cancel_left] using haclose f t ht)
      (by simpa only [add_sub_cancel_left] using hB_lip) hu hv
    rw [shifted_remainder_eq_recentered_add, shifted_remainder_eq_recentered_add,
      add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]
    refine hraw.trans ?_
    simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.coe_toNNReal _ hCq]
    gcongr
  · have ha0 : ‖alpha f t 0‖ ≤ ‖q‖ + (K : ℝ) * R := by
      exact (norm_le_norm_add_norm_sub' _ q).trans
        (add_le_add le_rfl (haclose f t ht 0 (by simpa only [norm_zero] using hR)))
    have hB0 : ‖reaction f t 0‖ ≤ ‖b₀‖ + (M₀ : ℝ) * R :=
      (norm_le_norm_add_norm_sub' _ b₀).trans (add_le_add le_rfl (hreaction_zero f t ht))
    simp only [shiftedRemainder, map_zero, zero_add, sub_zero]
    calc
      ‖m (alpha f t 0) (Q (f : X)) + reaction f t 0‖ ≤
          ‖m (alpha f t 0) (Q (f : X))‖ + ‖reaction f t 0‖ := norm_add_le _ _
      _ ≤ ‖m‖ * (‖q‖ + (K : ℝ) * R) * (‖Q f₀‖ + ‖Q‖ * δ) +
          (‖b₀‖ + (M₀ : ℝ) * R) :=
        add_le_add (m.le_of_opNorm₂_le_of_le le_rfl ha0 hQf) hB0
      _ = _ := by ring

end DifferentialGeometry.Analysis.Parabolic

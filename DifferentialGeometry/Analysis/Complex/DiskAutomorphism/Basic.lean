import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

open scoped ComplexConjugate

namespace Complex

def diskMoebius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

theorem diskMoebius_denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have ht : ‖conj a * z‖ < 1 := by
    rw [norm_mul, norm_conj]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz) ha
  rw [← h, norm_one] at ht
  exact (lt_irrefl 1) ht

theorem normSq_diskMoebius_identity (a z : ℂ) :
    normSq (1 - conj a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, mul_re, mul_im, conj_re, conj_im]
  ring

theorem norm_diskMoebius_le_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskMoebius a z‖ ≤ 1 := by
  have hden := diskMoebius_denominator_ne_zero ha hz
  have ha' : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz' : normSq z ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hi := normSq_diskMoebius_identity a z
  have hn : normSq (z - a) ≤ normSq (1 - conj a * z) := by nlinarith
  have hsq : normSq (diskMoebius a z) ≤ 1 := by
    rw [diskMoebius, normSq_div, div_le_one (normSq_pos.mpr hden)]
    exact hn
  rw [normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (diskMoebius a z)]

theorem norm_diskMoebius_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskMoebius a z‖ < 1 := by
  have hden := diskMoebius_denominator_ne_zero ha hz.le
  have ha' : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz' : normSq z < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hi := normSq_diskMoebius_identity a z
  have hn : normSq (z - a) < normSq (1 - conj a * z) := by nlinarith
  have hsq : normSq (diskMoebius a z) < 1 := by
    rw [diskMoebius, normSq_div, div_lt_one (normSq_pos.mpr hden)]
    exact hn
  rw [normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (diskMoebius a z)]

theorem diskMoebius_denominator_re_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 < (1 - conj a * z).re := by
  have hnorm : ‖conj a * z‖ < 1 := by
    rw [norm_mul, norm_conj]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz) ha
  have h := re_le_norm (conj a * z)
  simp only [sub_re, one_re]
  linarith

theorem norm_diskMoebius_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskMoebius a z‖ = 1 := by
  have hden := diskMoebius_denominator_ne_zero ha hz.le
  have hz' : normSq z = 1 := by rw [normSq_eq_norm_sq, hz]; norm_num
  have hi := normSq_diskMoebius_identity a z
  rw [hz'] at hi
  have hn : normSq (z - a) = normSq (1 - conj a * z) := by linarith
  have hsq : normSq (diskMoebius a z) = 1 := by
    rw [diskMoebius, normSq_div, hn, div_self (ne_of_gt (normSq_pos.mpr hden))]
  rw [normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (diskMoebius a z)]

theorem diskMoebius_eq_mul_conj_div {a z : ℂ} (hz : ‖z‖ = 1) :
    diskMoebius a z = z * conj (1 - conj a * z) / (1 - conj a * z) := by
  unfold diskMoebius
  congr 1
  have hc : z * conj z = 1 := by rw [mul_conj, normSq_eq_norm_sq, hz]; norm_num
  simp only [map_sub, map_one, map_mul, conj_conj]
  calc
    z - a = z - a * (z * conj z) := by rw [hc, mul_one]
    _ = z * (1 - a * conj z) := by ring

theorem diskMoebius_neg_apply {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskMoebius (-a) (diskMoebius a z) = z := by
  have hden := diskMoebius_denominator_ne_zero ha hz
  have ha' : ‖-a‖ < 1 := by simpa using ha
  have hinv := diskMoebius_denominator_ne_zero ha' (norm_diskMoebius_le_one ha hz)
  unfold diskMoebius at hinv ⊢
  simp only [map_neg, sub_neg_eq_add, neg_mul] at hinv ⊢
  apply (div_eq_iff hinv).mpr
  have hden' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hden
  field_simp [hden, hden']
  ring

theorem hasDerivAt_diskMoebius {a z : ℂ} (hz : 1 - conj a * z ≠ 0) :
    HasDerivAt (diskMoebius a) ((1 - normSq a) / (1 - conj a * z) ^ 2) z := by
  have hn : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have hd : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) z := by
    convert! (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj a)) using 1
    simp
  have h := hn.div hd hz
  convert! h using 1
  rw [← mul_conj a]
  ring

theorem hasDerivAt_const_mul_diskMoebius (η : ℂ) {a z : ℂ} (hz : 1 - conj a * z ≠ 0) :
    HasDerivAt (fun w => η * diskMoebius a w)
      (η * ((1 - normSq a) / (1 - conj a * z) ^ 2)) z :=
  (hasDerivAt_diskMoebius hz).const_mul η

theorem diskMoebius_sub {a z w : ℂ} (hz : 1 - conj a * z ≠ 0) (hw : 1 - conj a * w ≠ 0) :
    diskMoebius a z - diskMoebius a w =
      (1 - normSq a) * (z - w) / ((1 - conj a * z) * (1 - conj a * w)) := by
  unfold diskMoebius
  rw [← mul_conj a]
  have hz' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hz
  have hw' : 1 - w * conj a ≠ 0 := by simpa only [mul_comm] using hw
  field_simp [hz, hw, hz', hw']
  ring

theorem one_sub_norm_le_norm_diskMoebius_denominator {a z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - ‖a‖ ≤ ‖1 - conj a * z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (conj a * z)
  rw [norm_one, norm_mul, norm_conj] at h
  have hm := mul_le_of_le_one_right (norm_nonneg a) hz
  linarith

theorem dist_diskMoebius_le {a z w : ℂ} (ha : ‖a‖ < 1)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    dist (diskMoebius a z) (diskMoebius a w) ≤ (1 + ‖a‖) / (1 - ‖a‖) * dist z w := by
  have hzden := diskMoebius_denominator_ne_zero ha hz
  have hwden := diskMoebius_denominator_ne_zero ha hw
  have hza := one_sub_norm_le_norm_diskMoebius_denominator (a := a) hz
  have hwa := one_sub_norm_le_norm_diskMoebius_denominator (a := a) hw
  have ha0 := norm_nonneg a
  have hp : 0 < 1 - ‖a‖ := sub_pos.mpr ha
  have hs : 0 ≤ 1 - normSq a := by rw [normSq_eq_norm_sq]; nlinarith
  rw [dist_eq_norm, diskMoebius_sub hzden hwden, norm_div, norm_mul, norm_mul,
    ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    normSq_eq_norm_sq, dist_eq_norm]
  have hd : (1 - ‖a‖)^2 ≤ ‖1 - conj a * z‖ * ‖1 - conj a * w‖ := by
    nlinarith [mul_le_mul hza hwa hp.le (norm_nonneg (1 - conj a * z))]
  calc
    (1 - ‖a‖ ^ 2) * ‖z - w‖ / (‖1 - conj a * z‖ * ‖1 - conj a * w‖) ≤
        (1 - ‖a‖ ^ 2) * ‖z - w‖ / (1 - ‖a‖)^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (by nlinarith) (norm_nonneg _)) (sq_pos_of_pos hp) hd
    _ = (1 + ‖a‖) / (1 - ‖a‖) * ‖z - w‖ := by field_simp; ring

def diskAutomorphism (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 where
  toFun z := ⟨η * diskMoebius a z, by
    rw [mem_closedBall_zero_iff, norm_mul, hη, one_mul]
    exact norm_diskMoebius_le_one ha (mem_closedBall_zero_iff.mp z.property)⟩
  invFun z := ⟨diskMoebius (-a) (conj η * z), by
    rw [mem_closedBall_zero_iff]
    apply norm_diskMoebius_le_one (by simpa using ha)
    rw [norm_mul, norm_conj, hη, one_mul]
    exact mem_closedBall_zero_iff.mp z.property⟩
  left_inv z := by
    apply Subtype.ext
    dsimp
    have hc : conj η * η = 1 := by rw [mul_comm, mul_conj, normSq_eq_norm_sq, hη]; norm_num
    rw [← mul_assoc, hc, one_mul]
    exact diskMoebius_neg_apply ha (mem_closedBall_zero_iff.mp z.property)
  right_inv z := by
    apply Subtype.ext
    dsimp
    have hnorm : ‖conj η * (z : ℂ)‖ ≤ 1 := by
      rw [norm_mul, norm_conj, hη, one_mul]
      exact mem_closedBall_zero_iff.mp z.property
    have hinv := diskMoebius_neg_apply (a := -a) (by simpa using ha) hnorm
    simp only [neg_neg] at hinv
    rw [hinv, ← mul_assoc, mul_conj, normSq_eq_norm_sq, hη]
    norm_num
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_const.mul
    apply Continuous.div
    · exact continuous_subtype_val.sub continuous_const
    · exact continuous_const.sub (continuous_const.mul continuous_subtype_val)
    · intro z
      exact diskMoebius_denominator_ne_zero ha (mem_closedBall_zero_iff.mp z.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact (continuous_const.mul continuous_subtype_val).sub continuous_const
    · exact continuous_const.sub
        (continuous_const.mul (continuous_const.mul continuous_subtype_val))
    · intro z
      apply diskMoebius_denominator_ne_zero (by simpa using ha)
      rw [norm_mul, norm_conj, hη, one_mul]
      exact mem_closedBall_zero_iff.mp z.property

theorem coe_diskAutomorphism_apply (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1)
    (z : Metric.closedBall (0 : ℂ) 1) :
    (diskAutomorphism a η ha hη z : ℂ) = η * diskMoebius a z := rfl

theorem lipschitz_diskAutomorphism (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    LipschitzWith ⟨(1 + ‖a‖) / (1 - ‖a‖), by positivity⟩ (diskAutomorphism a η ha hη) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist (η * diskMoebius a z) (η * diskMoebius a w) ≤ _
  rw [dist_eq_norm, ← mul_sub, norm_mul, hη, one_mul, ← dist_eq_norm]
  exact dist_diskMoebius_le ha (mem_closedBall_zero_iff.mp z.property)
    (mem_closedBall_zero_iff.mp w.property)

theorem lipschitz_diskAutomorphism_symm (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    LipschitzWith ⟨(1 + ‖a‖) / (1 - ‖a‖), by positivity⟩ (diskAutomorphism a η ha hη).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hnorm (v : Metric.closedBall (0 : ℂ) 1) : ‖conj η * (v : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_conj, hη, one_mul]
    exact mem_closedBall_zero_iff.mp v.property
  have h := dist_diskMoebius_le (a := -a) (by simpa using ha) (hnorm z) (hnorm w)
  change dist (diskMoebius (-a) (conj η * (z : ℂ)))
    (diskMoebius (-a) (conj η * (w : ℂ))) ≤ (1 + ‖a‖) / (1 - ‖a‖) * dist (z : ℂ) (w : ℂ)
  convert! h using 1
  simp only [norm_neg, dist_eq_norm, ← mul_sub, norm_mul, norm_conj, hη, one_mul]

def diskAutomorphismCircle (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) : Circle ≃ₜ Circle where
  toFun z := ⟨η * diskMoebius a z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_mul, hη, one_mul]
    exact norm_diskMoebius_eq_one ha (Circle.norm_coe z)⟩
  invFun z := ⟨diskMoebius (-a) (conj η * z), by
    apply mem_sphere_zero_iff_norm.mpr
    apply norm_diskMoebius_eq_one (by simpa using ha)
    rw [norm_mul, norm_conj, hη, Circle.norm_coe, one_mul]⟩
  left_inv z := by
    apply Subtype.ext
    dsimp
    have hc : conj η * η = 1 := by rw [mul_comm, mul_conj, normSq_eq_norm_sq, hη]; norm_num
    rw [← mul_assoc, hc, one_mul]
    exact diskMoebius_neg_apply ha (Circle.norm_coe z).le
  right_inv z := by
    apply Subtype.ext
    dsimp
    have hn : ‖conj η * (z : ℂ)‖ ≤ 1 := by rw [norm_mul, norm_conj, hη, Circle.norm_coe, one_mul]
    have hi := diskMoebius_neg_apply (a := -a) (by simpa using ha) hn
    simp only [neg_neg] at hi
    rw [hi, ← mul_assoc, mul_conj, normSq_eq_norm_sq, hη]
    norm_num
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_const.mul
    apply Continuous.div
    · exact continuous_subtype_val.sub continuous_const
    · exact continuous_const.sub (continuous_const.mul continuous_subtype_val)
    · intro z
      exact diskMoebius_denominator_ne_zero ha (Circle.norm_coe z).le
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact (continuous_const.mul continuous_subtype_val).sub continuous_const
    · exact continuous_const.sub
        (continuous_const.mul (continuous_const.mul continuous_subtype_val))
    · intro z
      apply diskMoebius_denominator_ne_zero (by simpa using ha)
      rw [norm_mul, norm_conj, hη, Circle.norm_coe, one_mul]

theorem coe_diskAutomorphismCircle_apply (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1)
    (z : Circle) : (diskAutomorphismCircle a η ha hη z : ℂ) = η * diskMoebius a z := rfl

end Complex

end

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Set Function Metric
open scoped Topology
namespace DifferentialGeometry.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ballPrismScale (z : unitInterval × closedBall (0 : E) 1) : ℝ :=
  max ‖(z.2 : E)‖ (1 - z.1.val / 2)

omit [NormedSpace ℝ E] in
theorem half_le_ballPrismScale (z : unitInterval × closedBall (0 : E) 1) :
    (1 / 2 : ℝ) ≤ ballPrismScale z := by
  apply le_trans _ (le_max_right _ _)
  linarith [z.1.property.2]

omit [NormedSpace ℝ E] in
theorem ballPrismScale_pos (z : unitInterval × closedBall (0 : E) 1) : 0 < ballPrismScale z :=
  lt_of_lt_of_le (by norm_num) (half_le_ballPrismScale z)

omit [NormedSpace ℝ E] in
theorem continuous_ballPrismScale : Continuous (ballPrismScale (E := E)) :=
  continuous_norm.comp (continuous_subtype_val.comp continuous_snd) |>.max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2))

omit [NormedSpace ℝ E] in
theorem ballPrismScale_le_one (z : unitInterval × closedBall (0 : E) 1) :
    ballPrismScale z ≤ 1 := by
  apply max_le
  · simpa only [Metric.mem_closedBall, dist_zero_right] using z.2.property
  · linarith [z.1.property.1]

def ballPrismTime (z : unitInterval × closedBall (0 : E) 1) : unitInterval :=
  ⟨2 - (2 - z.1.val) / ballPrismScale z, by
    have hr := ballPrismScale_pos z
    have hlow : 1 - z.1.val / 2 ≤ ballPrismScale z := le_max_right _ _
    have hhigh := ballPrismScale_le_one z
    have hdiv0 : (2 - z.1.val) / ballPrismScale z ≤ 2 :=
      (div_le_iff₀ hr).mpr (by linarith)
    have hdiv1 : 1 ≤ (2 - z.1.val) / ballPrismScale z :=
      (le_div_iff₀ hr).mpr (by linarith [z.1.property.2])
    exact ⟨by linarith, by linarith⟩⟩

def ballPrismPosition (z : unitInterval × closedBall (0 : E) 1) : closedBall (0 : E) 1 :=
  ⟨(ballPrismScale z)⁻¹ • (z.2 : E), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
      Real.norm_of_nonneg (ballPrismScale_pos z).le]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ (ballPrismScale_pos z)).mpr (by
      simpa only [one_mul, ballPrismScale] using (le_max_left ‖(z.2 : E)‖ (1 - z.1.val / 2)))⟩

def ballPrismRetract (z : unitInterval × closedBall (0 : E) 1) :
    unitInterval × closedBall (0 : E) 1 := (ballPrismTime z, ballPrismPosition z)

theorem continuous_ballPrismRetract :
    Continuous (ballPrismRetract (E := E)) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_const.sub
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
        (continuous_ballPrismScale (E := E)) (fun z => (ballPrismScale_pos z).ne'))
  · apply Continuous.subtype_mk
    exact ((continuous_ballPrismScale (E := E)).inv₀
      (fun z => (ballPrismScale_pos z).ne')).smul
        (continuous_subtype_val.comp continuous_snd)

theorem ballPrismRetract_bottom (v : closedBall (0 : E) 1) :
    ballPrismRetract (0, v) = (0, v) := by
  have hs : ballPrismScale (0, v) = 1 := by
    change max ‖(v : E)‖ (1 - (0 : ℝ) / 2) = 1
    simpa only [zero_div, sub_zero] using
      max_eq_right (show ‖(v : E)‖ ≤ 1 by
        simpa only [Metric.mem_closedBall, dist_zero_right] using v.property)
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - (0 : ℝ)) / ballPrismScale (0, v) = 0
    rw [hs]
    norm_num
  · apply Subtype.ext
    change (ballPrismScale (0, v))⁻¹ • (v : E) = (v : E)
    rw [hs, inv_one, one_smul]

theorem ballPrismRetract_side (t : unitInterval) (v : closedBall (0 : E) 1)
    (hv : (v : E) ∈ sphere (0 : E) 1) : ballPrismRetract (t, v) = (t, v) := by
  have hn : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  have hs : ballPrismScale (t, v) = 1 := by
    change max ‖(v : E)‖ (1 - t.val / 2) = 1
    rw [hn]
    exact max_eq_left (by linarith [t.property.1])
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - t.val) / ballPrismScale (t, v) = t.val
    rw [hs]
    ring
  · apply Subtype.ext
    change (ballPrismScale (t, v))⁻¹ • (v : E) = (v : E)
    rw [hs, inv_one, one_smul]

theorem ballPrismRetract_time_zero (z : unitInterval × closedBall (0 : E) 1)
    (h : ‖(z.2 : E)‖ ≤ 1 - z.1.val / 2) : (ballPrismRetract z).1 = 0 := by
  have hr := ballPrismScale_pos z
  have hs : ballPrismScale z = 1 - z.1.val / 2 := max_eq_right h
  have hd : (2 - z.1.val) / ballPrismScale z = 2 :=
    (div_eq_iff hr.ne').mpr (by rw [hs]; ring)
  apply Subtype.ext
  change 2 - (2 - z.1.val) / ballPrismScale z = 0
  rw [hd, sub_self]

theorem ballPrismRetract_position_sphere (z : unitInterval × closedBall (0 : E) 1)
    (h : 1 - z.1.val / 2 ≤ ‖(z.2 : E)‖) :
    ((ballPrismRetract z).2 : E) ∈ sphere (0 : E) 1 := by
  have hr := ballPrismScale_pos z
  have hs : ballPrismScale z = ‖(z.2 : E)‖ := max_eq_left h
  apply mem_sphere_zero_iff_norm.mpr
  change ‖(ballPrismScale z)⁻¹ • (z.2 : E)‖ = 1
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, ← hs, inv_mul_cancel₀ hr.ne']

theorem ballPrismRetract_image (z : unitInterval × closedBall (0 : E) 1) :
    (ballPrismRetract z).1 = 0 ∨ ((ballPrismRetract z).2 : E) ∈ sphere (0 : E) 1 := by
  rcases le_total ‖(z.2 : E)‖ (1 - z.1.val / 2) with h | h
  · exact Or.inl (ballPrismRetract_time_zero z h)
  · exact Or.inr (ballPrismRetract_position_sphere z h)

theorem ballPrismRetract_idempotent (z : unitInterval × closedBall (0 : E) 1) :
    ballPrismRetract (ballPrismRetract z) = ballPrismRetract z := by
  rcases ballPrismRetract_image z with h | h
  · have heq : ballPrismRetract z = (0, (ballPrismRetract z).2) := Prod.ext h rfl
    rw [heq]
    exact ballPrismRetract_bottom _
  · exact ballPrismRetract_side _ _ h

end DifferentialGeometry.Topology

import DifferentialGeometry.Topology.Homotopy.CubeRadius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring







noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology


def cubePrismScale (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) : ℝ :=
  max (cubeRadius n z.2) (1 - z.1.val / 2)

theorem half_le_cubePrismScale (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    (1 / 2 : ℝ) ≤ cubePrismScale n z := by
  apply le_trans _ (le_max_right _ _)
  linarith [z.1.property.2]

theorem cubePrismScale_pos (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    0 < cubePrismScale n z := lt_of_lt_of_le (by norm_num) (half_le_cubePrismScale n z)

theorem cubePrismScale_le_one (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    cubePrismScale n z ≤ 1 :=
  max_le (cubeRadius_le_one n z.2) (by linarith [z.1.property.1])

theorem continuous_cubePrismScale (n : ℕ) : Continuous (cubePrismScale n) :=
  (continuous_cubeRadius n |>.comp continuous_snd).max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2))


def cubePrismTime (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) : unitInterval :=
  ⟨2 - (2 - z.1.val) / cubePrismScale n z, by
    have hr := cubePrismScale_pos n z
    have hlow : 1 - z.1.val / 2 ≤ cubePrismScale n z := le_max_right _ _
    have hhigh := cubePrismScale_le_one n z
    have hdiv0 : (2 - z.1.val) / cubePrismScale n z ≤ 2 :=
      (div_le_iff₀ hr).mpr (by linarith)
    have hdiv1 : 1 ≤ (2 - z.1.val) / cubePrismScale n z :=
      (le_div_iff₀ hr).mpr (by linarith [z.1.property.2])
    exact ⟨by linarith, by linarith⟩⟩


def cubePrismPosition (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    Fin (n + 1) → unitInterval := fun i =>
  ⟨((2 * (z.2 i).val - 1) / cubePrismScale n z + 1) / 2, by
    have hr := cubePrismScale_pos n z
    have hbound : |2 * (z.2 i).val - 1| ≤ cubePrismScale n z :=
      (cubeRadius_coordinate_le n z.2 i).trans (le_max_left _ _)
    have hb := abs_le.mp hbound
    have hlow : -1 ≤ (2 * (z.2 i).val - 1) / cubePrismScale n z :=
      (le_div_iff₀ hr).mpr (by linarith [hb.1])
    have hhigh : (2 * (z.2 i).val - 1) / cubePrismScale n z ≤ 1 :=
      (div_le_iff₀ hr).mpr (by linarith [hb.2])
    exact ⟨by linarith, by linarith⟩⟩


def cubePrismRetract (n : ℕ) (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    unitInterval × (Fin (n + 1) → unitInterval) := (cubePrismTime n z, cubePrismPosition n z)



theorem continuous_cubePrismRetract (n : ℕ) : Continuous (cubePrismRetract n) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_const.sub
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
        (continuous_cubePrismScale n) (fun z => (cubePrismScale_pos n z).ne'))
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_const.mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).sub continuous_const).div
        (continuous_cubePrismScale n) (fun z => (cubePrismScale_pos n z).ne')).add
          continuous_const |>.div_const 2


theorem cubePrismRetract_bottom (n : ℕ) (v : Fin (n + 1) → unitInterval) :
    cubePrismRetract n (0, v) = (0, v) := by
  have hs : cubePrismScale n (0, v) = 1 := by
    change max (cubeRadius n v) (1 - (0 : ℝ) / 2) = 1
    simpa only [zero_div, sub_zero] using max_eq_right (cubeRadius_le_one n v)
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - (0 : ℝ)) / cubePrismScale n (0, v) = 0
    rw [hs]
    norm_num
  · funext i
    apply Subtype.ext
    change ((2 * (v i).val - 1) / cubePrismScale n (0, v) + 1) / 2 = (v i).val
    rw [hs]
    ring


theorem cubePrismRetract_side (n : ℕ) (t : unitInterval)
    (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    cubePrismRetract n (t, v) = (t, v) := by
  have hs : cubePrismScale n (t, v) = 1 := by
    change max (cubeRadius n v) (1 - t.val / 2) = 1
    rw [(cubeRadius_eq_one_iff n v).mpr hv]
    exact max_eq_left (by linarith [t.property.1])
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - t.val) / cubePrismScale n (t, v) = t.val
    rw [hs]
    ring
  · funext i
    apply Subtype.ext
    change ((2 * (v i).val - 1) / cubePrismScale n (t, v) + 1) / 2 = (v i).val
    rw [hs]
    ring

end DifferentialGeometry.Topology

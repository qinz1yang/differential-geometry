import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace MetricSpace

variable {X : Type*}

@[simp] theorem rescale_one (m : MetricSpace X) : m.rescale 1 (by norm_num) = m := by
  apply MetricSpace.ext
  apply Dist.ext
  funext x y
  exact one_mul (@dist X m.toDist x y)

theorem rescale_mul (m : MetricSpace X) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (m.rescale a ha).rescale b hb = m.rescale (b * a) (mul_pos hb ha) := by
  apply MetricSpace.ext
  apply Dist.ext
  funext x y
  change b * (a * @dist X m.toDist x y) = (b * a) * @dist X m.toDist x y
  ring

theorem rescale_inv_ratio (m : MetricSpace X) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (m.rescale a⁻¹ (inv_pos.mpr ha)).rescale (b / a)⁻¹ (inv_pos.mpr (div_pos hb ha)) =
      m.rescale b⁻¹ (inv_pos.mpr hb) := by
  rw [rescale_mul]
  congr 1
  field_simp

end MetricSpace

namespace GC.MetricGeometry

theorem lipschitzWith_normalized_scale {X : Type*} [m : MetricSpace X]
    {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ) {p : X} (hp : 0 < ρ p) :
    let : MetricSpace X := m.rescale (ρ p)⁻¹ (inv_pos.mpr hp)
    LipschitzWith Λ (fun x => ρ x / ρ p) := by
  have hdiff (x y : X) : |ρ x - ρ y| ≤ Λ * dist x y := by
    simpa only [Real.dist_eq] using hρ.dist_le_mul x y
  let : MetricSpace X := m.rescale (ρ p)⁻¹ (inv_pos.mpr hp)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |ρ x / ρ p - ρ y / ρ p| ≤ Λ * ((ρ p)⁻¹ * @dist X m.toDist x y)
  rw [← sub_div, abs_div, abs_of_pos hp]
  have hh := hdiff x y
  calc
    _ ≤ ((Λ : ℝ) * @dist X m.toDist x y) / ρ p := div_le_div_of_nonneg_right hh hp.le
    _ = _ := by ring

end GC.MetricGeometry

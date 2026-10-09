import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry
open GC.Geometry.QuaternionPrismX127R3

namespace GC.Geometry.QuaternionPrismAxisSignX127

local notation "QH" => Quaternion ℝ
local notation "UQ" => unitary (Quaternion ℝ)

def axisI_X127 : QH := ⟨0, 1, 0, 0⟩

theorem j_flips_axisI_X127 :
    star (jUnit_X127 : QH) * axisI_X127 * (jUnit_X127 : QH) = -axisI_X127 := by
  have hjval : (jUnit_X127 : QH) = (⟨0, 0, 1, 0⟩ : QH) := rfl
  rw [hjval]
  apply Quaternion.ext <;> norm_num [axisI_X127]

private theorem character_fixes_axisI_X127 (n : ℕ) [NeZero n]
    (i : ZMod (2 * n)) :
    star (characterQ_X127 n i : QH) * axisI_X127 *
        (characterQ_X127 n i : QH) = axisI_X127 := by
  let a : UQ := characterQ_X127 n i
  have hunit : star (a : QH) * (a : QH) = 1 := a.property.1
  have hcomm : (a : QH) * axisI_X127 = axisI_X127 * (a : QH) := by
    apply Quaternion.ext <;>
      simp [a, axisI_X127, characterQ_X127, Quaternion.coeComplex]
  have hstarcomm : star (a : QH) * axisI_X127 =
      axisI_X127 * star (a : QH) := by
    apply Quaternion.ext <;>
      simp [a, axisI_X127, characterQ_X127, Quaternion.coeComplex]
  calc
    star (a : QH) * axisI_X127 * (a : QH) =
        (axisI_X127 * star (a : QH)) * (a : QH) := by rw [hstarcomm]
    _ = axisI_X127 * (star (a : QH) * (a : QH)) := by rw [mul_assoc]
    _ = axisI_X127 := by rw [hunit, mul_one]

theorem value_normalizes_axisI_X127 (n : ℕ) [NeZero n]
    (q : QuaternionGroup n) :
    star (value_X127 n q : QH) * axisI_X127 * (value_X127 n q : QH) =
        axisI_X127 ∨
      star (value_X127 n q : QH) * axisI_X127 * (value_X127 n q : QH) =
        -axisI_X127 := by
  cases q with
  | a i => exact Or.inl (character_fixes_axisI_X127 n i)
  | xa i =>
      right
      change star ((jUnit_X127 : QH) * (characterQ_X127 n i : QH)) *
        axisI_X127 * ((jUnit_X127 : QH) * (characterQ_X127 n i : QH)) =
          -axisI_X127
      rw [star_mul]
      have hj := j_flips_axisI_X127
      have ha := character_fixes_axisI_X127 n i
      calc
        (star (characterQ_X127 n i : QH) * star (jUnit_X127 : QH)) *
            axisI_X127 * ((jUnit_X127 : QH) * (characterQ_X127 n i : QH)) =
          (star (characterQ_X127 n i : QH) *
            (star (jUnit_X127 : QH) * axisI_X127 * (jUnit_X127 : QH))) *
              (characterQ_X127 n i : QH) := by noncomm_ring
        _ = (star (characterQ_X127 n i : QH) * (-axisI_X127)) *
              (characterQ_X127 n i : QH) := by rw [hj]
        _ = -axisI_X127 := by
          calc
            (star (characterQ_X127 n i : QH) * (-axisI_X127)) *
                (characterQ_X127 n i : QH) =
              -(star (characterQ_X127 n i : QH) * axisI_X127 *
                (characterQ_X127 n i : QH)) := by noncomm_ring
            _ = -axisI_X127 := by rw [ha]

end GC.Geometry.QuaternionPrismAxisSignX127

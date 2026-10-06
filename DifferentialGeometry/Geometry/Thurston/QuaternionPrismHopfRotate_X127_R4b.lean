import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismAxisSign_X127_R3b
import DifferentialGeometry.Geometry.Thurston.QuaternionAmbientHopf_X127
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry
open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismAxisSignX127
open GC.Geometry.QuaternionProjectiveX127

namespace GC.Geometry.QuaternionPrismHopfRotateX127

local notation "QH" => Quaternion ℝ
local notation "UQ" => unitary (Quaternion ℝ)

def halfRoot_X127 : ℝ := Real.sqrt (1 / 2)

theorem halfRoot_sq_X127 : halfRoot_X127 ^ 2 = 1 / 2 := by
  rw [halfRoot_X127, Real.sq_sqrt (by norm_num)]

def rotateValue_X127 : QH := ⟨halfRoot_X127, 0, -halfRoot_X127, 0⟩

def rotateUnit_X127 : UQ :=
  ⟨rotateValue_X127, by
    rw [Unitary.mem_iff]
    have hnormSq : Quaternion.normSq rotateValue_X127 = 1 := by
      rw [Quaternion.normSq_def']
      simp [rotateValue_X127, halfRoot_sq_X127]
      norm_num
    exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
      by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩

theorem rotate_axis_X127 :
    star (rotateUnit_X127 : QH) * quaternionEightHopfAxis_X127 *
      (rotateUnit_X127 : QH) = axisI_X127 := by
  apply Quaternion.ext <;>
    simp [rotateUnit_X127, rotateValue_X127, quaternionEightHopfAxis_X127,
      axisI_X127]
  nlinarith [halfRoot_sq_X127]

end GC.Geometry.QuaternionPrismHopfRotateX127

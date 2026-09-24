import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

theorem rotation_exp_circleMap (α θ : ℝ) :
    rotation (Circle.exp α) (circleMap 0 1 θ) = circleMap 0 1 (α + θ) := by
  simp [rotation_apply, Circle.coe_exp, circleMap, Complex.exp_add, add_mul]

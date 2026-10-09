import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
open scoped NNReal

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

def radialConeKernel (p x y : X) : ℝ :=
  (dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) / 2

structure RadialConeData (p : X) where
  map : ℝ≥0 → X → X
  map_zero : ∀ x, map 0 x = p
  map_one : ∀ x, map 1 x = x
  dist_sq : ∀ (s t : ℝ≥0) (x y : X),
    dist (map s x) (map t y) ^ 2 =
      (s : ℝ) ^ 2 * dist p x ^ 2 + (t : ℝ) ^ 2 * dist p y ^ 2 -
        2 * (s : ℝ) * (t : ℝ) * radialConeKernel p x y

theorem radialConeKernel_self (p x : X) : radialConeKernel p x x = dist p x ^ 2 := by
  simp only [radialConeKernel, dist_self, zero_pow (by decide : 2 ≠ 0)]
  ring

theorem radialConeKernel_comm (p x y : X) : radialConeKernel p x y = radialConeKernel p y x := by
  unfold radialConeKernel
  rw [dist_comm x y]
  ring

theorem radialConeKernel_bounds (p x y : X) :
    -(dist p x * dist p y) ≤ radialConeKernel p x y ∧
      radialConeKernel p x y ≤ dist p x * dist p y := by
  have hu : dist x y ≤ dist p x + dist p y := by
    simpa only [dist_comm x p] using dist_triangle x p y
  have hl : |dist p x - dist p y| ≤ dist x y := by
    apply abs_le.mpr
    constructor
    · have hh := dist_triangle p x y
      linarith
    · have hh := dist_triangle p y x
      rw [dist_comm y x] at hh
      linarith
  have hus := (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr hu
  have hls := (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mpr hl
  rw [sq_abs] at hls
  unfold radialConeKernel
  constructor <;> nlinarith

end GC.MetricGeometry

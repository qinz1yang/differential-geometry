import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric
import Mathlib.Topology.MetricSpace.ProperSpace

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem cosh_dist_origin (x : Hyperboloid E) :
    Real.cosh (dist origin x) = x.time := by
  simp [cosh_dist]

@[simp] theorem sinh_dist_origin (x : Hyperboloid E) :
    Real.sinh (dist origin x) = ‖x.space‖ := by
  have hs := Real.cosh_sq_sub_sinh_sq (dist origin x)
  rw [cosh_dist_origin] at hs
  nlinarith [norm_nonneg x.space, Real.sinh_nonneg_iff.mpr (dist_nonneg (x := origin) (y := x)),
    x.time_sq]

theorem closedBall_origin (r : ℝ) :
    Metric.closedBall (origin : Hyperboloid E) r =
      space ⁻¹' Metric.closedBall 0 (Real.sinh r) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
    ← sinh_dist_origin x, Real.sinh_le_sinh, dist_comm x origin]

instance [ProperSpace E] : ProperSpace (Hyperboloid E) := by
  apply ProperSpace.of_seq_closedBall (x := (origin : Hyperboloid E))
    (r := fun r : ℝ => r) Filter.tendsto_id
  exact Filter.Eventually.of_forall fun r => by
    rw [closedBall_origin]
    exact (spaceHomeomorph (E := E)).isCompact_preimage.mpr (isCompact_closedBall 0 (Real.sinh r))

end DifferentialGeometry.Hyperboloid

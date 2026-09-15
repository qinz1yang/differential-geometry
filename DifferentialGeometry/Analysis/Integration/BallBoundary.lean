import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Restrict

open Metric

namespace MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {c : X} {r : ℝ}

theorem ae_mem_ball_of_measure_sphere_eq_zero (h : μ (sphere c r) = 0) :
    ∀ᵐ x ∂μ.restrict (closedBall c r), x ∈ ball c r := by
  have hzero : ∀ᵐ x ∂μ, x ∉ sphere c r := by
    rw [ae_iff]
    convert h using 1
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, not_not]
  filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hzero] with x hx hxn
  exact lt_of_le_of_ne hx hxn

end MeasureTheory

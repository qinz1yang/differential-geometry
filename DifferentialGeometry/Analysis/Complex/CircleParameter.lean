import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Real.Pi.Bounds

section

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Analysis

theorem exists_circle_parameter_eq_of_mem_sphere {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) R) :
    ∃ t ∈ Icc (0 : ℝ) 1, circleMap 0 R (2 * Real.pi * t - Real.pi) = z := by
  have hmem : z ∈ range (circleMap 0 R) := by
    rw [range_circleMap]
    simpa only [abs_of_pos hR] using hz
  rw [← (periodic_circleMap 0 R).image_Ioc Real.two_pi_pos (-Real.pi)] at hmem
  obtain ⟨θ, hθ, hθz⟩ := hmem
  refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hθ.1]) (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [hθ.2])
  · have heq : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
      field_simp
      ring
    rwa [heq]

end DifferentialGeometry.Analysis

end

end

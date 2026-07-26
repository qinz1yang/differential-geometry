import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammExp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact terminal-time power integral for Koch--Lamm

This file evaluates the one-dimensional singular integral left by the
terminal heat-kernel `L^p` calculation.  It also records the two exponent
identities that expose the cancelling `R^(4/(n+4))` scale.
-/

noncomputable section

open MeasureTheory Real Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Adding one to the terminal kernel-power singularity leaves exponent
`2/(n+2)`. -/
theorem klHeatExp_add :
    klHeatExp V + 1 =
      2 / (Module.finrank ℝ V + 2 : ℝ) := by
  rw [klHeatExp_eq]
  have hn2 : (Module.finrank ℝ V : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn2]
  ring

/-- After taking the Hölder-dual root, the terminal time scale is
`t^(2/(n+4))`. -/
theorem klTermScale_exp :
    (klHeatExp V + 1) / klQDual V =
      2 / (Module.finrank ℝ V + 4 : ℝ) := by
  rw [klHeatExp_add]
  unfold klQDual
  have hn2 : (Module.finrank ℝ V : ℝ) + 2 ≠ 0 := by positivity
  have hn4 : (Module.finrank ℝ V : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hn2, hn4]

/-- Exact integral of the reflected terminal kernel-power singularity on
the terminal half interval. -/
theorem klTermTime_int (t : ℝ) :
    ∫ s : ℝ in t / 2..t, (t - s) ^ klHeatExp V =
      (t / 2) ^ (klHeatExp V + 1) / (klHeatExp V + 1) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ ↦ u ^ klHeatExp V) t]
  simp only [sub_self]
  rw [show t - t / 2 = t / 2 by ring]
  rw [integral_rpow (Or.inl (klHeatExp_gt (V := V)))]
  have hexp : 0 < klHeatExp V + 1 := by
    linarith [klHeatExp_gt (V := V)]
  rw [Real.zero_rpow hexp.ne']
  ring

/-- Set-integral form used by the restricted terminal product measure. -/
theorem klTermTime_set {t : ℝ} (ht : 0 < t) :
    ∫ s : ℝ in Set.Ioc (t / 2) t, (t - s) ^ klHeatExp V =
      (t / 2) ^ (klHeatExp V + 1) / (klHeatExp V + 1) := by
  rw [← intervalIntegral.integral_of_le (by linarith : t / 2 ≤ t)]
  exact klTermTime_int (V := V) t

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end

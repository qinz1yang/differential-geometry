import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Exponents
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory Real Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem kochLammHeatExp_add :
    kochLammHeatExp V + 1 =
      2 / (Module.finrank ℝ V + 2 : ℝ) := by
  rw [kochLammHeatExp_eq]
  have hn2 : (Module.finrank ℝ V : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn2]
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammTermScale_exp :
    (kochLammHeatExp V + 1) / kochLammQDual V =
      2 / (Module.finrank ℝ V + 4 : ℝ) := by
  rw [kochLammHeatExp_add]
  unfold kochLammQDual
  have hn2 : (Module.finrank ℝ V : ℝ) + 2 ≠ 0 := by positivity
  have hn4 : (Module.finrank ℝ V : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hn2, hn4]

omit [FiniteDimensional ℝ V] in
theorem kochLammTermTime_int (t : ℝ) :
    ∫ s : ℝ in t / 2..t, (t - s) ^ kochLammHeatExp V =
      (t / 2) ^ (kochLammHeatExp V + 1) / (kochLammHeatExp V + 1) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ ↦ u ^ kochLammHeatExp V) t]
  simp only [sub_self]
  rw [show t - t / 2 = t / 2 by ring]
  rw [integral_rpow (Or.inl (kochLammHeatExp_gt (V := V)))]
  have hexp : 0 < kochLammHeatExp V + 1 := by
    linarith [kochLammHeatExp_gt (V := V)]
  rw [Real.zero_rpow hexp.ne']
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammTermTime_set {t : ℝ} (ht : 0 < t) :
    ∫ s : ℝ in Set.Ioc (t / 2) t, (t - s) ^ kochLammHeatExp V =
      (t / 2) ^ (kochLammHeatExp V + 1) / (kochLammHeatExp V + 1) := by
  rw [← intervalIntegral.integral_of_le (by linarith : t / 2 ≤ t)]
  exact kochLammTermTime_int (V := V) t

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end

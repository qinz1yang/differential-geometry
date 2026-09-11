import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Spaces
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def kochLammQReal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / 2

def kochLammQDual (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / (Module.finrank ℝ V + 2 : ℝ)

def kochLammHeatExp (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    : ℝ :=
  (Module.finrank ℝ V : ℝ) * (1 - kochLammQDual V) / 2

omit [FiniteDimensional ℝ V] in
theorem kochLammQReal_ofReal : ENNReal.ofReal (kochLammQReal V) = kochLammQ V := by
  unfold kochLammQReal kochLammQ kochLammP
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show (Module.finrank ℝ V : ℝ) + 4 =
      ((Module.finrank ℝ V + 4 : ℕ) : ℝ) by norm_num]
  rw [ENNReal.ofReal_natCast]
  norm_num

omit [FiniteDimensional ℝ V] in
theorem kochLammQ_holder : (kochLammQDual V).HolderConjugate (kochLammQReal V) := by
  let n : ℝ := Module.finrank ℝ V
  have hn2 : 0 < n + 2 := by
    dsimp [n]
    positivity
  have hn4 : 0 < n + 4 := by
    dsimp [n]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold kochLammQDual kochLammQReal
    change ((n + 4) / (n + 2))⁻¹ + ((n + 4) / 2)⁻¹ = (1 : ℝ)⁻¹
    field_simp [hn2.ne', hn4.ne']
    ring
  · unfold kochLammQDual
    exact div_pos hn4 hn2
  · unfold kochLammQReal
    positivity

omit [FiniteDimensional ℝ V] in
theorem kochLammHeatExp_eq :
    kochLammHeatExp V =
      -(Module.finrank ℝ V : ℝ) / (Module.finrank ℝ V + 2 : ℝ) := by
  unfold kochLammHeatExp kochLammQDual
  have hn2 : (Module.finrank ℝ V : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn2]
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammHeatExp_gt : -1 < kochLammHeatExp V := by
  rw [kochLammHeatExp_eq]
  have hn2 : 0 < (Module.finrank ℝ V : ℝ) + 2 := by positivity
  rw [show -(Module.finrank ℝ V : ℝ) /
      (Module.finrank ℝ V + 2 : ℝ) =
        -((Module.finrank ℝ V : ℝ) /
          (Module.finrank ℝ V + 2 : ℝ)) by ring]
  rw [neg_lt_neg_iff]
  exact (div_lt_one hn2).2 (by linarith)

omit [FiniteDimensional ℝ V] in
theorem kochLammTimePow_intble {t : ℝ} :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ kochLammHeatExp V)
      volume (t / 2) t := by
  have hbase : IntervalIntegrable (fun u : ℝ ↦ u ^ kochLammHeatExp V)
      volume 0 (t / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (kochLammHeatExp_gt (V := V))
  have href := hbase.symm.comp_sub_left t
  convert href using 1 <;> ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end

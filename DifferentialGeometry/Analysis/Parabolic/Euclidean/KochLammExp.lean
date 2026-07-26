import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real exponents for the late Koch--Lamm heat estimate

The ordinary-source late exponent is `q = (n+4)/2`.  Its spatial Hölder
conjugate is `p = (n+4)/(n+2)`.  Raising the heat kernel to this `p` produces
the time power `-n/(n+2)`, which is strictly greater than `-1`; hence it is
integrable on the terminal half of a Duhamel interval.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Real form of the late ordinary-source exponent `(n+4)/2`. -/
def klQReal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / 2

/-- Spatial Hölder conjugate of `klQReal`. -/
def klQDual (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / (Module.finrank ℝ V + 2 : ℝ)

/-- Time exponent in the exact `klQDual`-power heat-kernel mass. -/
def klHeatExp (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Module.finrank ℝ V : ℝ) * (1 - klQDual V) / 2

/-- `klQReal` is exactly the real representative of the existing `ENNReal`
late-source exponent. -/
theorem klQReal_ofReal : ENNReal.ofReal (klQReal V) = klQ V := by
  unfold klQReal klQ klP
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show (Module.finrank ℝ V : ℝ) + 4 =
      ((Module.finrank ℝ V + 4 : ℕ) : ℝ) by norm_num]
  rw [ENNReal.ofReal_natCast]
  norm_num

/-- The late source exponent and heat-kernel exponent are Hölder conjugate. -/
theorem klQ_holder : (klQDual V).HolderConjugate (klQReal V) := by
  let n : ℝ := Module.finrank ℝ V
  have hn2 : 0 < n + 2 := by
    dsimp [n]
    positivity
  have hn4 : 0 < n + 4 := by
    dsimp [n]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold klQDual klQReal
    change ((n + 4) / (n + 2))⁻¹ + ((n + 4) / 2)⁻¹ = (1 : ℝ)⁻¹
    field_simp [hn2.ne', hn4.ne']
    ring
  · unfold klQDual
    exact div_pos hn4 hn2
  · unfold klQReal
    positivity

/-- The heat-kernel power simplifies to `-n/(n+2)`. -/
theorem klHeatExp_eq :
    klHeatExp V =
      -(Module.finrank ℝ V : ℝ) / (Module.finrank ℝ V + 2 : ℝ) := by
  unfold klHeatExp klQDual
  have hn2 : (Module.finrank ℝ V : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn2]
  ring

/-- The terminal heat-kernel time singularity is locally integrable. -/
theorem klHeatExp_gt : -1 < klHeatExp V := by
  rw [klHeatExp_eq]
  have hn2 : 0 < (Module.finrank ℝ V : ℝ) + 2 := by positivity
  rw [show -(Module.finrank ℝ V : ℝ) /
      (Module.finrank ℝ V + 2 : ℝ) =
        -((Module.finrank ℝ V : ℝ) /
          (Module.finrank ℝ V + 2 : ℝ)) by ring]
  rw [neg_lt_neg_iff]
  exact (div_lt_one hn2).2 (by linarith)

/-- The reflected kernel-power singularity is integrable on the terminal
half of every positive Duhamel interval. -/
theorem klTimePow_intble {t : ℝ} (_ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ klHeatExp V)
      volume (t / 2) t := by
  have hbase : IntervalIntegrable (fun u : ℝ ↦ u ^ klHeatExp V)
      volume 0 (t / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (klHeatExp_gt (V := V))
  have href := hbase.symm.comp_sub_left t
  convert href using 1 <;> ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end

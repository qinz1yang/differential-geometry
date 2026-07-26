import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real exponents for the late Koch--Lamm flux estimate

The late divergence-source exponent is `p = n + 4`.  Its Hölder conjugate is
`p' = (n+4)/(n+3)`.  A first spatial heat derivative raised to `p'` has the
time exponent `-(n+2)/(n+3)`, which is locally integrable and leaves exactly
the Koch--Lamm radius factor `R^(2/(n+4))` after taking the dual root.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Real form of the late divergence-source exponent `n + 4`. -/
def klPReal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  Module.finrank ℝ V + 4

/-- Hölder conjugate of `klPReal`. -/
def klPDual (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / (Module.finrank ℝ V + 3 : ℝ)

/-- Time exponent in the exact `klPDual`-power first-derivative kernel mass. -/
def klD1Exp (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  ((Module.finrank ℝ V : ℝ) * (1 - klPDual V) - klPDual V) / 2

/-- `klPReal` is the real representative of the existing `ENNReal` late
flux exponent. -/
theorem klPReal_ofReal : ENNReal.ofReal (klPReal V) = klP V := by
  unfold klPReal klP
  rw [show (Module.finrank ℝ V : ℝ) + 4 =
      ((Module.finrank ℝ V + 4 : ℕ) : ℝ) by norm_num]
  rw [ENNReal.ofReal_natCast]

/-- The late flux exponent and first-derivative kernel exponent are Hölder
conjugate. -/
theorem klP_holder : (klPDual V).HolderConjugate (klPReal V) := by
  let n : ℝ := Module.finrank ℝ V
  have hn3 : 0 < n + 3 := by
    dsimp [n]
    positivity
  have hn4 : 0 < n + 4 := by
    dsimp [n]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold klPDual klPReal
    change ((n + 4) / (n + 3))⁻¹ + (n + 4)⁻¹ = (1 : ℝ)⁻¹
    field_simp [hn3.ne', hn4.ne']
    ring
  · unfold klPDual
    exact div_pos hn4 hn3
  · unfold klPReal
    positivity

/-- The first-derivative dual exponent is at least one. -/
theorem klPDual_one : 1 ≤ klPDual V :=
  (klP_holder (V := V)).lt.le

/-- The first-derivative dual exponent lies in the `L¹ ∩ L²` interpolation
range used by `baseD1Maj_rpow`. -/
theorem klPDual_two : klPDual V ≤ 2 := by
  unfold klPDual
  have hn : 0 ≤ (Module.finrank ℝ V : ℝ) := by positivity
  have hn3 : 0 < (Module.finrank ℝ V : ℝ) + 3 := by positivity
  apply (div_le_iff₀ hn3).2
  linarith

/-- The first-derivative kernel power has exponent `-(n+2)/(n+3)`. -/
theorem klD1Exp_eq :
    klD1Exp V =
      -(Module.finrank ℝ V + 2 : ℝ) /
        (Module.finrank ℝ V + 3 : ℝ) := by
  unfold klD1Exp klPDual
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn3]
  ring

/-- The terminal first-derivative kernel singularity is locally integrable. -/
theorem klD1Exp_gt : -1 < klD1Exp V := by
  rw [klD1Exp_eq]
  have hn3 : 0 < (Module.finrank ℝ V : ℝ) + 3 := by positivity
  rw [show -(Module.finrank ℝ V + 2 : ℝ) /
      (Module.finrank ℝ V + 3 : ℝ) =
        -((Module.finrank ℝ V + 2 : ℝ) /
          (Module.finrank ℝ V + 3 : ℝ)) by ring]
  rw [neg_lt_neg_iff]
  exact (div_lt_one hn3).2 (by linarith)

/-- Adding one to the first-derivative kernel singularity leaves exponent
`1/(n+3)`. -/
theorem klD1Exp_add :
    klD1Exp V + 1 =
      1 / (Module.finrank ℝ V + 3 : ℝ) := by
  rw [klD1Exp_eq]
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn3]
  ring

/-- After taking the Hölder-dual root, the terminal heat-time scale is
`t^(1/(n+4))`. -/
theorem klD1Scale_exp :
    (klD1Exp V + 1) / klPDual V =
      1 / (Module.finrank ℝ V + 4 : ℝ) := by
  rw [klD1Exp_add]
  unfold klPDual
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  have hn4 : (Module.finrank ℝ V : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hn3, hn4]

/-- Exact integral of the reflected first-derivative kernel-power
singularity on the terminal half interval. -/
theorem klD1Time_int (t : ℝ) :
    ∫ s : ℝ in t / 2..t, (t - s) ^ klD1Exp V =
      (t / 2) ^ (klD1Exp V + 1) / (klD1Exp V + 1) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ ↦ u ^ klD1Exp V) t]
  simp only [sub_self]
  rw [show t - t / 2 = t / 2 by ring]
  rw [integral_rpow (Or.inl (klD1Exp_gt (V := V)))]
  have hexp : 0 < klD1Exp V + 1 := by
    linarith [klD1Exp_gt (V := V)]
  rw [Real.zero_rpow hexp.ne']
  ring

/-- Set-integral form used by the restricted terminal product measure. -/
theorem klD1Time_set {t : ℝ} (ht : 0 < t) :
    ∫ s : ℝ in Set.Ioc (t / 2) t, (t - s) ^ klD1Exp V =
      (t / 2) ^ (klD1Exp V + 1) / (klD1Exp V + 1) := by
  rw [← intervalIntegral.integral_of_le (by linarith : t / 2 ≤ t)]
  exact klD1Time_int (V := V) t

/-- The reflected first-derivative kernel-power singularity is integrable on
the terminal half of every positive Duhamel interval. -/
theorem klD1Time_intble {t : ℝ} (_ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ klD1Exp V)
      volume (t / 2) t := by
  have hbase : IntervalIntegrable (fun u : ℝ ↦ u ^ klD1Exp V)
      volume 0 (t / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (klD1Exp_gt (V := V))
  have href := hbase.symm.comp_sub_left t
  convert href using 1 <;> ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end

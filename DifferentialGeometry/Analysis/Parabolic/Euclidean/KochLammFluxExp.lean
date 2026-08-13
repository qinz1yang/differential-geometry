import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def klPReal (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  Module.finrank ℝ V + 4

def klPDual (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / (Module.finrank ℝ V + 3 : ℝ)

def klD1Exp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  ((Module.finrank ℝ V : ℝ) * (1 - klPDual V) - klPDual V) / 2

theorem klPReal_ofReal : ENNReal.ofReal (klPReal V) = klP V := by
  unfold klPReal klP
  rw [show (Module.finrank ℝ V : ℝ) + 4 =
      ((Module.finrank ℝ V + 4 : ℕ) : ℝ) by norm_num]
  rw [ENNReal.ofReal_natCast]

theorem klPDual_holder : (klPDual V).HolderConjugate (klPReal V) := by
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

theorem klPDual_one : 1 ≤ klPDual V :=
  (klPDual_holder (V := V)).lt.le

theorem klPDual_two : klPDual V ≤ 2 := by
  unfold klPDual
  have hn : 0 ≤ (Module.finrank ℝ V : ℝ) := by positivity
  have hn3 : 0 < (Module.finrank ℝ V : ℝ) + 3 := by positivity
  apply (div_le_iff₀ hn3).2
  linarith

theorem klD1Exp_eq :
    klD1Exp V =
      -(Module.finrank ℝ V + 2 : ℝ) /
        (Module.finrank ℝ V + 3 : ℝ) := by
  unfold klD1Exp klPDual
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn3]
  ring

theorem klD1Exp_gt : -1 < klD1Exp V := by
  rw [klD1Exp_eq]
  have hn3 : 0 < (Module.finrank ℝ V : ℝ) + 3 := by positivity
  rw [show -(Module.finrank ℝ V + 2 : ℝ) /
      (Module.finrank ℝ V + 3 : ℝ) =
        -((Module.finrank ℝ V + 2 : ℝ) /
          (Module.finrank ℝ V + 3 : ℝ)) by ring]
  rw [neg_lt_neg_iff]
  exact (div_lt_one hn3).2 (by linarith)

theorem klD1Exp_add :
    klD1Exp V + 1 =
      1 / (Module.finrank ℝ V + 3 : ℝ) := by
  rw [klD1Exp_eq]
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn3]
  ring

theorem klD1Scale_exp :
    (klD1Exp V + 1) / klPDual V =
      1 / (Module.finrank ℝ V + 4 : ℝ) := by
  rw [klD1Exp_add]
  unfold klPDual
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  have hn4 : (Module.finrank ℝ V : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hn3, hn4]

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

theorem klD1Time_set {t : ℝ} (ht : 0 < t) :
    ∫ s : ℝ in Set.Ioc (t / 2) t, (t - s) ^ klD1Exp V =
      (t / 2) ^ (klD1Exp V + 1) / (klD1Exp V + 1) := by
  rw [← intervalIntegral.integral_of_le (by linarith : t / 2 ≤ t)]
  exact klD1Time_int (V := V) t

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

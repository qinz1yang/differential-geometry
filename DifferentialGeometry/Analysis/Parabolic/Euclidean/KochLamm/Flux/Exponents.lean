import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Spaces
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

def kochLammPReal (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    : ℝ :=
  Module.finrank ℝ V + 4

def kochLammPDual (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    : ℝ :=
  (Module.finrank ℝ V + 4 : ℝ) / (Module.finrank ℝ V + 3 : ℝ)

def kochLammD1Exp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    : ℝ :=
  ((Module.finrank ℝ V : ℝ) * (1 - kochLammPDual V) - kochLammPDual V) / 2

omit [FiniteDimensional ℝ V] in
theorem kochLammPReal_ofReal : ENNReal.ofReal (kochLammPReal V) = kochLammP V := by
  unfold kochLammPReal kochLammP
  rw [show (Module.finrank ℝ V : ℝ) + 4 =
      ((Module.finrank ℝ V + 4 : ℕ) : ℝ) by norm_num]
  rw [ENNReal.ofReal_natCast]

omit [FiniteDimensional ℝ V] in
theorem kochLammPDual_holder : (kochLammPDual V).HolderConjugate (kochLammPReal V) := by
  let n : ℝ := Module.finrank ℝ V
  have hn3 : 0 < n + 3 := by
    dsimp [n]
    positivity
  have hn4 : 0 < n + 4 := by
    dsimp [n]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold kochLammPDual kochLammPReal
    change ((n + 4) / (n + 3))⁻¹ + (n + 4)⁻¹ = (1 : ℝ)⁻¹
    field_simp [hn3.ne', hn4.ne']
    ring
  · unfold kochLammPDual
    exact div_pos hn4 hn3
  · unfold kochLammPReal
    positivity

omit [FiniteDimensional ℝ V] in
theorem kochLammPDual_one : 1 ≤ kochLammPDual V :=
  (kochLammPDual_holder (V := V)).lt.le

omit [FiniteDimensional ℝ V] in
theorem kochLammPDual_two : kochLammPDual V ≤ 2 := by
  unfold kochLammPDual
  have hn : 0 ≤ (Module.finrank ℝ V : ℝ) := by positivity
  have hn3 : 0 < (Module.finrank ℝ V : ℝ) + 3 := by positivity
  apply (div_le_iff₀ hn3).2
  linarith

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Exp_eq :
    kochLammD1Exp V =
      -(Module.finrank ℝ V + 2 : ℝ) /
        (Module.finrank ℝ V + 3 : ℝ) := by
  unfold kochLammD1Exp kochLammPDual
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn3]
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Exp_gt : -1 < kochLammD1Exp V := by
  rw [kochLammD1Exp_eq]
  have hn3 : 0 < (Module.finrank ℝ V : ℝ) + 3 := by positivity
  rw [show -(Module.finrank ℝ V + 2 : ℝ) /
      (Module.finrank ℝ V + 3 : ℝ) =
        -((Module.finrank ℝ V + 2 : ℝ) /
          (Module.finrank ℝ V + 3 : ℝ)) by ring]
  rw [neg_lt_neg_iff]
  exact (div_lt_one hn3).2 (by linarith)

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Exp_add :
    kochLammD1Exp V + 1 =
      1 / (Module.finrank ℝ V + 3 : ℝ) := by
  rw [kochLammD1Exp_eq]
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn3]
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Scale_exp :
    (kochLammD1Exp V + 1) / kochLammPDual V =
      1 / (Module.finrank ℝ V + 4 : ℝ) := by
  rw [kochLammD1Exp_add]
  unfold kochLammPDual
  have hn3 : (Module.finrank ℝ V : ℝ) + 3 ≠ 0 := by positivity
  have hn4 : (Module.finrank ℝ V : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hn3, hn4]

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Time_int (t : ℝ) :
    ∫ s : ℝ in t / 2..t, (t - s) ^ kochLammD1Exp V =
      (t / 2) ^ (kochLammD1Exp V + 1) / (kochLammD1Exp V + 1) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ ↦ u ^ kochLammD1Exp V) t]
  simp only [sub_self]
  rw [show t - t / 2 = t / 2 by ring]
  rw [integral_rpow (Or.inl (kochLammD1Exp_gt (V := V)))]
  have hexp : 0 < kochLammD1Exp V + 1 := by
    linarith [kochLammD1Exp_gt (V := V)]
  rw [Real.zero_rpow hexp.ne']
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Time_set {t : ℝ} (ht : 0 < t) :
    ∫ s : ℝ in Set.Ioc (t / 2) t, (t - s) ^ kochLammD1Exp V =
      (t / 2) ^ (kochLammD1Exp V + 1) / (kochLammD1Exp V + 1) := by
  rw [← intervalIntegral.integral_of_le (by linarith : t / 2 ≤ t)]
  exact kochLammD1Time_int (V := V) t

omit [FiniteDimensional ℝ V] in
theorem kochLammD1Time_intble {t : ℝ} :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ kochLammD1Exp V)
      volume (t / 2) t := by
  have hbase : IntervalIntegrable (fun u : ℝ ↦ u ^ kochLammD1Exp V)
      volume 0 (t / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (kochLammD1Exp_gt (V := V))
  have href := hbase.symm.comp_sub_left t
  convert href using 1 <;> ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end

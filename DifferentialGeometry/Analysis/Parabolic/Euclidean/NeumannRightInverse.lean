import DifferentialGeometry.Analysis.Calculus.CLMNeumann
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RetractionParametrix
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem idAdd_isUnit [CompleteSpace Y]
    (B : Y →L[ℝ] Y) (hB : ‖B‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℝ Y + B) := by
  have hneg : ‖-B‖ < 1 := by simpa only [norm_neg]
  have hu := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
  simpa only [sub_neg_eq_add, ContinuousLinearMap.one_def] using hu

def neumannInv (B : Y →L[ℝ] Y) : Y →L[ℝ] Y :=
  Ring.inverse (ContinuousLinearMap.id ℝ Y + B)

theorem neumannInv_right [CompleteSpace Y]
    (B : Y →L[ℝ] Y) (hB : ‖B‖ < 1) :
    (ContinuousLinearMap.id ℝ Y + B).comp (neumannInv B) =
      ContinuousLinearMap.id ℝ Y := by
  rw [neumannInv, ← ContinuousLinearMap.mul_def]
  exact (Ring.mul_inverse_cancel _ (idAdd_isUnit B hB)).trans
    ContinuousLinearMap.one_def

theorem neumannInv_left [CompleteSpace Y]
    (B : Y →L[ℝ] Y) (hB : ‖B‖ < 1) :
    (neumannInv B).comp (ContinuousLinearMap.id ℝ Y + B) =
      ContinuousLinearMap.id ℝ Y := by
  rw [neumannInv, ← ContinuousLinearMap.mul_def]
  exact (Ring.inverse_mul_cancel _ (idAdd_isUnit B hB)).trans
    ContinuousLinearMap.one_def

theorem splitError_lt_half
    (B₂ B₁₀ : Y →L[ℝ] Y)
    (hB₂ : ‖B₂‖ ≤ (1 : ℝ) / 4)
    (hB₁₀ : ‖B₁₀‖ < (1 : ℝ) / 4) :
    ‖B₂ + B₁₀‖ < (1 : ℝ) / 2 := by
  calc
    ‖B₂ + B₁₀‖ ≤ ‖B₂‖ + ‖B₁₀‖ := norm_add_le _ _
    _ < (1 : ℝ) / 2 := by linarith

def correctedParametrix
    (Q : Y →L[ℝ] X) (B : Y →L[ℝ] Y) : Y →L[ℝ] X :=
  Q.comp (neumannInv B)

theorem corrected_right_inv [CompleteSpace Y]
    (T : X →L[ℝ] Y) (Q : Y →L[ℝ] X) (B : Y →L[ℝ] Y)
    (hTQ : T.comp Q = ContinuousLinearMap.id ℝ Y + B)
    (hB : ‖B‖ < 1) :
    T.comp (correctedParametrix Q B) = ContinuousLinearMap.id ℝ Y := by
  rw [correctedParametrix, ← ContinuousLinearMap.comp_assoc, hTQ]
  exact neumannInv_right B hB

theorem split_right_inv [CompleteSpace Y]
    (T : X →L[ℝ] Y) (Q : Y →L[ℝ] X) (B₂ B₁₀ : Y →L[ℝ] Y)
    (hTQ : T.comp Q = ContinuousLinearMap.id ℝ Y + (B₂ + B₁₀))
    (hB₂ : ‖B₂‖ ≤ (1 : ℝ) / 4)
    (hB₁₀ : ‖B₁₀‖ < (1 : ℝ) / 4) :
    T.comp (correctedParametrix Q (B₂ + B₁₀)) =
      ContinuousLinearMap.id ℝ Y := by
  apply corrected_right_inv T Q (B₂ + B₁₀) hTQ
  exact (splitError_lt_half B₂ B₁₀ hB₂ hB₁₀).trans
    (by norm_num)

end DifferentialGeometry.Analysis.Parabolic.Euclidean

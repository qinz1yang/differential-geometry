import DifferentialGeometry.Analysis.Calculus.CLMNeumann
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RetractionParametrix
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Neumann correction of an approximate right inverse

If `TQ = id + B` and the error endomorphism has norm less than one, the
canonical geometric-series unit for `1 - (-B)` supplies an exact right
inverse `Q (id + B)⁻¹`.  The formulation here permits the solution and data
spaces to be different, as they are in maximal regularity.
-/

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The small perturbation `id + B = 1 - (-B)` is a unit in the Banach
algebra of continuous linear endomorphisms. -/
theorem idAdd_isUnit [CompleteSpace Y]
    (B : Y →L[ℝ] Y) (hB : ‖B‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℝ Y + B) := by
  have hneg : ‖-B‖ < 1 := by simpa only [norm_neg]
  have hu := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
  simpa only [sub_neg_eq_add, ContinuousLinearMap.one_def] using hu

/-- The canonical ring inverse of `id + B`.  Under `‖B‖ < 1` this is the
Neumann-series inverse supplied by `isUnit_one_sub_of_norm_lt_one`. -/
def neumannInv (B : Y →L[ℝ] Y) : Y →L[ℝ] Y :=
  Ring.inverse (ContinuousLinearMap.id ℝ Y + B)

/-- The Neumann inverse cancels `id + B` on the right. -/
theorem neumannInv_right [CompleteSpace Y]
    (B : Y →L[ℝ] Y) (hB : ‖B‖ < 1) :
    (ContinuousLinearMap.id ℝ Y + B).comp (neumannInv B) =
      ContinuousLinearMap.id ℝ Y := by
  rw [neumannInv, ← ContinuousLinearMap.mul_def]
  exact (Ring.mul_inverse_cancel _ (idAdd_isUnit B hB)).trans
    ContinuousLinearMap.one_def

/-- The Neumann inverse also cancels `id + B` on the left. -/
theorem neumannInv_left [CompleteSpace Y]
    (B : Y →L[ℝ] Y) (hB : ‖B‖ < 1) :
    (neumannInv B).comp (ContinuousLinearMap.id ℝ Y + B) =
      ContinuousLinearMap.id ℝ Y := by
  rw [neumannInv, ← ContinuousLinearMap.mul_def]
  exact (Ring.inverse_mul_cancel _ (idAdd_isUnit B hB)).trans
    ContinuousLinearMap.one_def

/-- A quarter-sized principal error plus a strictly quarter-sized
first/zero-order error has norm strictly less than one half. -/
theorem splitError_lt_half
    (B₂ B₁₀ : Y →L[ℝ] Y)
    (hB₂ : ‖B₂‖ ≤ (1 : ℝ) / 4)
    (hB₁₀ : ‖B₁₀‖ < (1 : ℝ) / 4) :
    ‖B₂ + B₁₀‖ < (1 : ℝ) / 2 := by
  calc
    ‖B₂ + B₁₀‖ ≤ ‖B₂‖ + ‖B₁₀‖ := norm_add_le _ _
    _ < (1 : ℝ) / 2 := by linarith

/-- The Neumann-corrected parametrix. -/
def correctedParametrix
    (Q : Y →L[ℝ] X) (B : Y →L[ℝ] Y) : Y →L[ℝ] X :=
  Q.comp (neumannInv B)

/-- If `TQ = id + B` and `‖B‖ < 1`, the corrected parametrix is an exact
right inverse for `T`. -/
theorem corrected_right_inv [CompleteSpace Y]
    (T : X →L[ℝ] Y) (Q : Y →L[ℝ] X) (B : Y →L[ℝ] Y)
    (hTQ : T.comp Q = ContinuousLinearMap.id ℝ Y + B)
    (hB : ‖B‖ < 1) :
    T.comp (correctedParametrix Q B) = ContinuousLinearMap.id ℝ Y := by
  rw [correctedParametrix, ← ContinuousLinearMap.comp_assoc, hTQ]
  exact neumannInv_right B hB

/-- The exact split parametrix identity and the quarter bounds directly
produce an exact right inverse. -/
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

import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped BigOperators

theorem standardScalar3_standardRmDiag3 (l1 l2 l3 : ℝ) :
    standardScalar3 (standardRmDiag3 l1 l2 l3) = l1 + l2 + l3 := by
  unfold standardScalar3 standardRicci3 standardRmDiag3 ricciDiag3 ricciEigenScalar3 delta3
  simp
  ring

theorem standardRicci3_standardRmDiag3_diag (l1 l2 l3 : ℝ) (i : Fin 3) :
    standardRicci3 (standardRmDiag3 l1 l2 l3) i i =
      (if i = 0 then l1 else if i = 1 then l2 else l3) := by
  unfold standardRicci3 standardRmDiag3 ricciDiag3 ricciEigenScalar3 delta3
  fin_cases i <;> simp <;> ring

theorem standardRmNormSq3_standardRmDiag3 (l1 l2 l3 : ℝ) :
    standardRmNormSq3 (standardRmDiag3 l1 l2 l3) =
      (l1 + l2 - l3) ^ 2 + (l1 + l3 - l2) ^ 2 + (l2 + l3 - l1) ^ 2 := by
  rw [standardRmNormSq3_diag]
  unfold rmSecNormSq3 sec12Ric3 sec13Ric3 sec23Ric3
  ring

theorem standardScalar3_standardRmDiag3_roundSphere :
    standardScalar3 (standardRmDiag3 (1 / 3) (1 / 3) (1 / 3)) = 1 := by
  rw [standardScalar3_standardRmDiag3]
  norm_num

theorem standardRmNormSq3_standardRmDiag3_roundSphere :
    standardRmNormSq3 (standardRmDiag3 (1 / 3) (1 / 3) (1 / 3)) = 1 / 3 := by
  rw [standardRmNormSq3_standardRmDiag3]
  norm_num

theorem standardScalar3_standardRmDiag3_saddle :
    standardScalar3 (standardRmDiag3 (1 / 5) (-(1 / 10)) (-(1 / 10))) = 0 := by
  rw [standardScalar3_standardRmDiag3]
  norm_num

theorem standardRmNormSq3_standardRmDiag3_saddle :
    standardRmNormSq3 (standardRmDiag3 (1 / 5) (-(1 / 10)) (-(1 / 10))) = 6 / 25 := by
  rw [standardRmNormSq3_standardRmDiag3]
  norm_num

theorem standardRicci3_standardRmDiag3_saddle_negative :
    standardRicci3 (standardRmDiag3 (1 / 5) (-(1 / 10)) (-(1 / 10))) 1 1 < 0 := by
  rw [standardRicci3_standardRmDiag3_diag]
  norm_num

theorem standardRicci3_standardRmDiag3_roundSphere_nonnegative :
    ∀ i : Fin 3, 0 ≤ standardRicci3 (standardRmDiag3 (1 / 3) (1 / 3) (1 / 3)) i i := by
  intro i
  rw [standardRicci3_standardRmDiag3_diag]
  fin_cases i <;> norm_num

theorem not_ricciNonnegative_of_scalarBound_and_rmNormBound :
    (∃ R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ,
        standardScalar3 R ≤ 1 ∧ standardRmNormSq3 R ≤ 1 / 3 ∧ standardRicci3 R 1 1 < 0) ∧
      (∃ R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ,
        standardScalar3 R ≤ 1 ∧ standardRmNormSq3 R ≤ 1 / 3 ∧
          ∀ i : Fin 3, 0 ≤ standardRicci3 R i i) := by
  constructor
  · refine ⟨standardRmDiag3 (1 / 5) (-(1 / 10)) (-(1 / 10)), ?_, ?_,
      standardRicci3_standardRmDiag3_saddle_negative⟩
    · rw [standardScalar3_standardRmDiag3_saddle]
      norm_num
    · rw [standardRmNormSq3_standardRmDiag3_saddle]
      norm_num
  · refine ⟨standardRmDiag3 (1 / 3) (1 / 3) (1 / 3), ?_, ?_,
      standardRicci3_standardRmDiag3_roundSphere_nonnegative⟩
    · rw [standardScalar3_standardRmDiag3_roundSphere]
    · rw [standardRmNormSq3_standardRmDiag3_roundSphere]

end DifferentialGeometry.Geometry.Curvature

import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

open Real Set
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Toponogov


abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)


private def unitRay (t : ℝ) : EuclideanPlane :=
  EuclideanSpace.single 0 (Real.cos t) + EuclideanSpace.single 1 (Real.sin t)

private theorem inner_unitRay (s t : ℝ) :
    inner ℝ (unitRay s) (unitRay t) = Real.cos (s - t) := by
  simp [unitRay, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    Real.cos_sub]

private theorem norm_unitRay (t : ℝ) : ‖unitRay t‖ = 1 := by
  have hsq : ‖unitRay t‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_unitRay]
    simp
  nlinarith [norm_nonneg (unitRay t)]

private theorem angle_unitRay_zero {t : ℝ} (ht₀ : 0 ≤ t) (htπ : t ≤ Real.pi) :
    InnerProductGeometry.angle (unitRay 0) (unitRay t) = t := by
  rw [InnerProductGeometry.angle, inner_unitRay, norm_unitRay, norm_unitRay]
  simp only [zero_sub, Real.cos_neg, one_mul, div_one]
  rw [Real.arccos_cos ht₀ htπ]

private theorem angle_unitRay_add {s t : ℝ} (ht₀ : 0 ≤ t) (htπ : t ≤ Real.pi) :
    InnerProductGeometry.angle (unitRay s) (unitRay (s + t)) = t := by
  rw [InnerProductGeometry.angle, inner_unitRay, norm_unitRay, norm_unitRay]
  simp only [one_mul, sub_add_cancel_left, Real.cos_neg, div_one]
  rw [Real.arccos_cos ht₀ htπ]

theorem exists_euclideanSector_interpolation {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsum : A + B < Real.pi) :
    ∃ O X Y Z : EuclideanPlane,
      dist O X = 1 ∧ dist O Z = 1 ∧ 0 < dist O Y ∧ dist O Y ≤ 1 ∧
        Y ∈ segment ℝ X Z ∧
          InnerProductGeometry.angle (X - O) (Y - O) = A ∧
          InnerProductGeometry.angle (Y - O) (Z - O) = B := by
  rcases eq_or_lt_of_le hA with hA_zero | hA_pos
  · subst A
    have hB_pi : B ≤ Real.pi := by linarith
    refine ⟨0, unitRay 0, unitRay 0, unitRay B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [dist_zero_left, norm_unitRay]
    · simp only [dist_zero_left, norm_unitRay]
    · simp only [dist_zero_left, norm_unitRay, zero_lt_one]
    · simp only [dist_zero_left, norm_unitRay, le_refl]
    · exact left_mem_segment ℝ _ _
    · simpa only [sub_zero] using
        (angle_unitRay_zero (t := (0 : ℝ)) le_rfl Real.pi_pos.le)
    · simpa only [sub_zero] using angle_unitRay_zero hB hB_pi
  · rcases eq_or_lt_of_le hB with hB_zero | hB_pos
    · subst B
      have hA_pi : A ≤ Real.pi := by linarith
      refine ⟨0, unitRay 0, unitRay A, unitRay A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [dist_zero_left, norm_unitRay]
      · simp only [dist_zero_left, norm_unitRay]
      · simp only [dist_zero_left, norm_unitRay, zero_lt_one]
      · simp only [dist_zero_left, norm_unitRay, le_refl]
      · exact right_mem_segment ℝ _ _
      · simpa only [sub_zero] using angle_unitRay_zero hA hA_pi
      · simpa only [sub_zero, add_zero] using
          (angle_unitRay_add (s := A) (t := (0 : ℝ)) le_rfl Real.pi_pos.le)
    · have hA_pi : A ≤ Real.pi := by linarith
      have hB_pi : B ≤ Real.pi := by linarith
      have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA_pos (by linarith)
      have hsinB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB_pos (by linarith)
      have hsinSum : 0 < Real.sin (A + B) :=
        Real.sin_pos_of_pos_of_lt_pi (add_pos hA_pos hB_pos) hsum
      let denominator : ℝ := Real.sin A + Real.sin B
      let t : ℝ := Real.sin A / denominator
      let radius : ℝ := Real.sin (A + B) / denominator
      have hdenominator : 0 < denominator := by
        dsimp only [denominator]
        positivity
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact (div_pos hsinA hdenominator).le
        · exact (div_le_one hdenominator).2 (by
            dsimp only [denominator]
            linarith)
      have hradius : 0 < radius := div_pos hsinSum hdenominator
      let X : EuclideanPlane := unitRay 0
      let Z : EuclideanPlane := unitRay (A + B)
      let Y : EuclideanPlane := AffineMap.lineMap X Z t
      have hY : Y = radius • unitRay A := by
        ext i
        fin_cases i
        · dsimp only [Y, X, Z, t, radius, denominator]
          simp [AffineMap.lineMap_apply_module, unitRay]
          field_simp [hdenominator.ne']
          rw [Real.sin_add, Real.cos_add]
          nlinarith [Real.sin_sq_add_cos_sq A]
        · dsimp only [Y, X, Z, t, radius, denominator]
          simp [AffineMap.lineMap_apply_module, unitRay]
          field_simp [hdenominator.ne']
      have hY_segment : Y ∈ segment ℝ X Z := lineMap_mem_segment ℝ X Z ht
      have hY_norm_le : ‖Y‖ ≤ 1 := by
        rw [show Y = (1 - t) • X + t • Z by
          exact AffineMap.lineMap_apply_module X Z t]
        calc
          ‖(1 - t) • X + t • Z‖ ≤ ‖(1 - t) • X‖ + ‖t • Z‖ := norm_add_le _ _
          _ = (1 - t) * 1 + t * 1 := by
            rw [norm_smul, norm_smul]
            simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2),
              abs_of_nonneg ht.1, X, Z, norm_unitRay]
          _ = 1 := by ring
      refine ⟨0, X, Y, Z, ?_, ?_, ?_, ?_, hY_segment, ?_, ?_⟩
      · simp only [dist_zero_left, X, norm_unitRay]
      · simp only [dist_zero_left, Z, norm_unitRay]
      · rw [dist_zero_left, hY, norm_smul, norm_unitRay, mul_one, Real.norm_eq_abs,
          abs_of_pos hradius]
        exact hradius
      · simpa only [dist_zero_left] using hY_norm_le
      · simp only [sub_zero, X, hY]
        rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hradius]
        exact angle_unitRay_zero hA hA_pi
      · simp only [sub_zero, Z, hY]
        rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hradius]
        exact angle_unitRay_add hB hB_pi

end DifferentialGeometry.Toponogov

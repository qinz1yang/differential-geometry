import DifferentialGeometry.Analysis.FiniteDimensional.BilinearPositivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A bilinear Hessian negative on the tangent kernel becomes negative definite after
a sufficiently large negative conormal square, as in the correction u-Cu².
-/

set_option autoImplicit false

noncomputable section

open Set Metric NormedSpace
open scoped Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

theorem exists_boundary_hessian_correction (B : E →L[ℝ] E →L[ℝ] ℝ) (l : E →L[ℝ] ℝ)
    (hB : ∀ v : E, l v = 0 → v ≠ 0 → B v v < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E, v ≠ 0 → B v v - 2 * C * (l v) ^ 2 < 0 := by
  have hcont : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  let K : Set E := sphere (0 : E) 1 ∩ {v : E | 0 ≤ B v v}
  have hK : IsCompact K :=
    (isCompact_sphere (0 : E) 1).inter_right (isClosed_le continuous_const hcont)
  have hreduce {C : ℝ}
      (hunit : ∀ v : E, ‖v‖ = 1 → B v v - 2 * C * (l v) ^ 2 < 0) :
      ∀ v : E, v ≠ 0 → B v v - 2 * C * (l v) ^ 2 < 0 := by
    intro v hv
    have hform : B v v - 2 * C * (l v) ^ 2 =
        ‖v‖ ^ 2 * (B (normalize v) (normalize v) - 2 * C * (l (normalize v)) ^ 2) := by
      conv_lhs => rw [← norm_smul_normalize v]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hform]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (norm_pos_iff.mpr hv))
      (hunit (normalize v) (norm_normalize hv))
  by_cases hne : K.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne (l.continuous.pow 2).continuousOn
    have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by
      rw [mem_sphere_zero_iff_norm.mp hw.1]
      exact one_ne_zero)
    have hlw : l w ≠ 0 := fun hz => (not_lt_of_ge hw.2) (hB w hz hw0)
    have hδ : 0 < (l w) ^ 2 := sq_pos_of_ne_zero hlw
    let C : ℝ := (‖B‖ + 1) / (2 * (l w) ^ 2)
    have hc : 0 < C := div_pos (by positivity) (by positivity)
    have hCδ : 2 * C * (l w) ^ 2 = ‖B‖ + 1 := by
      dsimp only [C]
      field_simp
    refine ⟨C, hc, hreduce ?_⟩
    intro v hv
    by_cases hb : 0 ≤ B v v
    · have hminv : (l w) ^ 2 ≤ (l v) ^ 2 :=
        hmin ⟨mem_sphere_zero_iff_norm.mpr hv, hb⟩
      have hbound : B v v ≤ ‖B‖ := by
        have hn := B.le_opNorm₂ v v
        rw [Real.norm_eq_abs, hv, mul_one, mul_one] at hn
        exact (le_abs_self _).trans hn
      nlinarith [mul_le_mul_of_nonneg_left hminv (by positivity : 0 ≤ 2 * C)]
    · have hbneg := lt_of_not_ge hb
      nlinarith [sq_nonneg (l v)]
  · refine ⟨1, zero_lt_one, hreduce ?_⟩
    intro v hv
    have hb : B v v < 0 := by
      by_contra hn
      exact hne ⟨v, mem_sphere_zero_iff_norm.mpr hv, le_of_not_gt hn⟩
    nlinarith [sq_nonneg (l v)]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

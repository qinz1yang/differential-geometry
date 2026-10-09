import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace IsometryEquiv

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace P] [NormedAddTorsor E P]

include E in
theorem apply_apply_ne_of_no_fixed_point (f : P ≃ᵢ P) (hf : ∀ x, f x ≠ x) (x : P) :
    f (f x) ≠ x := by
  intro h
  apply hf (midpoint ℝ (V := E) x (f x))
  rw [f.map_midpoint (E := E), h, midpoint_comm]

theorem apply_apply_eq_add_of_no_fixed_point (f : ℂ ≃ᵢ ℂ)
    (hf : ∀ z, f z ≠ z) (z : ℂ) : f (f z) = z + f (f 0) := by
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f.toRealLinearIsometryEquiv
  · have he (w : ℂ) : f w = (a : ℂ) * w + f 0 := by
      have h := congrArg (fun g : ℂ ≃ₗᵢ[ℝ] ℂ => g w) ha
      rw [toRealLinearIsometryEquiv_apply, rotation_apply] at h
      exact sub_eq_iff_eq_add.mp h
    have ha1 : (a : ℂ) = 1 := by
      by_contra hne
      apply hf (f 0 / (1 - (a : ℂ)))
      rw [he]
      field_simp [sub_ne_zero.mpr (Ne.symm hne)]
      ring
    rw [he (f z), he z, he (f 0), ha1]
    ring
  · have he (w : ℂ) : f w = (a : ℂ) * starRingEnd ℂ w + f 0 := by
      have h := congrArg (fun g : ℂ ≃ₗᵢ[ℝ] ℂ => g w) ha
      simp only [toRealLinearIsometryEquiv_apply, LinearIsometryEquiv.trans_apply,
        rotation_apply, Complex.conjLIE_apply] at h
      exact sub_eq_iff_eq_add.mp h
    have hu : (a : ℂ) * starRingEnd ℂ (a : ℂ) = 1 := by
      rw [Complex.mul_conj]
      simp
    rw [he (f z), he z, he (f 0)]
    simp only [map_add, map_mul, starRingEnd_self_apply]
    calc
      (a : ℂ) * (starRingEnd ℂ (a : ℂ) * z + starRingEnd ℂ (f 0)) + f 0 =
          ((a : ℂ) * starRingEnd ℂ (a : ℂ)) * z +
            ((a : ℂ) * starRingEnd ℂ (f 0) + f 0) := by ring
      _ = z + ((a : ℂ) * starRingEnd ℂ (f 0) + f 0) := by rw [hu, one_mul]

end IsometryEquiv

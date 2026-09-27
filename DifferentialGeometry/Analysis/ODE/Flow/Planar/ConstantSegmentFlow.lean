import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem integralCurve_eq_translation_in_constant_halfSpace_of_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E → E} (hv : ContDiff ℝ ∞ v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hfixed : ∀ x, b ≤ ℓ x → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (s t : ℝ)
    (ht : b ≤ ℓ (γ t)) (hend : b ≤ ℓ (γ t + (s - t) • c)) :
    γ s = γ t + (s - t) • c := by
  let η : ℝ → E := fun r ↦ γ (t + r * (s - t))
  let ξ : ℝ → E := fun r ↦ γ t + (r * (s - t)) • c
  let w : E → E := fun x ↦ (s - t) • v x
  have hw : ContDiff ℝ ∞ w := contDiff_const.smul hv
  have hη (r : ℝ) : HasDerivAt η (w (η r)) r := by
    simpa only [η, w, Function.comp_def, mul_one, one_mul, zero_add, id_eq] using
      (hγ (t + r * (s - t))).scomp r
        (((hasDerivAt_id r).mul_const (s - t)).const_add t)
  have hξmem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : b ≤ ℓ (ξ r) := by
    have he : ℓ (ξ r) = (1 - r) * ℓ (γ t) + r * ℓ (γ t + (s - t) • c) := by
      simp only [ξ, map_add, map_smul, smul_eq_mul]
      ring
    rw [he]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr ht),
      mul_nonneg hr.1 (sub_nonneg.mpr hend)]
  have hξ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : HasDerivAt ξ (w (ξ r)) r := by
    rw [show w (ξ r) = (s - t) • c from congrArg ((s - t) • ·) (hfixed _ (hξmem r hr))]
    simpa only [ξ, one_mul, id_eq] using
      ((((hasDerivAt_id r).mul_const (s - t)).smul_const c).const_add (γ t))
  have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hw
    (a := 0) (b := 1) (fun r _ ↦ (hη r).hasDerivWithinAt)
    (fun r hr ↦ (hξ r hr).hasDerivWithinAt) (by simp [η, ξ])
  simpa only [η, ξ, one_mul, add_sub_cancel] using he ⟨zero_le_one, le_rfl⟩

end DifferentialGeometry.Analysis

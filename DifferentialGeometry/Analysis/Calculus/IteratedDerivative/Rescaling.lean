import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_smul_comp_smul_of_ne_zero
    (f : E → F) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fun y => b • f (a • y)) x =
      (b * a ^ j) • iteratedFDeriv ℝ j f (a • x) := by
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  let B : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (Units.mk0 b hb)
  have hinput : iteratedFDeriv ℝ j (f ∘ A) x =
      (iteratedFDeriv ℝ j f (A x)).compContinuousLinearMap
        (fun _ : Fin j => A.toContinuousLinearMap) := by
    have h := A.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
      (show A x ∈ Set.univ from Set.mem_univ _) j
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using h
  have houtput := B.iteratedFDeriv_comp_left (f := f ∘ A) (x := x) (i := j)
  rw [hinput] at houtput
  calc
    iteratedFDeriv ℝ j (fun y => b • f (a • y)) x =
        iteratedFDeriv ℝ j (B ∘ (f ∘ A)) x := rfl
    _ = B.toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ j f (A x)).compContinuousLinearMap
          (fun _ : Fin j => A.toContinuousLinearMap)) := houtput
    _ = (b * a ^ j) • iteratedFDeriv ℝ j f (a • x) := by
      ext v
      change b • ((iteratedFDeriv ℝ j f (a • x)) (fun i => a • v i)) =
        (b * a ^ j) • ((iteratedFDeriv ℝ j f (a • x)) v)
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]

theorem norm_iteratedFDeriv_rescale
    (f : E → F) (r : ℝ) (hr : 0 < r) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => r⁻¹ • f (r • y)) (r⁻¹ • x)‖ =
      (r⁻¹ * r ^ j) * ‖iteratedFDeriv ℝ j f x‖ := by
  rw [iteratedFDeriv_smul_comp_smul_of_ne_zero f r r⁻¹ hr.ne' (inv_ne_zero hr.ne')]
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  simp only [norm_smul, norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hr]

end DifferentialGeometry.Analysis

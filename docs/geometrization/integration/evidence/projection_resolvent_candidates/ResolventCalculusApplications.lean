import DifferentialGeometry.Analysis.Calculus.Resolvent
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionResolvent
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace ResolventCalculusApplications

private theorem avoids_real_spectrum (x : ℝ) :
    Complex.I ∈ resolventSet ℂ (Complex.ofRealCLM x) := by
  change IsUnit (Complex.I - (x : ℂ))
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

example : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => resolvent (Complex.ofRealCLM x) Complex.I) :=
  Complex.ofRealCLM.contDiff.resolvent avoids_real_spectrum

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => resolvent (Complex.ofRealCLM y) Complex.I)
      (resolvent (Complex.ofRealCLM x) Complex.I ^ 2) x := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := x)).resolvent (avoids_real_spectrum x)
  simpa [ContinuousLinearMap.mulLeftRight_apply, pow_two] using h.hasDerivAt

example : ContDiffWithinAt ℝ 3
    (fun x : ℝ => resolvent (Complex.ofRealCLM x) Complex.I) (Set.Ici 0) 0 :=
  Complex.ofRealCLM.contDiff.contDiffWithinAt.resolvent (avoids_real_spectrum 0)

example (x : ℝ) :
    ‖fderiv ℝ (fun y : ℝ => resolvent (Complex.ofRealCLM y) Complex.I) x‖ ≤
      ‖resolvent (Complex.ofRealCLM x) Complex.I‖ ^ 2 * ‖fderiv ℝ Complex.ofRealCLM x‖ :=
  Complex.ofRealCLM.differentiableAt.norm_fderiv_resolvent_le (avoids_real_spectrum x)

private def D : ℝ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℂ ℂ)
private def A (t : ℝ) : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ + D t
private theorem close (t : ℝ) (ht : t ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) :
    ‖A t - (⊤ : Submodule ℂ ℂ).starProjection‖ ≤ (1 / 4 : ℝ) := by
  simpa [A, D, Submodule.starProjection_top, norm_smul] using
    (abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩ : |t| ≤ (1 / 4 : ℝ))
private theorem smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) A := contDiff_const.add D.contDiff
private theorem invertible (t : ℝ) (ht : t ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) :
    (3 / 2 : ℂ) ∈ resolventSet ℂ (A t) :=
  ContinuousLinearMap.mem_resolventSet_of_norm_sub_starProjection_lt (A t) ⊤
    ((close t ht).trans_lt (by norm_num))

example : ContDiffOn ℝ (↑(⊤ : ℕ∞))
    (fun t => resolvent (A t) (3 / 2 : ℂ)) (Set.Ioo (-1 / 4 : ℝ) (1 / 4)) :=
  smooth.contDiffOn.resolvent invertible

example (t : ℝ) (ht : t ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) :
    ‖fderiv ℝ (fun u => resolvent (A u) (3 / 2 : ℂ)) t‖ ≤ 16 := by
  have hres := ContinuousLinearMap.norm_resolvent_le_of_norm_sub_starProjection_le (A t) ⊤
    (μ := (3 / 2 : ℂ)) (close t ht) (by norm_num)
  norm_num at hres
  have hd : fderiv ℝ A t = D := by
    simpa [A] using! ((hasFDerivAt_const (ContinuousLinearMap.id ℂ ℂ) t).add D.hasFDerivAt).fderiv
  have hn : ‖D‖ = 1 := by simp [D, ContinuousLinearMap.norm_smulRight_apply]
  have h := (smooth.differentiable (by simp)).differentiableAt.norm_fderiv_resolvent_le (invertible t ht)
  rw [hd, hn, mul_one] at h
  nlinarith [norm_nonneg (resolvent (A t) (3 / 2 : ℂ))]

end ResolventCalculusApplications

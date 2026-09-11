import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_of_contDiffOn
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφc hφs
  let v := EuclideanSpace.single i (1 : ℝ)
  have hdφs : tsupport (fun x => fderiv ℝ φ x v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφs
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x v) := hφc.fderiv_apply (𝕜 := ℝ) v
  have hdc : ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint₁ : Integrable (fun x => fderiv ℝ f x v * φ x) :=
    ((hdc.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  have hint₂ : Integrable (fun x => f x * fderiv ℝ φ x v) :=
    ((hf.continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hdφs)).integrable_of_hasCompactSupport hdφc.mul_left
  have hint₃ : Integrable (fun x => f x * φ x) :=
    ((hf.continuousOn.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint₁ hint₂ hint₃
      (fun x hx => ((hf x (hφs hx)).contDiffAt (hΩ.mem_nhds (hφs hx))).differentiableAt
        one_ne_zero)
      (fun x _ => (hφ.differentiable (by simp)) x)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)), mul_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hdφs h)), mul_zero]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

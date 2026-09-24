import DifferentialGeometry.Analysis.Sobolev.Euclidean.LocallyLipschitz.ChainRule

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_exp_neg_add_const_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (c : ℝ) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => -Real.exp (-f x + c) * fderiv ℝ f x (EuclideanSpace.single i 1))
      (fun x => Real.exp (-f x + c)) Ω := by
  simpa only [Pi.smul_apply, smul_eq_mul, Real.exp_add, mul_neg, neg_mul,
    mul_assoc, mul_comm, mul_left_comm] using
      (hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn hΩ hΩc hf i).const_smul
        (Real.exp c)

theorem memLp_exp_neg_add_const_mul_fderiv_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f)
    (c : ℝ) (p : ℝ≥0∞) (i : Fin d) :
    MemLp (fun x => -Real.exp (-f x + c) * fderiv ℝ f x (EuclideanSpace.single i 1))
      p (volume.restrict Ω) := by
  simpa only [Real.exp_add, mul_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm] using
    (memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn hΩ hΩc hf p i).const_mul
      (Real.exp c)

theorem fderiv_exp_neg_add_const_ae_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (c : ℝ) (i : Fin d) :
    (fun x => fderiv ℝ (fun y => Real.exp (-f y + c)) x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
        (fun x => -Real.exp (-f x + c) * fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  filter_upwards [ae_restrict_mem hΩ.measurableSet,
    (hC.mono subset_closure).ae_differentiableWithinAt (μ := volume) hΩ.measurableSet]
      with x hx hdx
  have hd : DifferentiableAt ℝ f x := hdx.differentiableAt (hΩ.mem_nhds hx)
  simpa only [Pi.neg_apply, smul_apply, neg_apply, smul_eq_mul, mul_neg, neg_mul] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (hd.hasFDerivAt.neg.add_const c).exp.fderiv

theorem hasWeakPartialDeriv_exp_gaussian_normalization_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f)
    (n : ℕ) (t : ℝ) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => -Real.exp (-f x - (n : ℝ) / 2 * Real.log t -
        (n : ℝ) / 2 * Real.log (4 * Real.pi)) * fderiv ℝ f x (EuclideanSpace.single i 1))
      (fun x => Real.exp (-f x - (n : ℝ) / 2 * Real.log t -
        (n : ℝ) / 2 * Real.log (4 * Real.pi))) Ω := by
  simpa only [sub_eq_add_neg, add_assoc, neg_div, neg_mul] using
    hasWeakPartialDeriv_exp_neg_add_const_of_locallyLipschitzOn hΩ hΩc hf
      (-(n : ℝ) / 2 * Real.log t - (n : ℝ) / 2 * Real.log (4 * Real.pi)) i

end DifferentialGeometry.Analysis.Sobolev.Euclidean

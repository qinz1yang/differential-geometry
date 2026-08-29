import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cml_deriv_zero {n : ℕ}
    {A : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    {A' : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    {V : Fin n → ℝ → E} {V' : Fin n → E} {s : ℝ}
    (hA : HasDerivAt A A' s) (hV : ∀ i, HasDerivAt (V i) (V' i) s)
    (hzero : A s = 0) :
    HasDerivAt (fun r => A r (fun i => V i r))
      (A' (fun i => V i s)) s := by
  classical
  have h := hA.hasFDerivAt.continuousMultilinearMap_apply
    (fun i => (hV i).hasFDerivAt)
  convert h.hasDerivAt using 1
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.apply_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply,
    FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, hzero,
    zero_apply, Finset.sum_const_zero, add_zero]

end DifferentialGeometry.Analysis.Calculus

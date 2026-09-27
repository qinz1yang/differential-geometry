import DifferentialGeometry.Analysis.Calculus.Multilinear

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
  simpa only [hzero, zero_apply, Finset.sum_const_zero, add_zero] using
    hA.continuousMultilinearMap_apply hV

end DifferentialGeometry.Analysis.Calculus

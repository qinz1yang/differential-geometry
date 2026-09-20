import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section
open Manifold
open scoped Manifold

namespace ContinuousLinearEquiv

theorem comp_right_mfderiv
    {V W E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (L : V ≃L[ℝ] W) (u : W → M) (x : V) :
    mfderiv 𝓘(ℝ, V) I (u ∘ L) x =
      (mfderiv 𝓘(ℝ, W) I u (L x)).comp L.toContinuousLinearMap := by
  have hL : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) L x := L.differentiableAt.mdifferentiableAt
  by_cases hu : MDifferentiableAt 𝓘(ℝ, W) I u (L x)
  · rw [mfderiv_comp x hu hL, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
    rfl
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, V) I (u ∘ L) x := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, V) L.symm (L x) :=
        L.symm.differentiableAt.mdifferentiableAt
      have h' : MDifferentiableAt 𝓘(ℝ, V) I (u ∘ L) (L.symm (L x)) :=
        (L.symm_apply_apply x).symm ▸ h
      have heq : ((u ∘ L) ∘ L.symm) = u := by
        funext y
        simp only [Function.comp_apply, L.apply_symm_apply]
      exact hu (heq ▸ h'.comp (L x) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hu]
    rfl

end ContinuousLinearEquiv

end

import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.ODE.Basic

open scoped Manifold

theorem IsMIntegralCurveOn.map
    {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {γ : ℝ → M} {V : (x : M) → TangentSpace I x} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ V s) {f : M → N} {W : (x : N) → TangentSpace J x}
    (hf : ∀ t ∈ s, MDifferentiableAt I J f (γ t))
    (hrelated : ∀ t ∈ s, mfderiv I J f (γ t) (V (γ t)) = W (f (γ t))) :
    IsMIntegralCurveOn (f ∘ γ) W s := by
  intro t ht
  have h := (hf t ht).hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
  have hD : (mfderiv I J f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (W (f (γ t))) := by
    apply ContinuousLinearMap.ext
    intro r
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, map_smul, hrelated t ht]
  exact hD ▸ h

theorem isMIntegralCurveOn_iff_isIntegralCurveOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {V : E → E} {s : Set ℝ} :
    IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ V s ↔ IsIntegralCurveOn γ (fun _ => V) s := by
  constructor
  · intro h t ht
    exact (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp (h t ht))
  · intro h t ht
    exact (h t ht).hasFDerivWithinAt.hasMFDerivWithinAt

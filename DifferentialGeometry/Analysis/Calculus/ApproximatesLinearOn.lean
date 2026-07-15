import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Derivative bounds for quantitative linear approximation

This file records pointwise derivative consequences of
`ApproximatesLinearOn` at interior points of the approximation set.
-/

noncomputable section

/-- A differentiable map which approximates a linear map on a neighborhood has
derivative within the same operator-norm error at the center. -/
theorem ApproximatesLinearOn.fderiv_sub_le
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {A : E →L[𝕜] F} {s : Set E} {c : NNReal} {x : E}
    (hf : ApproximatesLinearOn f A s c) (hs : s ∈ nhds x)
    (hfd : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 f x - A‖ ≤ (c : Real) := by
  have hres : HasFDerivAt (f - (A : E → F))
      (fderiv 𝕜 f x - A) x := by
    simpa only [Pi.sub_apply] using hfd.hasFDerivAt.sub A.hasFDerivAt
  exact hres.le_of_lipschitzOn hs hf.lipschitzOnWith

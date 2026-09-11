import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
noncomputable section
open scoped Manifold
namespace DifferentialGeometry.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}


theorem mfderiv_const_sub_real {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (b : ℝ) :
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => b - f y) x) =
      -(show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) ((fun _ : M => b) - f) x) = _
  erw [mfderiv_sub mdifferentiableAt_const hf,mfderiv_const,zero_sub]
  rfl

end DifferentialGeometry.Manifold

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
namespace DifferentialGeometry.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem fderiv_fderiv_log_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x v w =
      (f x)⁻¹ * fderiv ℝ (fderiv ℝ f) x v w -
        (f x)⁻¹ ^ 2 * fderiv ℝ f x v * fderiv ℝ f x w := by
  have hfd := hf.differentiableAt (by norm_num)
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y => Real.log (f y)) =ᶠ[𝓝 x]
      fun y => (f y)⁻¹ • fderiv ℝ f y := by
    filter_upwards [hf.eventually (by norm_num), hfd.continuousAt.eventually_ne hx] with y hfy hy
    exact fderiv.log (hfy.differentiableAt (by norm_num)) hy
  have hd := ((hasDerivAt_inv hx).comp_hasFDerivAt x hfd.hasFDerivAt).smul hdf.hasFDerivAt
  simp only [Function.comp_def, Pi.smul_def'] at hd
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul, inv_pow]
  ring
end DifferentialGeometry.Analysis

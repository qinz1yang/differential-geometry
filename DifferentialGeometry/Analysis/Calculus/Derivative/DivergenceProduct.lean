import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring


namespace DifferentialGeometry.Analysis.Calculus

open scoped ContDiff

theorem fderiv_mul_fderiv_apply
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {c f : E → 𝕜} {x : E} (hc : DifferentiableAt 𝕜 c x)
    (hf : ContDiffAt 𝕜 2 f x) (u v : E) :
    fderiv 𝕜 (fun y => c y * fderiv 𝕜 f y u) x v =
      c x * iteratedFDeriv 𝕜 2 f x ![v, u] +
        iteratedFDeriv 𝕜 1 c x (fun _ => v) *
          iteratedFDeriv 𝕜 1 f x (fun _ => u) := by
  have hd : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_fun_mul hc (hd.clm_apply (differentiableAt_const u))]
  rw [fderiv_clm_apply hd (differentiableAt_const u)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end DifferentialGeometry.Analysis.Calculus

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Gradient

theorem mvfderiv_signed_affine_coordinate
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (f : M → ℝ) (x : M) (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (σ c : ℝ) (hσ : σ = 1 ∨ σ = -1) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ σ * f y + c) x (σ • v) = mvfderiv I f x v := by
  have hm : MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ σ * f y) x :=
    mdifferentiableAt_const.mul hf
  rw [mvfderiv_fun_add hm mdifferentiableAt_const,
    mvfderiv_fun_mul mdifferentiableAt_const hf, mvfderiv_const, mvfderiv_const]
  simp only [smul_zero, add_zero, smul_apply, map_smul, smul_eq_mul]
  have hs : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [← mul_assoc, hs, one_mul]

end DifferentialGeometry.Geometry.Gradient

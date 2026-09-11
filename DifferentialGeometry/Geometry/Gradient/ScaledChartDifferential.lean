import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Gradient

theorem mvfderiv_scaled_chart_coordinate
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : M ≃ₘ⟮I, J⟯ N) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (c : ℝ) (hc : 0 < c) (x : M) (w : TangentSpace I x) :
    mvfderiv J (fun y ↦ (Real.sqrt c)⁻¹ * f (Φ.symm y)) (Φ x)
      (Real.sqrt c • mfderiv I J Φ x w) = mvfderiv I f x w := by
  let h : N → ℝ := fun y ↦ (Real.sqrt c)⁻¹ * f (Φ.symm y)
  have hh : ContMDiff J 𝓘(ℝ) ∞ h := contMDiff_const.mul (hf.comp Φ.symm.contMDiff)
  have heq : h ∘ Φ = fun y ↦ (Real.sqrt c)⁻¹ * f y := by
    funext y
    simp only [Function.comp_apply, h, Φ.symm_apply_apply]
  have hd := mvfderiv_comp_apply x (hh.mdifferentiable (by decide) (Φ x))
    (Φ.mdifferentiable (by decide) x) w
  rw [heq] at hd
  have hs : (Real.sqrt c)⁻¹ * mvfderiv I f x w =
      mvfderiv J h (Φ x) (mfderiv I J Φ x w) := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const (hf.mdifferentiable (by decide) x),
      mvfderiv_const] at hd
    simpa only [smul_zero, add_zero, smul_apply, smul_eq_mul] using hd
  change mvfderiv J h (Φ x) (Real.sqrt c • mfderiv I J Φ x w) = _
  rw [map_smul, smul_eq_mul, ← hs, ← mul_assoc,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_mul]

end DifferentialGeometry.Geometry.Gradient

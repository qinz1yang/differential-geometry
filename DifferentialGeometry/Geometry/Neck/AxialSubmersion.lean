import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Topology.Manifold.ProductChartSubmersion
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set
open scoped Manifold ContDiff

namespace Poincare.Geometry.Neck

theorem cylindricalChart.contMDiff_and_mvfderiv_affine_axial_ne_zero
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H' M]
    (C : cylindricalChart J (M := M)) (ι : W → M) (hι : ContMDiff I J ∞ ι)
    (hsurj : ∀ w, Function.Surjective (mfderiv I J ι w))
    (htarget : ∀ w, ι w ∈ C.target) (τ c : ℝ) (hτ : τ ≠ 0) :
    let u := fun w ↦ τ * C.axial (ι w) + c
    ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  let q : W → ℝ := fun w ↦
    (C.chart.symm ⟨ι w, htarget w⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2
  obtain ⟨hq, hqsurj⟩ := Poincare.Topology.Manifold.contMDiff_and_surjective_mfderiv_snd_of_product_chart
    C.domain C.target C.chart ι hι hsurj htarget
  change ContMDiff I 𝓘(ℝ) ∞ q at hq
  have heq : (fun w ↦ τ * C.axial (ι w) + c) =
      (fun w ↦ (τ * (Real.sqrt C.scale)⁻¹) * q w + c) := by
    funext w
    unfold cylindricalChart.axial
    rw [Subtype.val_injective.extend_apply _ _ (⟨ι w, htarget w⟩ : C.target)]
    change τ * ((Real.sqrt C.scale)⁻¹ * q w) + c = _
    rw [mul_assoc]
  rw [heq]
  refine ⟨(contMDiff_const.mul hq).add contMDiff_const, ?_⟩
  intro w hzero
  obtain ⟨z, hz⟩ := hqsurj w 1
  have hz' : mvfderiv I q w z = 1 := hz
  have hq' := hq.mdifferentiable (by decide) w
  have hmul : MDifferentiableAt I 𝓘(ℝ) (fun w ↦ (τ * (Real.sqrt C.scale)⁻¹) * q w) w :=
    mdifferentiableAt_const.mul hq'
  have hval := DFunLike.congr_fun hzero z
  rw [mvfderiv_fun_add hmul mdifferentiableAt_const,
    mvfderiv_fun_mul mdifferentiableAt_const hq', mvfderiv_const, mvfderiv_const] at hval
  simp only [smul_zero, add_zero, smul_apply, smul_eq_mul, hz', mul_one, zero_apply] at hval
  exact (mul_ne_zero hτ (inv_ne_zero (Real.sqrt_pos.mpr C.scale_pos).ne')) hval

end Poincare.Geometry.Neck

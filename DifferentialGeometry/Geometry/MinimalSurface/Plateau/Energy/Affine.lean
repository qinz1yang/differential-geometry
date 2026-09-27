import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

section

noncomputable section

open Manifold MeasureTheory Set
open scoped Manifold Pointwise ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem diskMapPartial_comp_affine (U : ℂ → M) (b z v : ℂ) (r : ℝ) :
    diskMapPartial (E := E) (fun w => U (b + r • w)) z v =
      r • diskMapPartial (E := E) U (b + r • z) v := by
  by_cases hr : r = 0
  · subst r
    have heq : (fun w : ℂ => U (b + (0 : ℝ) • w)) = fun _ => U b := by
      funext w
      rw [zero_smul, add_zero]
    change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => U (b + (0 : ℝ) • w)) z v : E) =
      (0 : ℝ) • diskMapPartial (E := E) U (b + (0 : ℝ) • z) v
    rw [heq, mfderiv_const]
    exact (zero_smul ℝ (diskMapPartial (E := E) U (b + (0 : ℝ) • z) v)).symm
  have ha : HasFDerivAt (fun w : ℂ => b + r • w)
      (r • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).const_smul r).const_add b
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (b + r • z)
  · unfold diskMapPartial
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ fun w => b + r • w) z v = _
    rw [mfderiv_comp z hU ha.differentiableAt.mdifferentiableAt,
      mfderiv_eq_fderiv, ha.fderiv]
    exact (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (b + r • z)).map_smul r v
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (fun w => U (b + r • w)) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
          (fun w : ℂ => r⁻¹ • (w - b)) (b + r • z) :=
        ((differentiableAt_id.sub_const b).const_smul r⁻¹).mdifferentiableAt
      have hz : r⁻¹ • (b + r • z - b) = z := by
        rw [add_sub_cancel_left, inv_smul_smul₀ hr]
      have h' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
          (fun w => U (b + r • w)) (r⁻¹ • (b + r • z - b)) := hz.symm ▸ h
      have heq : ((fun w => U (b + r • w)) ∘ fun w => r⁻¹ • (w - b)) = U := by
        funext w
        change U (b + r • (r⁻¹ • (w - b))) = U w
        rw [smul_inv_smul₀ hr, add_comm b, sub_add_cancel]
      exact hU (heq ▸ h'.comp (b + r • z) hi)
    unfold diskMapPartial
    rw [mfderiv_zero_of_not_mdifferentiableAt hc,
      mfderiv_zero_of_not_mdifferentiableAt hU]
    change (0 : E) = r • (0 : E)
    exact (smul_zero r).symm

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapEnergyDensity_comp_affine
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (b z : ℂ) (r : ℝ) :
    diskMapEnergyDensity g (fun w => U (b + r • w)) z =
      r ^ 2 * diskMapEnergyDensity g U (b + r • z) := by
  simp only [diskMapEnergyDensity, diskMapPartial_comp_affine, map_smul, smul_apply,
    smul_eq_mul]
  ring

theorem integral_diskMapEnergyDensity_comp_affine
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (b : ℂ) {r : ℝ}
    (hr : r ≠ 0) (s : Set ℂ) :
    (∫ z in s, diskMapEnergyDensity g (fun w => U (b + r • w)) z) =
      ∫ z in (fun w => b + r • w) '' s, diskMapEnergyDensity g U z := by
  simp_rw [diskMapEnergyDensity_comp_affine]
  rw [integral_const_mul,
    Measure.setIntegral_comp_smul volume (fun z => diskMapEnergyDensity g U (b + z)) s hr]
  simp only [Complex.finrank_real_complex, smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]
  simpa only [← image_smul, image_image] using
    ((measurePreserving_add_left (volume : Measure ℂ) b).setIntegral_image_emb
      (MeasurableEquiv.addLeft b).measurableEmbedding
      (diskMapEnergyDensity g U) (r • s)).symm

theorem integral_diskMapEnergyDensity_comp_affine_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (b : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      diskMapEnergyDensity g (fun w => U (b + r • w)) z) =
      ∫ z in Metric.ball b r, diskMapEnergyDensity g U z := by
  rw [integral_diskMapEnergyDensity_comp_affine g U b hr.ne']
  have himage : (fun w : ℂ => b + r • w) '' Metric.ball 0 1 = Metric.ball b r := by
    simpa only [← image_vadd, ← image_smul, image_image, vadd_eq_add] using affinity_unitBall hr b
  rw [himage]

theorem integral_diskMapEnergyDensity_comp_affine_closedBall
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (b : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (fun w => U (b + r • w)) z) =
      ∫ z in Metric.closedBall b r, diskMapEnergyDensity g U z := by
  rw [integral_diskMapEnergyDensity_comp_affine g U b hr.ne']
  have himage : (fun w : ℂ => b + r • w) '' Metric.closedBall 0 1 =
      Metric.closedBall b r := by
    simpa only [← image_vadd, ← image_smul, image_image, vadd_eq_add] using
      affinity_unitClosedBall hr.le b
  rw [himage]

end DifferentialGeometry.Geometry

end

end

import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Set MeasureTheory

namespace LinearIsometryEquiv

theorem norm_fderiv_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → G) (x : E) :
    ‖fderiv ℝ (f ∘ e) x‖ = ‖fderiv ℝ f (e x)‖ := by
  have hd : fderiv ℝ (f ∘ e) x = (fderiv ℝ f (e x)).comp (e : E →L[ℝ] F) :=
    e.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := x)
  rw [hd]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e

theorem integral_norm_fderiv_sq_comp_closedBall
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → G) (r : ℝ) :
    (∫ x in Metric.closedBall (0 : E) r, ‖fderiv ℝ (f ∘ e) x‖ ^ 2) =
      ∫ y in Metric.closedBall (0 : F) r, ‖fderiv ℝ f y‖ ^ 2 := by
  simp_rw [e.norm_fderiv_comp]
  have h := e.measurePreserving.setIntegral_preimage_emb e.toMeasurableEquiv.measurableEmbedding
    (fun y => ‖fderiv ℝ f y‖ ^ 2) (Metric.closedBall (0 : F) r)
  have hset : e ⁻¹' Metric.closedBall (0 : F) r = Metric.closedBall (0 : E) r := by
    ext x
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, e.norm_map]
  rw [hset] at h
  exact h

end LinearIsometryEquiv

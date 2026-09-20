import DifferentialGeometry.Analysis.Integration.Measure.ModelChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Operator.ModelChange
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [I.Boundaryless] in
private theorem normGradSqFun_model_change
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (f : M → ℝ) (x : M) :
    normGradSqFun (g.transContinuousLinearEquiv e) f x = normGradSqFun g f x := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · exact normGradSqFun_transContinuousLinearEquiv g e f x hf
  · have hf' : ¬ MDifferentiableAt (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) f x := by
      intro h
      let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
      have hcomp := h.comp x (Φ.contMDiff.mdifferentiableAt (by simp))
      exact hf hcomp
    rw [normGradSqFun_eq_zero_iff.mpr (mfderiv_zero_of_not_mdifferentiableAt hf'),
      normGradSqFun_eq_zero_iff.mpr (mfderiv_zero_of_not_mdifferentiableAt hf)]

theorem isHamiltonNormalizedPotential_transContinuousLinearEquiv_iff
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (f : M → ℝ) :
    IsHamiltonNormalizedPotential (g.transContinuousLinearEquiv e) f ↔
      IsHamiltonNormalizedPotential g f := by
  change (∀ x : M, metricScalarAt (g.transContinuousLinearEquiv e) x +
    normGradSqFun (g.transContinuousLinearEquiv e) f x = f x) ↔
    ∀ x : M, metricScalarAt g x + normGradSqFun g f x = f x
  simp only [metricScalarAt_transContinuousLinearEquiv, normGradSqFun_model_change]

variable [SigmaCompactSpace M]

theorem normalizedShrinkerMass_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (f : M → ℝ) :
    normalizedShrinkerMass (g.transContinuousLinearEquiv e) f =
      normalizedShrinkerMass g f := by
  unfold normalizedShrinkerMass
  rw [riemannianVolumeMeasure_transContinuousLinearEquiv, e.toLinearEquiv.finrank_eq]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

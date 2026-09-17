import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Naturality
import DifferentialGeometry.Analysis.Integration.Measure.ModelChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem redDensity_transContinuousLinearEquiv
    (S : SolutionOn (I := I) (M := M) D) (e : E ≃L[ℝ] F)
    (T : ℝ) (x y : M) (tau : ℝ) :
    redDensity (S.pullback (ContinuousLinearEquiv.toTransContinuousLinearEquiv
      (n := ∞) I M e).symm) T x y tau = redDensity S T x y tau := by
  have hcost := lCost_pullback_cross S
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm T x y tau
  change lCost (S.pullback (ContinuousLinearEquiv.toTransContinuousLinearEquiv
    (n := ∞) I M e).symm) T x y tau = lCost S T x y tau at hcost
  unfold redDensity redLength
  rw [hcost, ← e.toLinearEquiv.finrank_eq]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem redVolume_transContinuousLinearEquiv [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (e : E ≃L[ℝ] F)
    (T : ℝ) (x : M) (tau : ℝ) :
    redVolume (S.pullback (ContinuousLinearEquiv.toTransContinuousLinearEquiv
      (n := ∞) I M e).symm) T x tau = redVolume S T x tau := by
  unfold redVolume
  simp_rw [redDensity_transContinuousLinearEquiv]
  change (∫⁻ y, ENNReal.ofReal (redDensity S T x y tau)
    ∂riemannianVolumeMeasure (I := I.transContinuousLinearEquiv e)
      (M := M) ((S.base.metric (T - tau)).transContinuousLinearEquiv e)) = _
  rw [riemannianVolumeMeasure_transContinuousLinearEquiv]

end DifferentialGeometry.PDE.RicciFlow.Perelman

import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Family.Stationary
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection (LeviCivita)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
def SolutionOn.const (g : SmoothRiemannianMetric I M) (D : RealTimeInterval) :
    SolutionOn (I := I) (M := M) D where
  base.metric := fun _ => g

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem SolutionOn.const_metric (g : SmoothRiemannianMetric I M)
    (D : RealTimeInterval) (t : ℝ) :
    (SolutionOn.const g D).base.metric t = g := rfl

theorem isSolutionOn_const_of_ricciTensor_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hric : ∀ x (v w : TangentSpace I x), ricciTensor g x v w = 0)
    (D : RealTimeInterval) :
    IsSolutionOn (SolutionOn.const g D) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply isSolutionOn_of_reg (fun _ => g)
  · exact metricFamilySmoothOn_stationary g D
  · intro t _ x v w
    rw [hric, mul_zero]
    exact hasDerivAt_const t (g.inner x v w)
  · exact ((metricScalar_smooth g).continuous.comp continuous_snd).continuousOn
  · intro t _ x
    exact differentiableWithinAt_const (c := metricScalarAt g x)
  · have hc := (metricRicci g).contMDiff.continuous.comp
      (continuous_snd : Continuous (Prod.snd : {t : ℝ // t ∈ D.carrier} × M → M))
    simpa only [tensor0SFamilyContinuousOnSet, Function.comp_def, metricRicci_apply] using hc
  · have hc := (metricRm04 g).contMDiff.continuous.comp
      (continuous_snd : Continuous (Prod.snd : {t : ℝ // t ∈ D.carrier} × M → M))
    simpa only [tensor0SFamilyContinuousOnSet, Function.comp_def, metricRm04_apply] using hc

theorem isSolutionOn_const_euclidean_real (D : RealTimeInterval) :
    IsSolutionOn (SolutionOn.const (euclideanMetric (E := ℝ)) D) := by
  apply isSolutionOn_const_of_ricciTensor_eq_zero
  intro x v w
  rw [ricciTensor_apply]
  have hz : ricciEndo (euclideanMetric (E := ℝ)) x v w = 0 := by
    apply LinearMap.ext
    intro z
    exact riemannOp_eq_zero_of_finrank_le_one (LeviCivita (euclideanMetric (E := ℝ)))
      (by simp) x z v w
  rw [hz, map_zero]

end DifferentialGeometry.PDE.RicciFlow
